"""Scope-aware Hypothesis strategies over the tier-1 surface AST.

The single highest-leverage design feature (prong2-design §3): an environment
of bound locals and previously-defined methods threads through top-down
generation, so generated programs reference names that resolve and method
dispatch actually fires — instead of every program dying at line 1 with
NameError. Deterministic errors are still legal oracle cases, so expressions
are not type-checked; loops are bounded by construction.
"""

from __future__ import annotations

from dataclasses import dataclass, replace

from hypothesis import strategies as st

from . import ast as A

LOCAL_POOL = ("a", "b", "c", "d")
LOOP_POOL = ("i", "j")
FOR_POOL = ("fi", "fj")  # `for` loop vars — leak to the enclosing scope
REDO_POOL = ("rg0", "rg1")  # monotonic guard counters bounding `redo`
PARAM_POOL = ("x", "y")
BLOCK_PARAM_POOL = ("bx", "by")  # block/lambda params; disjoint from everything else
METHOD_POOL = ("m0", "m1", "m2", "m3")
CLASS_POOL = ("C0", "C1", "C2")
MODULE_POOL = ("M0", "M1")
IMETHOD_POOL = ("im0", "im1")
MMETHOD_POOL = ("mm0", "mm1")  # module instance methods; disjoint from IMETHOD_POOL
SMETHOD_POOL = ("sm0", "sm1")  # class/self methods
ESM_POOL = ("esm0", "esm1")  # class methods defined via `class << self`
MM_GHOST_POOL = ("ghost0", "ghost1")  # names never defined → route to method_missing
DMETHOD_POOL = ("dm0", "dm1")  # define_method'd instance methods
DSM_POOL = ("ds0", "ds1")  # define_singleton_method'd class methods
ROPEN_POOL = ("rm0", "rm1")  # methods added by reopening a class
ALIAS_POOL = ("al0", "al1")  # fresh names introduced by alias/alias_method
UNDEF_POOL = ("ud0",)  # throwaway method defined only to be `undef`'d
CONST_POOL = ("K0", "K1")  # constants defined in a class/module body
EXT_CONST_POOL = ("E0", "E1")  # constants assigned externally via `Cls::E0 = …`
RETRY_POOL = ("rt0", "rt1")  # monotonic guard counters bounding `retry`
# StandardError subclasses, mutually non-ancestor → a `rescue X` catches iff X is the
# raised class (or a bare `rescue`); safe for typed/non-matching clause construction
EXC_CLASSES = ("RuntimeError", "TypeError", "ArgumentError", "ZeroDivisionError")
IVAR_POOL = ("@x", "@y")
INSTANCE_POOL = ("o", "p", "q")  # locals that hold instances; disjoint from LOCAL/LOOP/PARAM
PROC_POOL = ("f", "g", "h")  # locals that hold procs/lambdas; disjoint too
INDEXABLE_POOL = ("ix0", "ix1", "ix2")  # locals that hold arrays/hashes; disjoint too
STR_POOL = ("hi", "ok", "zap", "a b", "")
SYM_POOL = ("k", "v", "s")
# unary methods every object answers → safe as `&:sym` block-pass and deterministic
SAFE_UNARY_SYMS = ("to_s", "inspect", "itself", "class", "freeze")

MAX_EXPR_DEPTH = 3

# Recursion-capable instance-method names (bodies that may self-send other instance
# methods), in a fixed global order. A body may self-call only STRICTLY-LOWER-ranked
# names in this order; module/attr/method_missing methods are sinks (never call
# im/dm/rm), so they carry no rank and are always callable. Because virtual dispatch
# preserves the *name*, "every body calls only lower names" makes any call chain
# strictly descend → the per-object call graph is acyclic for *any* receiver class,
# even across inheritance/override/shadowing (which is how mutual recursion would
# otherwise arise: a low-rank inherited method calling a name that dispatches to a
# high-rank subclass override that calls back up).
_CALL_ORDER = ("im0", "im1", "dm0", "dm1", "rm0", "rm1")
_CALL_RANK = {n: i for i, n in enumerate(_CALL_ORDER)}


def _callable_ok(callee: str, current: str) -> bool:
    """May a method named `current` self-call a method named `callee` without risking
    an unbounded virtual-dispatch cycle?"""
    kr = _CALL_RANK.get(callee)
    if kr is None:
        return True  # callee is a sink (module/attr/method_missing) — cannot cycle back
    cr = _CALL_RANK.get(current)
    if cr is None:
        return True  # a sink body doesn't reach here in practice
    return kr < cr

# disjoint pools for varied top-level-method params (see Sig / _method_param_spec)
OPT_POOL = ("o1", "o2")  # optional positional param names
REST_POOL = ("r1",)  # *rest param name
KEY_POOL = ("k1", "k2")  # keyword param names
KWREST_POOL = ("o9",)  # **kwrest param name
KW_CALL_POOL = ("k1", "k2", "k3")  # arbitrary keyword names for **kwrest / ... call sites
DESTR_POOL = ("da", "db")  # destructuring block sub-param names


@dataclass(frozen=True)
class Sig:
    """A callable's parameter shape, used to generate a *compatible* call. Only
    top-level methods carry a non-trivial Sig (registered in `Env.sigs`); instance/
    class/module methods stay plain-required (`reqpos` only, no Sig → plain call).
    Required keywords (`req_keys`) are safe because every call site consults
    `Env.sig_for` — the same enriched generator runs everywhere `env` reaches."""

    reqpos: int = 0
    nopt: int = 0  # optional positional params (each rendered with a default)
    rest: bool = False  # has `*rest`
    req_keys: tuple = ()  # required keyword names (`k:`)
    opt_keys: tuple = ()  # optional keyword names (`k: default`)
    kwrest: bool = False  # has `**kwrest`
    fwd: bool = False  # `...` — accepts and forwards arbitrary args (to a **-sink)


@dataclass(frozen=True)
class ClassInfo:
    name: str
    ctor_arity: int  # arity of `.new` (own or inherited `initialize`)
    imethods: tuple[tuple[str, int], ...]  # effective instance methods: own + inherited + mixed
    smethods: tuple[tuple[str, int], ...] = ()  # class/self methods
    attr_writers: tuple[str, ...] = ()  # ivar base names with a writer (attr_accessor/writer)
    consts: tuple[str, ...] = ()  # constants readable as `Name::const` (cpath)
    has_mm: bool = False  # defines method_missing → a missing send routes there


@dataclass(frozen=True)
class ModuleInfo:
    name: str
    methods: tuple[tuple[str, int], ...]  # instance methods mixed in on include/prepend


@dataclass(frozen=True)
class Env:
    locals: tuple[str, ...] = ()
    methods: tuple[tuple[str, int], ...] = ()  # (name, arity)
    # names that must not be (re)assigned — loop counters, whose progress
    # guarantees termination; they stay readable
    frozen: tuple[str, ...] = ()
    # defined classes (strict DAG: a class's methods see only *prior* classes,
    # and each ctor is pure ivar-assignment, so `.new` cannot recurse)
    classes: tuple[ClassInfo, ...] = ()
    # defined modules (mixed into classes via include/prepend)
    modules: tuple[ModuleInfo, ...] = ()
    # arity to forward when the current override body may call `super`, else None
    can_super: "int | None" = None
    # locals known to hold an instance: (local_name, class_name). Kept out of
    # `locals` on purpose — they are only ever used as method-call receivers.
    instances: tuple[tuple[str, str], ...] = ()
    # instance vars readable in the current method body (@x, @y)
    ivars: tuple[str, ...] = ()
    # locals holding an array/hash: (local_name, "array" | "hash"). Also in
    # `locals`; tracked here so index-assignment targets a real container.
    indexables: tuple[tuple[str, str], ...] = ()
    # locals known to hold a proc/lambda: (local_name, arity, strict). Kept out
    # of `locals` — only ever used as `.call` receivers or `&`-passed. `strict`
    # marks lambdas (arity-checked); only non-strict procs are `&`-passed as
    # blocks, so a yield-arity mismatch can never raise ArgumentError.
    procs: tuple[tuple[str, int, bool], ...] = ()
    # methods that `yield` (kept OUT of `methods` so a plain call never targets
    # them without a block → no LocalJumpError): (name, arg_arity, yield_arity)
    yielders: tuple[tuple[str, int, int], ...] = ()
    # yield arity of the enclosing method body, or None if it may not `yield`
    can_yield: "int | None" = None
    in_block: bool = False  # inside a block body → `next`/`break` are legal
    in_method: bool = False  # inside a method body → `return` is legal
    # constant assignment (`X =`, `A::X =`) is a syntax error inside any *block*
    # or *method* ("dynamic constant assignment"); True only at a static position
    # (top-level / class body / `if`/`while`/`for`/`begin`, which are not closures)
    const_asgn_ok: bool = True
    # richer signatures for names in `methods` (top-level methods only); a name
    # absent here is a plain-required method. Threaded everywhere `env` reaches so
    # every call site (incl. method bodies) generates a compatible call.
    sigs: tuple[tuple[str, Sig], ...] = ()

    def sig_for(self, name: str) -> "Sig | None":
        return next((s for (n, s) in self.sigs if n == name), None)

    def with_sig(self, name: str, sig: Sig) -> "Env":
        return replace(self, sigs=self.sigs + ((name, sig),))

    def with_local(self, name: str) -> "Env":
        return self if name in self.locals else replace(self, locals=self.locals + (name,))

    def with_frozen(self, name: str) -> "Env":
        return replace(self.with_local(name), frozen=self.frozen + (name,))

    def with_method(self, name: str, arity: int) -> "Env":
        return replace(self, methods=self.methods + ((name, arity),))

    def with_class(self, ci: ClassInfo) -> "Env":
        return replace(self, classes=self.classes + (ci,))

    def with_module(self, mi: ModuleInfo) -> "Env":
        return replace(self, modules=self.modules + (mi,))

    def update_class(self, name: str, new_ci: ClassInfo) -> "Env":
        return replace(self, classes=tuple(new_ci if c.name == name else c for c in self.classes))

    def with_indexable(self, name: str, kind: str) -> "Env":
        # readable (in locals) but frozen (never reassigned to a scalar), so the
        # index-assign target always still holds a container
        e = self.with_frozen(name)
        ix = tuple((n, k) for (n, k) in e.indexables if n != name) + ((name, kind),)
        return replace(e, indexables=ix)

    @property
    def instances_with_writers(self) -> tuple[tuple[str, str, tuple], ...]:
        """(inst_name, class_name, writer_names) for instances whose class has attr writers."""
        out = []
        for n, c in self.instances:
            ci = self.class_info(c)
            if ci and ci.attr_writers:
                out.append((n, c, ci.attr_writers))
        return tuple(out)

    def with_instance(self, name: str, class_name: str) -> "Env":
        insts = tuple((n, c) for (n, c) in self.instances if n != name) + ((name, class_name),)
        return replace(self, instances=insts)

    def with_proc(self, name: str, arity: int, strict: bool) -> "Env":
        ps = tuple(p for p in self.procs if p[0] != name) + ((name, arity, strict),)
        return replace(self, procs=ps)

    def with_yielder(self, name: str, arg_arity: int, yield_arity: int) -> "Env":
        return replace(self, yielders=self.yielders + ((name, arg_arity, yield_arity),))

    def class_info(self, name: str) -> "ClassInfo | None":
        return next((ci for ci in self.classes if ci.name == name), None)

    @property
    def assignable(self) -> tuple[str, ...]:
        return tuple(n for n in self.locals if n not in self.frozen)

    @property
    def callable_instances(self) -> tuple[tuple[str, str], ...]:
        """Instances whose class has at least one callable instance method."""
        return tuple(
            (n, c)
            for (n, c) in self.instances
            if (self.class_info(c) or ClassInfo(c, 0, ())).imethods
        )

    @property
    def classes_with_smethods(self) -> tuple[ClassInfo, ...]:
        return tuple(ci for ci in self.classes if ci.smethods)

    @property
    def classes_with_consts(self) -> tuple[ClassInfo, ...]:
        return tuple(ci for ci in self.classes if ci.consts)

    @property
    def mm_instances(self) -> tuple[tuple[str, str], ...]:
        """Instances whose class defines method_missing (a missing send routes there)."""
        return tuple((n, c) for (n, c) in self.instances if (self.class_info(c) or ClassInfo(c, 0, ())).has_mm)


@st.composite
def _literal(draw) -> A.Node:
    kind = draw(st.sampled_from(["int", "int", "str", "sym", "bool", "nil"]))
    if kind == "int":
        return A.IntLit(draw(st.integers(-20, 100)))
    if kind == "str":
        return A.StrLit(draw(st.sampled_from(STR_POOL)))
    if kind == "sym":
        return A.SymLit(draw(st.sampled_from(SYM_POOL)))
    if kind == "bool":
        return A.BoolLit(draw(st.booleans()))
    return A.NilLit()


@st.composite
def _gen_call(draw, env: "Env", sig: Sig, depth: int):
    """Positional args + kwargs compatible with `sig` (never raises ArgumentError).
    Optional positionals are filled as a *prefix* (Ruby has no positional skipping);
    required keywords are always supplied; `**kwrest`/`...` may take extra names."""
    d = max(depth - 1, 0)
    if sig.fwd:
        npos = draw(st.integers(0, 3))
        req_keys, opt_keys, kwrest = (), (), True
    else:
        npos = sig.reqpos + draw(st.integers(0, sig.nopt))
        if sig.rest:
            npos += draw(st.integers(0, 2))
        req_keys, opt_keys, kwrest = sig.req_keys, sig.opt_keys, sig.kwrest
    args = tuple(draw(_expr(env, d)) for _ in range(npos))
    keys = list(req_keys)
    for k in opt_keys:
        if draw(st.booleans()):
            keys.append(k)
    if kwrest:
        declared = set(req_keys) | set(opt_keys)
        for kk in KW_CALL_POOL:
            if kk not in keys and kk not in declared and draw(st.booleans()):
                keys.append(kk)
    kwargs = tuple((k, draw(_expr(env, d))) for k in keys)
    return args, kwargs


@st.composite
def _method_param_spec(draw, depth: int):
    """A varied top-level-method param list → (params, Sig, bound_names). Order is
    Ruby-legal: required, optional (with defaults), `*rest`, keywords, `**kwrest`."""
    params: list = []
    bound: list[str] = []
    reqpos = draw(st.integers(0, len(PARAM_POOL)))
    for nm in PARAM_POOL[:reqpos]:
        params.append(nm)
        bound.append(nm)
    nopt = draw(st.integers(0, len(OPT_POOL)))
    for nm in OPT_POOL[:nopt]:
        # default reads an earlier param (exercises lazy left-to-right eval in the
        # callee frame — the popt obligation) or a literal
        if bound and draw(st.booleans()):
            default = A.LocalRead(draw(st.sampled_from(tuple(bound))))
        else:
            default = draw(_literal())
        params.append(A.POpt(nm, default))
        bound.append(nm)
    rest = draw(st.booleans())
    if rest:
        params.append(A.PRest(REST_POOL[0]))
        bound.append(REST_POOL[0])
    req_keys: list[str] = []
    opt_keys: list[str] = []
    for nm in KEY_POOL[: draw(st.integers(0, len(KEY_POOL)))]:
        if draw(st.booleans()):
            params.append(A.PKey(nm, None))
            req_keys.append(nm)
        else:
            params.append(A.PKey(nm, draw(_literal())))
            opt_keys.append(nm)
        bound.append(nm)
    kwrest = draw(st.booleans())
    if kwrest:
        params.append(A.PKwRest(KWREST_POOL[0]))
        bound.append(KWREST_POOL[0])
    sig = Sig(reqpos, nopt, rest, tuple(req_keys), tuple(opt_keys), kwrest)
    return tuple(params), sig, tuple(bound)


@st.composite
def _expr(draw, env: Env, depth: int, no_range_head: bool = False) -> A.Node:
    # `no_range_head` forbids a range at *this* level only (children recurse
    # unrestricted). A range literal that is the direct condition of `if`/the
    # direct operand of `!`/a ternary predicate is parsed by Ruby as a *flip-flop*,
    # not a range (verified via Prism); `&&`/`||`/`==`/args/assignment are safe.
    kinds = ["lit", "lit"]
    if env.locals:
        kinds += ["local", "local", "local"]
    if env.ivars:
        kinds += ["ivar", "ivar"]
    if env.methods:
        kinds += ["call", "call"]
    if env.procs:
        kinds += ["proccall", "proccall"]
    if env.can_yield is not None:
        kinds += ["yield", "blockgiven"]
    if env.can_super is not None:
        kinds += ["super"] * 5
    callable_instances = env.callable_instances
    classes_with_smethods = env.classes_with_smethods
    classes_with_consts = env.classes_with_consts
    # `new` in *expression* position yields a value that may flow into string
    # interpolation. The desugar lowers `"#{e}"` to `Kernel#String(e)`, which calls
    # `to_str` (→ `method_missing`) whereas real interpolation (`rb_obj_as_string`)
    # calls only `to_s` — so `String(o) != "#{o}"` for a method_missing object (a real
    # desugar bug, see implementation-notes N22). Keep method_missing classes out of
    # value-position `new`; they are still instantiated via the `new_inst` *statement*
    # (bound to a receiver-only instance var, never interpolated) for ghost-call coverage.
    new_classes = tuple(ci for ci in env.classes if not ci.has_mm)
    if depth > 0:
        kinds += ["binop", "binop", "and", "or", "not", "interp", "array", "index", "hash"]
        if not no_range_head:
            kinds += ["range"]
        if new_classes:
            kinds += ["new"]
        if callable_instances:
            kinds += ["mcall", "mcall", "send"]
        if classes_with_smethods:
            kinds += ["smcall"]
        if classes_with_consts:
            kinds += ["cpath"]
        if env.mm_instances:
            kinds += ["mm_call", "mm_call", "mm_call"]
        if env.instances:
            kinds += ["respondto", "ivarget", "ivarset"]
    kind = draw(st.sampled_from(kinds))

    sub = lambda: draw(_expr(env, depth - 1))  # noqa: E731

    if kind == "lit":
        return draw(_literal())
    if kind == "proccall":
        name, arity, _strict = draw(st.sampled_from(env.procs))
        return A.ProcCall(A.LocalRead(name), tuple(sub() for _ in range(arity)))
    if kind == "yield":
        return A.Yield(tuple(sub() for _ in range(env.can_yield)))
    if kind == "blockgiven":
        return A.BlockGiven()
    if kind == "super":
        # bare `super` (zsuper — forwards the method's args) or `super(args)`
        if draw(st.booleans()):
            return A.Super(None)
        return A.Super(tuple(sub() for _ in range(env.can_super)))
    if kind == "cpath":
        ci = draw(st.sampled_from(classes_with_consts))
        return A.ConstPath(ci.name, draw(st.sampled_from(ci.consts)))
    if kind == "mm_call":
        inst_name, _cls = draw(st.sampled_from(env.mm_instances))
        # a name never defined on the class → dispatch falls through to method_missing
        ghost = draw(st.sampled_from(MM_GHOST_POOL))
        return A.MethodCall(
            A.LocalRead(inst_name), ghost, tuple(sub() for _ in range(draw(st.integers(0, 2))))
        )
    if kind == "smcall":
        ci = draw(st.sampled_from(classes_with_smethods))
        sname, arity = draw(st.sampled_from(ci.smethods))
        return A.MethodCall(A.ConstRead(ci.name), sname, tuple(sub() for _ in range(arity)))
    if kind == "send":
        inst_name, class_name = draw(st.sampled_from(callable_instances))
        mname, arity = draw(st.sampled_from(env.class_info(class_name).imethods))
        return A.SendCall(
            A.LocalRead(inst_name), mname, tuple(sub() for _ in range(arity)), draw(st.booleans())
        )
    if kind == "respondto":
        inst_name, class_name = draw(st.sampled_from(env.instances))
        ci = env.class_info(class_name)
        # a real method name (→ true) or an arbitrary one (→ false)
        pool = tuple(m for m, _ in ci.imethods) + SYM_POOL if ci and ci.imethods else SYM_POOL
        return A.RespondTo(A.LocalRead(inst_name), draw(st.sampled_from(pool)))
    if kind == "ivarget":
        inst_name, _ = draw(st.sampled_from(env.instances))
        return A.IvarGetCall(A.LocalRead(inst_name), draw(st.sampled_from(IVAR_POOL)))
    if kind == "ivarset":
        inst_name, _ = draw(st.sampled_from(env.instances))
        return A.IvarSetCall(A.LocalRead(inst_name), draw(st.sampled_from(IVAR_POOL)), sub())
    if kind == "range":
        lo = draw(st.integers(0, 3))
        return A.RangeLit(A.IntLit(lo), A.IntLit(lo + draw(st.integers(0, 3))), draw(st.booleans()))
    if kind == "local":
        return A.LocalRead(draw(st.sampled_from(env.locals)))
    if kind == "ivar":
        return A.IvarRead(draw(st.sampled_from(env.ivars)))
    if kind == "call":
        name, arity = draw(st.sampled_from(env.methods))
        sig = env.sig_for(name)
        if sig is not None:
            args, kwargs = draw(_gen_call(env, sig, depth))
            return A.Call(name, args, kwargs)
        return A.Call(name, tuple(draw(_expr(env, depth - 1)) for _ in range(arity)))
    if kind == "new":
        ci = draw(st.sampled_from(new_classes))
        return A.New(ci.name, tuple(draw(_expr(env, depth - 1)) for _ in range(ci.ctor_arity)))
    if kind == "mcall":
        inst_name, class_name = draw(st.sampled_from(callable_instances))
        ci = env.class_info(class_name)
        mname, arity = draw(st.sampled_from(ci.imethods))
        return A.MethodCall(
            A.LocalRead(inst_name), mname, tuple(draw(_expr(env, depth - 1)) for _ in range(arity))
        )
    if kind == "binop":
        op = draw(st.sampled_from(["+", "+", "-", "*", "%", "==", "<", ">", "<=", ">="]))
        return A.BinOp(op, sub(), sub())
    if kind == "and":
        # conditional context propagates through &&/||: a range under a condition's
        # &&/|| is still a flip-flop, so forward `no_range_head` to the operands
        return A.And(
            draw(_expr(env, depth - 1, no_range_head)), draw(_expr(env, depth - 1, no_range_head))
        )
    if kind == "or":
        return A.Or(
            draw(_expr(env, depth - 1, no_range_head)), draw(_expr(env, depth - 1, no_range_head))
        )
    if kind == "not":
        # `!range` is a flip-flop regardless of surrounding context
        return A.Not(draw(_expr(env, depth - 1, no_range_head=True)))
    if kind == "interp":
        n = draw(st.integers(1, 2))
        parts: list = []
        for _ in range(n):
            parts.append(draw(st.sampled_from(["v=", "<", " ", ""])))
            parts.append(sub())
        return A.StrInterp(tuple(parts))
    if kind == "array":
        return A.ArrayLit(tuple(sub() for _ in range(draw(st.integers(0, 3)))))
    if kind == "index":
        items = tuple(sub() for _ in range(draw(st.integers(1, 3))))
        return A.Index(A.ArrayLit(items), A.IntLit(draw(st.integers(-1, 3))))
    if kind == "hash":
        n = draw(st.integers(1, 2))
        pairs = tuple((A.SymLit(SYM_POOL[k]), sub()) for k in range(n))
        return A.HashLit(pairs)
    raise AssertionError(kind)


@st.composite
def _lambda(draw, env: Env, depth: int) -> A.Lambda:
    kind = draw(st.sampled_from(["->", "proc", "lambda"]))
    arity = draw(st.integers(0, len(BLOCK_PARAM_POOL)))
    params = BLOCK_PARAM_POOL[:arity]
    # A lambda/proc body is a plain closure over the current locals + its params.
    # `return`/`next`/`break` are NOT emitted here (their proc-vs-lambda semantics
    # are subtle — left to tier 3); the body just computes a value.
    body_env = replace(
        env,
        locals=env.locals + params,
        can_yield=None,
        can_super=None,
        in_block=False,
        in_method=False,
        const_asgn_ok=False,
    )
    body, _ = draw(_stmt_seq(body_env, max(depth - 1, 0), 1, 2))
    final = draw(_expr(body_env, 1))
    return A.Lambda(kind, params, body + (final,))


def _bound_of(params: tuple) -> tuple:
    """Flatten a block/lambda param list to the local names it binds (a `PDestr`
    contributes its sub-names; a named `*rest` contributes its name)."""
    out: list[str] = []
    for p in params:
        if isinstance(p, str):
            out.append(p)
        elif isinstance(p, A.PDestr):
            out.extend(_bound_of(p.subparams))
        elif isinstance(p, A.PRest) and p.name:
            out.append(p.name)
    return tuple(out)


@st.composite
def _block_body(draw, env: Env, depth: int, params: tuple) -> A.Block:
    # A literal block: its params bind as locals; `next`/`break` are legal here,
    # and `return` too when the block is lexically inside a method.
    body_env = replace(
        env, locals=env.locals + _bound_of(params), in_block=True, can_yield=None,
        const_asgn_ok=False,
    )
    body, _ = draw(_stmt_seq(body_env, max(depth - 1, 0), 1, 2))
    final = draw(_expr(body_env, 1))
    return A.Block(params, body + (final,))


@st.composite
def _block_arg(draw, env: Env, depth: int, recv_kind: str) -> A.Node:
    """Draw the trailing block: a literal block, `&proc`, or a safe `&:sym`."""
    lenient_procs = tuple(p for p in env.procs if not p[2])
    choices = ["literal", "literal", "sym", "destr"]
    if lenient_procs:
        choices += ["proc"]
    choice = draw(st.sampled_from(choices))
    if choice == "proc":
        name, _arity, _strict = draw(st.sampled_from(lenient_procs))
        return A.BlockPass(A.LocalRead(name))
    if choice == "sym":
        return A.BlockPass(A.SymLit(draw(st.sampled_from(SAFE_UNARY_SYMS))))
    if choice == "destr":
        # a single destructuring param `|(da, db)|` — lenient over scalars (db→nil)
        # and real over arrays of arrays (the `pairs` receiver in `_block_call`)
        return draw(_block_body(env, depth, (A.PDestr((DESTR_POOL[0], DESTR_POOL[1])),)))
    bparams = BLOCK_PARAM_POOL[: draw(st.integers(0, 2 if recv_kind == "each_index" else 1))]
    return draw(_block_body(env, depth, bparams))


@st.composite
def _block_call(draw, env: Env, depth: int) -> A.BlockCall:
    forms = ["array", "range", "pairs"]
    if env.yielders:
        forms += ["yielder", "yielder"]
    form = draw(st.sampled_from(forms))
    if form == "yielder":
        name, arg_arity, _ = draw(st.sampled_from(env.yielders))
        args = tuple(draw(_expr(env, 1)) for _ in range(arg_arity))
        return A.BlockCall(None, name, args, draw(_block_arg(env, depth, "yielder")))
    if form == "pairs":
        # an array of 2-element arrays → a destructuring block param `|(da, db)|`
        # binds each pair's elements (real array destructuring, not the lenient path)
        n = draw(st.integers(0, 3))
        recv = A.ArrayLit(
            tuple(A.ArrayLit((draw(_literal()), draw(_literal()))) for _ in range(n))
        )
        method = draw(st.sampled_from(["each", "map"]))
        destr = A.PDestr((DESTR_POOL[0], DESTR_POOL[1]))
        return A.BlockCall(recv, method, (), draw(_block_body(env, depth, (destr,))))
    if form == "range":
        lo = draw(st.integers(0, 3))
        recv = A.RangeLit(A.IntLit(lo), A.IntLit(lo + draw(st.integers(0, 3))), draw(st.booleans()))
        method = draw(st.sampled_from(["each", "map", "select"]))
        return A.BlockCall(recv, method, (), draw(_block_arg(env, depth, method)))
    # array: a bounded literal array, so iteration count is bounded
    recv = A.ArrayLit(tuple(draw(_literal()) for _ in range(draw(st.integers(0, 3)))))
    method = draw(st.sampled_from(["each", "map", "select", "reject", "each_with_index"]))
    rk = "each_index" if method == "each_with_index" else method
    return A.BlockCall(recv, method, (), draw(_block_arg(env, depth, rk)))


@st.composite
def _stmt(draw, env: Env, depth: int) -> tuple[A.Node, Env]:
    kinds = ["assign", "assign", "puts", "puts", "puts"]
    if env.assignable:
        kinds += ["opassign"]
    if env.classes:
        kinds += ["new_inst", "new_inst"]
    # a class with an unused external-constant slot → `Cls::E0 = v` (cpath_asgn).
    # Constant assignment is a syntax error inside a method/block body ("dynamic
    # constant assignment"), so only at a static position (top-level / conditional).
    cpath_asgn_targets = tuple(
        ci for ci in env.classes if any(e not in ci.consts for e in EXT_CONST_POOL)
    )
    if cpath_asgn_targets and env.const_asgn_ok:
        kinds += ["cpath_asgn"]
    if env.in_block:
        kinds += ["next", "break"]  # legal only inside a block body
    if env.in_method:
        kinds += ["return"]  # legal only inside a method body
    kinds += ["make_indexable", "massign"]
    if env.indexables:
        kinds += ["index_assign", "index_assign"]
    writer_insts = env.instances_with_writers
    if writer_insts:
        kinds += ["attr_assign", "attr_assign"]
    free_loop_vars = tuple(v for v in LOOP_POOL if v not in env.frozen)
    if depth > 0:
        kinds += ["if", "begin", "begin", "retry_begin", "proc_def", "block_iter", "for", "redo_loop"]
        if free_loop_vars:
            kinds += ["while", "times", "dowhile"]
    kind = draw(st.sampled_from(kinds))

    if kind == "assign":
        name = draw(st.sampled_from(LOCAL_POOL))  # disjoint from LOOP_POOL, so never frozen
        return A.Assign(name, draw(_expr(env, MAX_EXPR_DEPTH - 1))), env.with_local(name)
    if kind == "new_inst":
        ci = draw(st.sampled_from(env.classes))
        var = draw(st.sampled_from(INSTANCE_POOL))  # disjoint from value-local pools
        args = tuple(draw(_expr(env, MAX_EXPR_DEPTH - 1)) for _ in range(ci.ctor_arity))
        # An Assign node that records the binding as an instance (not a plain
        # local), so it is only ever reached as a method-call receiver.
        return A.Assign(var, A.New(ci.name, args)), env.with_instance(var, ci.name)
    if kind == "cpath_asgn":
        ci = draw(st.sampled_from(cpath_asgn_targets))
        # a fresh (unused) external constant slot → no "already initialized" reinit
        name = draw(st.sampled_from(tuple(e for e in EXT_CONST_POOL if e not in ci.consts)))
        new_ci = replace(ci, consts=ci.consts + (name,))
        return A.ConstPathAssign(ci.name, name, draw(_expr(env, 1))), env.update_class(ci.name, new_ci)
    if kind == "opassign":
        name = draw(st.sampled_from(env.assignable))
        op = draw(st.sampled_from(["+=", "-=", "*=", "||="]))
        return A.OpAssign(name, op, draw(_expr(env, 1))), env
    if kind == "proc_def":
        var = draw(st.sampled_from(PROC_POOL))
        lam = draw(_lambda(env, depth))
        strict = lam.kind in ("->", "lambda")
        return A.Assign(var, lam), env.with_proc(var, len(lam.params), strict)
    if kind == "block_iter":
        bc = draw(_block_call(env, depth))
        if draw(st.booleans()):
            name = draw(st.sampled_from(LOCAL_POOL))
            return A.Assign(name, bc), env.with_local(name)
        return bc, env
    if kind == "make_indexable":
        name = draw(st.sampled_from(INDEXABLE_POOL))
        if draw(st.booleans()):
            lit = A.ArrayLit(tuple(draw(_literal()) for _ in range(draw(st.integers(0, 3)))))
            kindk = "array"
        else:
            n = draw(st.integers(1, 2))
            lit = A.HashLit(tuple((A.SymLit(SYM_POOL[k]), draw(_literal())) for k in range(n)))
            kindk = "hash"
        return A.Assign(name, lit), env.with_indexable(name, kindk)
    if kind == "index_assign":
        name, ik = draw(st.sampled_from(env.indexables))
        index = A.SymLit(draw(st.sampled_from(SYM_POOL))) if ik == "hash" else A.IntLit(
            draw(st.integers(0, 3))
        )
        if draw(st.booleans()):
            return A.IndexAssign(A.LocalRead(name), index, draw(_expr(env, 1))), env
        # `||=` is safe whatever the current element holds (once-only obligation intact)
        return A.IndexOpAssign(A.LocalRead(name), index, "||=", draw(_expr(env, 1))), env
    if kind == "attr_assign":
        # plain writer send only: `obj.x ||= v` would need a reader too (accessor),
        # and the once-only read-modify-write obligation is already covered by
        # `a[i] ||= v` above — so keep this to the pure writer-call.
        inst_name, _cls, writers = draw(st.sampled_from(writer_insts))
        attr = draw(st.sampled_from(writers))
        return A.AttrAssign(A.LocalRead(inst_name), attr, draw(_expr(env, 1))), env
    if kind == "massign":
        n = draw(st.integers(2, 3))
        targets = tuple(LOCAL_POOL[:n])
        splat_index = draw(st.one_of(st.none(), st.integers(0, n - 1)))
        nvals = draw(st.integers(n, n + 1))
        values = tuple(draw(_expr(env, 1)) for _ in range(nvals))
        env2 = env
        for t in targets:
            env2 = env2.with_local(t)
        return A.MultiAssign(targets, splat_index, values), env2
    if kind == "next":
        return A.Next(draw(st.one_of(st.none(), _expr(env, 1)))), env
    if kind == "break":
        return A.Break(draw(st.one_of(st.none(), _expr(env, 1)))), env
    if kind == "return":
        return A.Return(draw(st.one_of(st.none(), _expr(env, 1)))), env
    if kind == "puts":
        n = draw(st.integers(1, 2))
        return A.Puts(tuple(draw(_expr(env, 2)) for _ in range(n))), env
    if kind == "if":
        cond = draw(_expr(env, 2, no_range_head=True))
        then, _ = draw(_stmt_seq(env, depth - 1, 1, 3))
        orelse = draw(st.one_of(st.none(), _stmt_seq(env, depth - 1, 1, 2)))
        # conservative scoping: locals introduced inside branches are not
        # exposed to later statements (Ruby would define them as nil; we
        # simply never read them, which is sound)
        return A.If(cond, then, orelse[0] if orelse else None), env
    if kind == "while":
        var = draw(st.sampled_from(free_loop_vars))
        # `next`/`break` would target *this* loop and skip the manual `+= 1`
        # increment the renderer appends → infinite loop. Disable them in the
        # body (a nested block/times re-enables them, targeting itself, safely).
        body_env = replace(env.with_frozen(var), in_block=False)
        body, _ = draw(_stmt_seq(body_env, depth - 1, 1, 2))
        return A.WhileCounter(var, draw(st.integers(0, 3)), body), env.with_local(var)
    if kind == "times":
        var = draw(st.sampled_from(free_loop_vars))
        # a `times` block is self-counting, so `next`/`break` are safe here
        body_env = replace(env.with_local(var), in_block=True, const_asgn_ok=False)
        body, _ = draw(_stmt_seq(body_env, depth - 1, 1, 2))
        return A.TimesBlock(draw(st.integers(0, 3)), var, body), env
    if kind == "for":
        var = draw(st.sampled_from(FOR_POOL))
        # a bounded array or range → iteration terminates; `next`/`break` are safe
        if draw(st.booleans()):
            coll = A.ArrayLit(tuple(draw(_literal()) for _ in range(draw(st.integers(0, 3)))))
        else:
            lo = draw(st.integers(0, 3))
            coll = A.RangeLit(A.IntLit(lo), A.IntLit(lo + draw(st.integers(0, 3))), draw(st.booleans()))
        body_env = replace(env.with_local(var), in_block=True)
        body, _ = draw(_stmt_seq(body_env, depth - 1, 1, 2))
        # the loop var leaks to the enclosing scope (Ruby `for` semantics)
        return A.ForLoop(var, coll, body), env.with_local(var)
    if kind == "dowhile":
        var = draw(st.sampled_from(free_loop_vars))
        # like `while`: `next`/`break` would skip the manual `+= 1` the renderer
        # appends → infinite loop, so disable them in the body
        body_env = replace(env.with_frozen(var), in_block=False)
        body, _ = draw(_stmt_seq(body_env, depth - 1, 1, 2))
        return A.DoWhile(var, draw(st.integers(0, 3)), body), env.with_local(var)
    if kind == "redo_loop":
        guard = draw(st.sampled_from(REDO_POOL))
        limit = draw(st.integers(1, 3))
        # a non-empty bounded array so the block runs and `redo` has an iteration
        coll = A.ArrayLit(tuple(draw(_literal()) for _ in range(draw(st.integers(1, 3)))))
        blockvar = BLOCK_PARAM_POOL[0]
        inner_env = replace(
            env.with_frozen(guard).with_local(blockvar), in_block=True, const_asgn_ok=False
        )
        extra, _ = draw(_stmt_seq(inner_env, max(depth - 2, 0), 1, 1))
        # guard += 1 on every (re)entry, then redo only while guard < limit → bounded
        block_body = (
            A.OpAssign(guard, "+=", A.IntLit(1)),
            A.If(A.BinOp("<", A.LocalRead(guard), A.IntLit(limit)), (A.Redo(),), None),
        ) + extra + (A.NilLit(),)
        return A.RedoLoop(guard, coll, blockvar, block_body), env.with_frozen(guard)
    if kind == "begin":
        body, _ = draw(_stmt_seq(env, depth - 1, 1, 2))
        # optionally raise; track the class so a typed clause can match it
        raised = None
        if draw(st.booleans()):
            msg = draw(st.sampled_from(["boom", "bad"]))
            if draw(st.booleans()):
                raised = draw(st.sampled_from(EXC_CLASSES))
                body = body + (A.Raise(msg, raised),)
            else:
                raised = "RuntimeError"  # bare `raise(msg)` raises RuntimeError
                body = body + (A.Raise(msg),)
        renv = env.with_local("e")

        def _rbody():
            rb, _ = draw(_stmt_seq(renv, 0, 1, 1))
            return (A.Puts((A.StrInterp(("err:", A.LocalRead("e"))),)),) + rb

        rescues: list = []
        # a leading typed clause that does NOT match the raised class (skipped at runtime)
        if raised and draw(st.booleans()):
            nonmatch = draw(st.sampled_from(tuple(c for c in EXC_CLASSES if c != raised)))
            rescues.append(((nonmatch,), "e", _rbody()))
        # a typed clause that DOES match (exercises typed rescue)
        if raised and draw(st.booleans()):
            others = tuple(c for c in EXC_CLASSES if c != raised)
            classes = (raised,) if draw(st.booleans()) else (draw(st.sampled_from(others)), raised)
            rescues.append((classes, "e", _rbody()))
        # a final bare catch-all → nothing ever propagates (any stray deterministic
        # error from the body is caught here too), so `else` runs iff no exception
        rescues.append(((), "e", _rbody()))
        else_body = None
        if draw(st.booleans()):
            eb, _ = draw(_stmt_seq(env, 0, 1, 1))
            else_body = (A.Puts((A.StrLit("else-ran"),)),) + eb
        ensure_body = None
        if draw(st.booleans()):
            enb, _ = draw(_stmt_seq(env, 0, 1, 1))
            ensure_body = (A.Puts((A.StrLit("ensure-ran"),)),) + enb
        return A.BeginResc(body, tuple(rescues), else_body, ensure_body), env
    if kind == "retry_begin":
        guard = draw(st.sampled_from(RETRY_POOL))
        limit = draw(st.integers(1, 3))
        # guard increments each attempt; the raise stops once guard > limit, so the
        # begin succeeds after limit+1 attempts. No random body stmts (they might
        # raise and make `retry` spin) — just the guarded raise.
        body = (
            A.OpAssign(guard, "+=", A.IntLit(1)),
            A.If(A.BinOp("<=", A.LocalRead(guard), A.IntLit(limit)), (A.Raise("boom"),), None),
            A.NilLit(),
        )
        rescue_body = (A.Puts((A.StrInterp(("retry:", A.LocalRead("e"))),)),)
        return A.RetryBegin(guard, limit, body, "e", rescue_body), env.with_frozen(guard)
    raise AssertionError(kind)


@st.composite
def _stmt_seq(draw, env: Env, depth: int, min_n: int, max_n: int) -> tuple[tuple, Env]:
    n = draw(st.integers(min_n, max_n))
    stmts = []
    for _ in range(n):
        node, env = draw(_stmt(env, depth))
        stmts.append(node)
    return tuple(stmts), env


def _merge(base: tuple, add: tuple) -> tuple:
    """Union method (name, arity) lists; entries in `add` override same-named ones."""
    names = {n for n, _ in add}
    return tuple((n, a) for (n, a) in base if n not in names) + add


@st.composite
def _method_body(draw, name, arity, callable_methods, ivars, classes, modules, can_super, is_def=True, sigs=()):
    """A `MethodDef` whose body may self-send `callable_methods`, read `ivars`,
    instantiate `classes`, and (when `can_super` is set) call `super`.

    `is_def=False` for a `define_method`/`define_singleton_method` body: that is a
    *block*, not a `def`, so a lexical `return` there is a top-level return (the
    desugar's `@fn_depth` gate only counts real `def` bodies) — suppress it."""
    params = PARAM_POOL[:arity]
    body_env = Env(
        locals=params,
        methods=callable_methods,
        ivars=ivars,
        classes=classes,
        modules=modules,
        in_method=is_def,
        can_super=can_super,
        sigs=sigs,
        const_asgn_ok=False,
    )
    body, _ = draw(_stmt_seq(body_env, 1, 1, 3))
    final = draw(_expr(body_env, 2))
    return A.MethodDef(name, params, body + (final,))


@st.composite
def _module_def(draw, env: Env, name: str) -> tuple[A.ModuleDef, Env]:
    methods: list[A.MethodDef] = []
    minfos: list[tuple[str, int]] = []
    for k in range(draw(st.integers(1, len(MMETHOD_POOL)))):
        arity = draw(st.integers(0, len(PARAM_POOL)))
        # module-method bodies carry no ivars (an includer may lack them) and see
        # earlier module methods (bare self-sends once mixed in) + prior classes
        m = draw(
            _method_body(
                MMETHOD_POOL[k], arity, env.methods + tuple(minfos), (), env.classes, (), None,
                sigs=env.sigs,
            )
        )
        methods.append(m)
        minfos.append((MMETHOD_POOL[k], arity))
    return A.ModuleDef(name, tuple(methods)), env.with_module(ModuleInfo(name, tuple(minfos)))


@st.composite
def _class_def(draw, env: Env, name: str) -> tuple[A.ClassDef, Env]:
    # superclass: a prior class, or none (< Object); mixins: prior modules
    sup = draw(st.sampled_from((None,) + tuple(ci.name for ci in env.classes)))
    sup_ci = env.class_info(sup) if sup else None
    mixins: list[tuple[str, str]] = []
    mixed: tuple = ()
    for mi in env.modules:
        if draw(st.booleans()):
            mixins.append((mi.name, draw(st.sampled_from(["include", "prepend"]))))
            mixed = _merge(mixed, mi.methods)

    # a subclass inherits its parent's `initialize` (ivars=()); base class owns ivars
    if sup_ci is not None:
        ivars: tuple = ()
        ctor_arity = sup_ci.ctor_arity
        inherited = sup_ci.imethods
    else:
        ivars = IVAR_POOL[: draw(st.integers(0, len(IVAR_POOL)))]
        ctor_arity = len(ivars)
        inherited = ()
    effective = _merge(inherited, mixed)  # methods visible on instances so far
    eff_ivars = IVAR_POOL[:ctor_arity]  # ivars are always a prefix of IVAR_POOL

    # class/self methods (self is the class; call as `C.sm(args)`)
    self_methods: list[A.MethodDef] = []
    sinfos: list[tuple[str, int]] = []
    for k in range(draw(st.integers(0, len(SMETHOD_POOL)))):
        arity = draw(st.integers(0, len(PARAM_POOL)))
        self_methods.append(
            draw(_method_body(SMETHOD_POOL[k], arity, env.methods, (), env.classes, (), None, sigs=env.sigs))
        )
        sinfos.append((SMETHOD_POOL[k], arity))

    # ---- metaprogramming class-body decls (registered so later methods can call them)
    decls: list[A.Node] = []
    const_names: list[str] = []
    for cn in CONST_POOL[: draw(st.integers(0, len(CONST_POOL)))]:
        decls.append(A.ConstAssign(cn, draw(_literal())))  # readable as `Name::cn`
        const_names.append(cn)
    attr_writers: tuple = ()
    base_names = tuple(iv[1:] for iv in eff_ivars)  # attr only over ivars the class has
    if base_names and draw(st.booleans()):
        kind = draw(st.sampled_from(["accessor", "reader", "writer"]))
        names = tuple(n for n in base_names if draw(st.booleans())) or base_names[:1]
        decls.append(A.AttrDecl(kind, names))
        if kind in ("accessor", "reader"):
            effective = _merge(effective, tuple((n, 0) for n in names))
        if kind in ("accessor", "writer"):
            attr_writers = names
    for k in range(draw(st.integers(0, len(DMETHOD_POOL)))):  # define_method → instance method
        arity = draw(st.integers(0, len(PARAM_POOL)))
        callable_methods = tuple(env.methods) + tuple(
            e for e in effective if _callable_ok(e[0], DMETHOD_POOL[k])
        )
        m = draw(_method_body(DMETHOD_POOL[k], arity, callable_methods, eff_ivars, env.classes, env.modules, None, is_def=False, sigs=env.sigs))
        decls.append(A.DefineMethod(DMETHOD_POOL[k], m.params, m.body, False))
        effective = _merge(effective, ((DMETHOD_POOL[k], arity),))
    for k in range(draw(st.integers(0, len(DSM_POOL)))):  # define_singleton_method → class method
        arity = draw(st.integers(0, len(PARAM_POOL)))
        m = draw(_method_body(DSM_POOL[k], arity, env.methods, (), env.classes, (), None, is_def=False, sigs=env.sigs))
        decls.append(A.DefineMethod(DSM_POOL[k], m.params, m.body, True))
        sinfos.append((DSM_POOL[k], arity))
    if draw(st.booleans()):  # `class << self; def esm; end; end` → class method (sclass)
        arity = draw(st.integers(0, len(PARAM_POOL)))
        em = draw(_method_body(ESM_POOL[0], arity, env.methods, (), env.classes, (), None, sigs=env.sigs))
        decls.append(A.EigenClass((em,)))
        sinfos.append((ESM_POOL[0], arity))

    # instance methods: fresh im-names, or overrides of an inherited im-method (+ super)
    methods: list[A.MethodDef] = []
    own: tuple = ()
    overridable = tuple(m for m in inherited if m[0] in IMETHOD_POOL)
    for k in range(draw(st.integers(0, len(IMETHOD_POOL)))):
        if overridable and draw(st.booleans()):
            mname, arity = draw(st.sampled_from(overridable))
            can_super = arity  # `super` reaches the parent's version
        else:
            mname, arity, can_super = IMETHOD_POOL[k], draw(st.integers(0, len(PARAM_POOL))), None
        # bare-callable = top-level (always) + instance methods of strictly-lower
        # global rank (`_callable_ok`) — the acyclicity invariant that survives
        # inheritance/override/shadowing (a shadowing subclass method has the same
        # *name*, hence the same rank, so it still only calls lower names → no cycle).
        callable_methods = tuple(env.methods) + tuple(
            e for e in _merge(effective, own) if _callable_ok(e[0], mname)
        )
        methods.append(
            draw(
                _method_body(
                    mname, arity, callable_methods, eff_ivars, env.classes, env.modules, can_super,
                    sigs=env.sigs,
                )
            )
        )
        own = _merge(own, ((mname, arity),))

    effective = _merge(effective, own)

    # method_missing: a `MethodCall` to a never-defined name (`ghost0`) on an instance
    # of this class routes here (see `_expr` `mm_call`). Returns a deterministic string;
    # kept OUT of `effective` so it is only reached via missing dispatch, never directly.
    if draw(st.booleans()):
        methods.append(
            A.MethodDef(
                "method_missing",
                ("name", A.PRest("args")),
                (A.StrInterp(("mm-", A.LocalRead("name"))),),
            )
        )
        own_mm = True
    else:
        own_mm = False
    # method_missing is INHERITED: a subclass of an mm-class is itself an mm-class even
    # if it doesn't define method_missing. Must be inheritance-aware or the `new`-gate
    # (and value-flow avoidance) leaks a subclass instance into interpolation.
    has_mm = own_mm or (sup_ci is not None and sup_ci.has_mm)

    # ---- tail decls: alias/undef (method-table heap mutation), rendered *after* the
    # instance methods so the referenced method is already defined in the class body
    tail_decls: list[A.Node] = []
    if effective and draw(st.booleans()):  # alias an existing method to a fresh name
        old, oarity = draw(st.sampled_from(effective))
        new = draw(st.sampled_from(ALIAS_POOL))
        tail_decls.append(A.Alias(new, old, draw(st.booleans())))
        effective = _merge(effective, ((new, oarity),))
    if draw(st.booleans()):  # define a throwaway method and undef it (never called)
        ud = UNDEF_POOL[0]
        methods.append(A.MethodDef(ud, (), (A.NilLit(),)))
        tail_decls.append(A.Undef(ud))

    ci = ClassInfo(
        name, ctor_arity, effective, tuple(sinfos), attr_writers, tuple(const_names), has_mm
    )
    node = A.ClassDef(
        name, sup, tuple(mixins), ivars, tuple(self_methods), tuple(methods), tuple(decls),
        tuple(tail_decls),
    )
    return node, env.with_class(ci)


@st.composite
def _reopen(draw, env: Env, ci: ClassInfo) -> tuple[A.ClassDef, Env]:
    """`class C; def rm0(...) ... end; end` reopening an existing class."""
    k = draw(st.integers(0, len(ROPEN_POOL) - 1))
    arity = draw(st.integers(0, len(PARAM_POOL)))
    callable_methods = tuple(env.methods) + tuple(
        e for e in ci.imethods if _callable_ok(e[0], ROPEN_POOL[k])
    )
    m = draw(
        _method_body(
            ROPEN_POOL[k], arity, callable_methods, IVAR_POOL[: ci.ctor_arity], env.classes, (), None,
            sigs=env.sigs,
        )
    )
    node = A.ClassDef(ci.name, None, (), (), (), (m,))
    new_ci = replace(ci, imethods=_merge(ci.imethods, ((ROPEN_POOL[k], arity),)))
    return node, env.update_class(ci.name, new_ci)


@st.composite
def programs(draw) -> A.Program:
    env = Env()
    stmts: list[A.Node] = []
    n_defs = draw(st.integers(0, 3))
    for k in range(n_defs):
        name = METHOD_POOL[k]
        # method flavors: `plain`, `varied` (optional/keyword/rest/kwrest params),
        # `fwd` (`def m(...); sink(...); end` — needs a prior `*rest`+`**kwrest`
        # sink to absorb anything), or `yielder` (yields, invoked only with a block).
        sink_names = [n for (n, s) in env.sigs if s.rest and s.kwrest and not s.fwd]
        flavor_pool = ["plain", "varied", "varied", "yielder", "yielder"]
        if sink_names:
            flavor_pool += ["fwd"]
        flavor = draw(st.sampled_from(flavor_pool))

        if flavor == "fwd":
            sink = draw(st.sampled_from(sink_names))
            stmts.append(A.MethodDef(name, (A.PFwd(),), (A.Call(sink, (A.FwdArg(),)),)))
            env = env.with_method(name, 0).with_sig(name, Sig(fwd=True))
            continue

        if flavor == "varied":
            params, sig, bound = draw(_method_param_spec(2))
            body_env = Env(
                locals=bound, methods=env.methods, in_method=True, sigs=env.sigs,
                const_asgn_ok=False,
            )
            body, _ = draw(_stmt_seq(body_env, 1, 1, 3))
            final = draw(_expr(body_env, 2))
            stmts.append(A.MethodDef(name, params, body + (final,)))
            env = env.with_method(name, sig.reqpos).with_sig(name, sig)
            continue

        arity = draw(st.integers(0, len(PARAM_POOL)))
        params = PARAM_POOL[:arity]
        # yielders go in `env.yielders` (not `methods`), so they are only ever
        # invoked with a block (via `_block_call`) — never a blockless LocalJumpError
        yields = flavor == "yielder" and arity >= 1
        body_env = Env(
            locals=params, methods=env.methods, in_method=True,
            can_yield=1 if yields else None, sigs=env.sigs, const_asgn_ok=False,
        )
        body, _ = draw(_stmt_seq(body_env, 1, 1, 3))
        # make the return value depend on the params when there are any
        final = draw(_expr(body_env, 2))
        stmts.append(A.MethodDef(name, params, body + (final,)))
        env = env.with_yielder(name, arity, 1) if yields else env.with_method(name, arity)
    n_modules = draw(st.integers(0, len(MODULE_POOL)))
    for c in range(n_modules):
        mod_node, env = draw(_module_def(env, MODULE_POOL[c]))
        stmts.append(mod_node)
    n_classes = draw(st.integers(0, len(CLASS_POOL)))
    for c in range(n_classes):
        cls_node, env = draw(_class_def(env, CLASS_POOL[c]))
        stmts.append(cls_node)
    # reopen a few existing classes to add methods (heap mutation of the class object)
    for ci in list(env.classes):
        if draw(st.booleans()):
            reopen_node, env = draw(_reopen(env, ci))
            stmts.append(reopen_node)
    main, env = draw(_stmt_seq(env, 3, 1, 6))
    stmts.extend(main)
    stmts.append(A.Puts((draw(_expr(env, 2)),)))  # always end with observable output
    return A.Program(tuple(stmts))
