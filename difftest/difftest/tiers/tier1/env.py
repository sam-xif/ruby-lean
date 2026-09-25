"""Tier-1 generation environment: the name pools, and the scope record.

The single highest-leverage design feature (the prong-2 design, `docs/front-end/method.md` 06 §4) lives here: an
`Env` of bound locals, defined methods, classes and modules threads through
top-down generation, so generated programs reference names that resolve and
method dispatch actually fires — instead of every program dying at line 1 with
NameError.

Split out of `strategies.py` (N35), no behaviour change.
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
