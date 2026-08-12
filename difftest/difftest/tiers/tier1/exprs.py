"""Tier-1 expression strategies: literals, calls, operators, lambdas, blocks.

Expressions and statements are mutually recursive (a block body is a statement
sequence; a statement contains expressions), so `_block_body` imports
`_stmt_seq` at call time rather than at module load. That one deferred import is
the whole cost of keeping the two categories in separate files.

Split out of `strategies.py` (N35), no behaviour change.
"""

from __future__ import annotations

from hypothesis import strategies as st

from . import ast as A
from .env import *  # noqa: F403
from .env import Env, Sig, _callable_ok  # noqa: F401

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
    if depth > 0:
        kinds += ["binop", "binop", "and", "or", "not", "interp", "array", "index", "hash"]
        if not no_range_head:
            kinds += ["range"]
        if env.classes:
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
        # method_missing objects may now flow into interpolation safely — the desugar
        # lowers `"#{e}"` to `rb_obj_as_string` (to_s, not `Kernel#String`'s to_str),
        # so `"#{C.new}"` agrees again (desugar C30 / difftest N22 addendum).
        ci = draw(st.sampled_from(env.classes))
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
    from .stmts import _stmt_seq  # deferred: expressions and statements are mutually recursive

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
    from .stmts import _stmt_seq  # deferred: expressions and statements are mutually recursive

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
