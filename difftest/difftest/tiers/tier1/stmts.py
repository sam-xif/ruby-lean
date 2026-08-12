"""Tier-1 statement strategies: assignment, control flow, exceptions, method bodies.

Split out of `strategies.py` (N35), no behaviour change.
"""

from __future__ import annotations

from hypothesis import strategies as st

from . import ast as A
from .env import *  # noqa: F403
from .env import Env, Sig, _callable_ok  # noqa: F401
from .exprs import *  # noqa: F403
from .exprs import _block_call, _expr, _lambda, _literal, _method_param_spec  # noqa: F401

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
