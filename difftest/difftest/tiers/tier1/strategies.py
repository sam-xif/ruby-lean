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
PARAM_POOL = ("x", "y")
METHOD_POOL = ("m0", "m1", "m2")
STR_POOL = ("hi", "ok", "zap", "a b", "")
SYM_POOL = ("k", "v", "s")

MAX_EXPR_DEPTH = 3


@dataclass(frozen=True)
class Env:
    locals: tuple[str, ...] = ()
    methods: tuple[tuple[str, int], ...] = ()  # (name, arity)
    # names that must not be (re)assigned — loop counters, whose progress
    # guarantees termination; they stay readable
    frozen: tuple[str, ...] = ()

    def with_local(self, name: str) -> "Env":
        return self if name in self.locals else replace(self, locals=self.locals + (name,))

    def with_frozen(self, name: str) -> "Env":
        return replace(self.with_local(name), frozen=self.frozen + (name,))

    def with_method(self, name: str, arity: int) -> "Env":
        return replace(self, methods=self.methods + ((name, arity),))

    @property
    def assignable(self) -> tuple[str, ...]:
        return tuple(n for n in self.locals if n not in self.frozen)


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
def _expr(draw, env: Env, depth: int) -> A.Node:
    kinds = ["lit", "lit"]
    if env.locals:
        kinds += ["local", "local", "local"]
    if env.methods:
        kinds += ["call", "call"]
    if depth > 0:
        kinds += ["binop", "binop", "and", "or", "not", "interp", "array", "index", "hash"]
    kind = draw(st.sampled_from(kinds))

    sub = lambda: draw(_expr(env, depth - 1))  # noqa: E731

    if kind == "lit":
        return draw(_literal())
    if kind == "local":
        return A.LocalRead(draw(st.sampled_from(env.locals)))
    if kind == "call":
        name, arity = draw(st.sampled_from(env.methods))
        return A.Call(name, tuple(draw(_expr(env, depth - 1)) for _ in range(arity)))
    if kind == "binop":
        op = draw(st.sampled_from(["+", "+", "-", "*", "%", "==", "<", ">", "<=", ">="]))
        return A.BinOp(op, sub(), sub())
    if kind == "and":
        return A.And(sub(), sub())
    if kind == "or":
        return A.Or(sub(), sub())
    if kind == "not":
        return A.Not(sub())
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
def _stmt(draw, env: Env, depth: int) -> tuple[A.Node, Env]:
    kinds = ["assign", "assign", "puts", "puts", "puts"]
    if env.assignable:
        kinds += ["opassign"]
    free_loop_vars = tuple(v for v in LOOP_POOL if v not in env.frozen)
    if depth > 0:
        kinds += ["if", "begin"]
        if free_loop_vars:
            kinds += ["while", "times"]
    kind = draw(st.sampled_from(kinds))

    if kind == "assign":
        name = draw(st.sampled_from(LOCAL_POOL))  # disjoint from LOOP_POOL, so never frozen
        return A.Assign(name, draw(_expr(env, MAX_EXPR_DEPTH - 1))), env.with_local(name)
    if kind == "opassign":
        name = draw(st.sampled_from(env.assignable))
        op = draw(st.sampled_from(["+=", "-=", "*=", "||="]))
        return A.OpAssign(name, op, draw(_expr(env, 1))), env
    if kind == "puts":
        n = draw(st.integers(1, 2))
        return A.Puts(tuple(draw(_expr(env, 2)) for _ in range(n))), env
    if kind == "if":
        cond = draw(_expr(env, 2))
        then, _ = draw(_stmt_seq(env, depth - 1, 1, 3))
        orelse = draw(st.one_of(st.none(), _stmt_seq(env, depth - 1, 1, 2)))
        # conservative scoping: locals introduced inside branches are not
        # exposed to later statements (Ruby would define them as nil; we
        # simply never read them, which is sound)
        return A.If(cond, then, orelse[0] if orelse else None), env
    if kind == "while":
        var = draw(st.sampled_from(free_loop_vars))
        body_env = env.with_frozen(var)  # readable, but never reassigned in the body
        body, _ = draw(_stmt_seq(body_env, depth - 1, 1, 2))
        return A.WhileCounter(var, draw(st.integers(0, 3)), body), env.with_local(var)
    if kind == "times":
        var = draw(st.sampled_from(free_loop_vars))
        body, _ = draw(_stmt_seq(env.with_local(var), depth - 1, 1, 2))
        return A.TimesBlock(draw(st.integers(0, 3)), var, body), env
    if kind == "begin":
        body, _ = draw(_stmt_seq(env, depth - 1, 1, 2))
        if draw(st.booleans()):
            body = body + (A.Raise(draw(st.sampled_from(["boom", "bad"]))),)
        rescue_env = env.with_local("e")
        rescue_body, _ = draw(_stmt_seq(rescue_env, 0, 1, 1))
        rescue_body = (A.Puts((A.StrInterp(("err:", A.LocalRead("e"))),)),) + rescue_body
        return A.BeginRescue(body, "e", rescue_body), env
    raise AssertionError(kind)


@st.composite
def _stmt_seq(draw, env: Env, depth: int, min_n: int, max_n: int) -> tuple[tuple, Env]:
    n = draw(st.integers(min_n, max_n))
    stmts = []
    for _ in range(n):
        node, env = draw(_stmt(env, depth))
        stmts.append(node)
    return tuple(stmts), env


@st.composite
def programs(draw) -> A.Program:
    env = Env()
    stmts: list[A.Node] = []
    n_defs = draw(st.integers(0, 2))
    for k in range(n_defs):
        name = METHOD_POOL[k]
        arity = draw(st.integers(0, len(PARAM_POOL)))
        params = PARAM_POOL[:arity]
        # method bodies see their params as locals and may call earlier methods
        body_env = Env(locals=params, methods=env.methods)
        body, _ = draw(_stmt_seq(body_env, 1, 1, 3))
        # make the return value depend on the params when there are any
        final = draw(_expr(body_env, 2))
        stmts.append(A.MethodDef(name, params, body + (final,)))
        env = env.with_method(name, arity)
    main, env = draw(_stmt_seq(env, 3, 1, 6))
    stmts.extend(main)
    stmts.append(A.Puts((draw(_expr(env, 2)),)))  # always end with observable output
    return A.Program(tuple(stmts))
