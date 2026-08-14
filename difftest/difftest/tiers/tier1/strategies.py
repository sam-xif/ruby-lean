"""Tier-1 program generation — the top-level strategy.

The grammar itself lives in `env.py` (pools + scope record), `exprs.py`,
`stmts.py` and `classes.py`; this module assembles a whole program and is the
public entry point (`programs`). Split out of a single 1,087-line file (N35),
no behaviour change.
"""

from __future__ import annotations

from hypothesis import strategies as st

from . import ast as A
from .env import *  # noqa: F403
from .env import ClassInfo, Env, ModuleInfo, Sig  # noqa: F401
from .exprs import *  # noqa: F403
from .exprs import _block_call, _expr, _method_param_spec  # noqa: F401
from .stmts import *  # noqa: F403
from .stmts import _stmt_seq  # noqa: F401
from .classes import *  # noqa: F403
from .classes import _class_def, _module_def, _reopen  # noqa: F401
from .slice_heads import (
    comparable_probe,
    regex_interp_probe,
    regex_probe,
    range_probe,
    regex_scope_probe,
)

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
    # W4b — the slice's own feature set, as self-contained probe blocks appended
    # after the generated body (see `slice_heads.py` for why they are blocks and
    # not `_expr` heads). They introduce their own locals/classes from disjoint
    # pools, so they neither read nor disturb `env`.
    for i in range(draw(st.integers(0, 2))):
        stmts.extend(draw(regex_probe(i)))
    for i in range(draw(st.integers(0, 1))):
        stmts.extend(draw(comparable_probe(i)))
    for i in range(draw(st.integers(0, 1))):
        stmts.extend(draw(regex_interp_probe(i)))
    for i in range(draw(st.integers(0, 1))):
        stmts.extend(draw(regex_scope_probe(i)))
    for i in range(draw(st.integers(0, 1))):
        stmts.extend(draw(range_probe(i)))
    stmts.append(A.Puts((draw(_expr(env, 2)),)))  # always end with observable output
    return A.Program(tuple(stmts))
