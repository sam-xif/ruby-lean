"""Tier-1 class and module definitions, and reopening.

Split out of `strategies.py` (N35), no behaviour change.
"""

from __future__ import annotations

from hypothesis import strategies as st

from . import ast as A
from .env import *  # noqa: F403
from .env import ClassInfo, Env, ModuleInfo, Sig, _callable_ok  # noqa: F401
from .exprs import *  # noqa: F403
from .exprs import _expr, _literal, _method_param_spec  # noqa: F401
from .stmts import *  # noqa: F403
from .stmts import _merge, _method_body, _stmt_seq  # noqa: F401

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
