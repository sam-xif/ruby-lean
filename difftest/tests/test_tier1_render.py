"""Property: every generated program parses under CRuby and runs deterministically.

Kept to a small example count — each check is a CRuby subprocess.
"""

import pytest
from hypothesis import HealthCheck, given, settings

from difftest.control import CRubyRunner
from difftest.tiers.tier1.render import render_program
from difftest.tiers.tier1.strategies import programs

runner = CRubyRunner(timeout=10.0)


@settings(
    max_examples=25, deadline=None, database=None, suppress_health_check=list(HealthCheck)
)
@given(programs())
def test_generated_programs_parse(prog):
    src = render_program(prog)
    err = runner.check_parses(src)
    assert err is None, f"generated program does not parse:\n{src}\n{err}"


@settings(
    max_examples=10, deadline=None, database=None, suppress_health_check=list(HealthCheck)
)
@given(programs())
def test_generated_programs_deterministic(prog):
    src = render_program(prog)
    obs, why = runner.run_deterministic(src)
    assert obs is not None, f"generated program excluded ({why}):\n{src}"


def test_render_smoke():
    from difftest.tiers.tier1 import ast as A

    prog = A.Program(
        (
            A.MethodDef("m0", ("x",), (A.BinOp("+", A.LocalRead("x"), A.IntLit(1)),)),
            A.Assign("a", A.Call("m0", (A.IntLit(2),))),
            A.Puts((A.StrInterp(("a=", A.LocalRead("a"))),)),
        )
    )
    src = render_program(prog)
    obs = runner.run(src)
    assert obs.stdout == "a=3\n"


def test_block_yield_smoke():
    from difftest.tiers.tier1 import ast as A

    # def m0(x); yield(x); end ;  puts(m0(3) { |a| a + 1 })  →  4
    prog = A.Program(
        (
            A.MethodDef("m0", ("x",), (A.Yield((A.LocalRead("x"),)),)),
            A.Puts(
                (
                    A.BlockCall(
                        None,
                        "m0",
                        (A.IntLit(3),),
                        A.Block(("a",), (A.BinOp("+", A.LocalRead("a"), A.IntLit(1)),)),
                    ),
                )
            ),
        )
    )
    assert runner.run(render_program(prog)).stdout == "4\n"


def test_inheritance_super_smoke():
    from difftest.tiers.tier1 import ast as A

    # C0#im0 returns @x; C1 < C0 overrides im0 = super() + 1 ;  C1.new(10).im0  →  11
    c0 = A.ClassDef("C0", None, (), ("@x",), (), (A.MethodDef("im0", (), (A.IvarRead("@x"),)),))
    c1 = A.ClassDef(
        "C1", "C0", (), (), (), (A.MethodDef("im0", (), (A.BinOp("+", A.Super(()), A.IntLit(1)),)),)
    )
    prog = A.Program(
        (c0, c1, A.Puts((A.MethodCall(A.New("C1", (A.IntLit(10),)), "im0", ()),)))
    )
    assert runner.run(render_program(prog)).stdout == "11\n"


def test_metaprogramming_writer_smoke():
    from difftest.tiers.tier1 import ast as A

    # attr_accessor :x ; o = C0.new(5); o.x = 9; puts(o.send(:x))  →  9
    c0 = A.ClassDef(
        "C0", None, (), ("@x",), (), (), (A.AttrDecl("accessor", ("x",)),)
    )
    prog = A.Program(
        (
            c0,
            A.Assign("o", A.New("C0", (A.IntLit(5),))),
            A.AttrAssign(A.LocalRead("o"), "x", A.IntLit(9)),
            A.Puts((A.SendCall(A.LocalRead("o"), "x", (), False),)),
        )
    )
    assert runner.run(render_program(prog)).stdout == "9\n"


def test_varied_params_smoke():
    from difftest.tiers.tier1 import ast as A

    # def m0(x, o1 = x, k1:, **o9); [x, o1, k1, o9]; end
    # puts(m0(1, k1: 2, extra: 9))  →  [1, 1, 2, {:extra=>9}]
    params = (
        "x",
        A.POpt("o1", A.LocalRead("x")),
        A.PKey("k1", None),
        A.PKwRest("o9"),
    )
    body = (
        A.ArrayLit(
            (A.LocalRead("x"), A.LocalRead("o1"), A.LocalRead("k1"), A.LocalRead("o9"))
        ),
    )
    call = A.Call("m0", (A.IntLit(1),), (("k1", A.IntLit(2)), ("extra", A.IntLit(9))))
    out = A.Puts((A.StrInterp((call,)),))
    prog = A.Program((A.MethodDef("m0", params, body), out))
    assert runner.run(render_program(prog)).stdout == "[1, 1, 2, {extra: 9}]\n"


def test_fwd_forwarding_smoke():
    from difftest.tiers.tier1 import ast as A

    # def sink(*r1, **o9); [r1, o9]; end ; def m1(...); sink(...); end
    # puts(m1(1, 2, k: 3))  →  [[1, 2], {:k=>3}]
    sink = A.MethodDef(
        "sink",
        (A.PRest("r1"), A.PKwRest("o9")),
        (A.ArrayLit((A.LocalRead("r1"), A.LocalRead("o9"))),),
    )
    fwd = A.MethodDef("m1", (A.PFwd(),), (A.Call("sink", (A.FwdArg(),)),))
    call = A.Call("m1", (A.IntLit(1), A.IntLit(2)), (("k", A.IntLit(3)),))
    prog = A.Program((sink, fwd, A.Puts((A.StrInterp((call,)),))))
    assert runner.run(render_program(prog)).stdout == "[[1, 2], {k: 3}]\n"


def test_destructuring_block_smoke():
    from difftest.tiers.tier1 import ast as A

    # [[1, 2], [3, 4]].map { |(da, db)| da + db }  →  [3, 7]
    block = A.Block(
        (A.PDestr(("da", "db")),), (A.BinOp("+", A.LocalRead("da"), A.LocalRead("db")),)
    )
    recv = A.ArrayLit((A.ArrayLit((A.IntLit(1), A.IntLit(2))), A.ArrayLit((A.IntLit(3), A.IntLit(4)))))
    prog = A.Program((A.Puts((A.StrInterp((A.BlockCall(recv, "map", (), block),)),)),))
    assert runner.run(render_program(prog)).stdout == "[3, 7]\n"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
