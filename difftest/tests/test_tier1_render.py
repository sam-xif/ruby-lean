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


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
