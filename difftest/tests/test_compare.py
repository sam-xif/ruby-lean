from difftest.compare import Verdict, compare
from difftest.observation import Observation


def test_agree():
    a = Observation("x\n", "1", None)
    assert compare(a, Observation("x\n", "1", None)) == (Verdict.AGREE, None)


def test_disagree_stdout():
    v, reason = compare(Observation("x\n", "1", None), Observation("y\n", "1", None))
    assert v == Verdict.DISAGREE
    assert "stdout" in reason


def test_agree_modulo_addresses():
    v, _ = compare(
        Observation("#<C:0x0000aaaa1111>\n", "nil", None),
        Observation("#<C:0x0000bbbb2222>\n", "nil", None),
    )
    assert v == Verdict.AGREE


def test_identical_exceptions_agree():
    e = ("RuntimeError", "boom")
    v, _ = compare(Observation("", None, e), Observation("", None, e))
    assert v == Verdict.AGREE
