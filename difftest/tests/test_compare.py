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


def test_sut_stack_overflow_is_unsupported():
    # Control ran to completion; the SUT overflowed the stack (its extra
    # frames-per-call tipped a deep-but-bounded recursion over). That is a
    # resource-limit artifact, not a wrong answer — inconclusive, like a SUT
    # timeout. (SUT-side dual of the N24 control gate.)
    control = Observation("done\n", "42", None)
    sut = Observation("done\n", None, ("SystemStackError", "stack level too deep"))
    v, reason = compare(control, sut)
    assert v == Verdict.SUT_UNSUPPORTED
    assert "stack overflow" in reason


def test_both_stack_overflow_agrees():
    # If both sides overflow with identical normalized output it is an AGREE
    # (in practice run_case excludes this as control_invalid before the SUT runs,
    # but compare() itself must not special-case a symmetric overflow as unsupported).
    e = ("SystemStackError", "stack level too deep")
    v, _ = compare(Observation("x\n", None, e), Observation("x\n", None, e))
    assert v == Verdict.AGREE
