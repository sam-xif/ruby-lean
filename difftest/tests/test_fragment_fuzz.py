"""Structural properties of the fragment generator.

No toolchain: these check that the *generator* upholds the invariants the fuzz
report's numbers depend on. If `injected-literal` ever emitted a local-rooted
receiver, `reject_recall` would silently measure something else.
"""

import random
import re

from difftest.fragment_fuzz import (
    BAD_OPERANDS,
    INTENTS,
    generate,
    sample,
    srb_batch,
)


def gen(intent, seed=0):
    return generate(random.Random(seed), intent)


def test_seed_determines_the_program():
    """The report prints only count and seed, so reproduction depends on this."""
    assert [s.source for s in sample(12, 3)] == [s.source for s in sample(12, 3)]
    assert [s.source for s in sample(12, 3)] != [s.source for s in sample(12, 4)]


def test_every_program_carries_the_sigil():
    """Without `# typed: true` srb defaults to `false` and checks nothing, which
    would read as perfect agreement."""
    for s in sample(30, 11):
        assert s.source.startswith("# typed: true\n"), s.source


def test_intents_are_evenly_distributed():
    counts = {i: 0 for i in INTENTS}
    for s in sample(30, 5):
        counts[s.intent] += 1
    assert set(counts.values()) == {10}


def body(src):
    """Everything but the `# typed: true` sigil, which itself contains "true"."""
    return src.split("\n", 1)[1]


def test_wellformed_never_mentions_a_bad_operand():
    for i in range(40):
        src = body(gen("wellformed", i))
        for bad in BAD_OPERANDS:
            assert not re.search(rf"\b{bad}\b", src), src


def test_injected_literal_puts_the_bad_operand_under_a_literal_receiver():
    """The property `reject_recall` measures. The final line must be
    `<literal-rooted expr> <op> <bad>` with no local name in the receiver —
    otherwise `defTy` has no unconditional type and the honest verdict is
    `unknown`, not `reject`."""
    for i in range(40):
        src = gen("injected-literal", i)
        last = src.strip().splitlines()[-1]
        receiver, _, operand = last.rpartition(" ")
        receiver = receiver.rsplit(" ", 1)[0]
        assert operand in BAD_OPERANDS, last
        assert not re.search(r"\bv\d+\b", receiver), last


def test_injected_local_puts_the_bad_operand_under_a_local():
    """The complementary population: known incompleteness, kept measured."""
    for i in range(40):
        src = gen("injected-local", i)
        last = src.strip().splitlines()[-1]
        assert last.split()[-1] in BAD_OPERANDS, last
        assert re.match(r"^v\d+ [+\-*] ", last), last


def test_grammar_stays_inside_the_fragment():
    """`while` and comparisons are inexpressible until `Integer#<` is tabulated;
    if either appears here the docstring's account of the fragment is stale."""
    for s in sample(60, 2):
        assert "while" not in body(s.source)
        assert not re.search(r"[<>]|==", body(s.source)), s.source


def test_srb_batch_parses_codes_and_keys_by_program(monkeypatch):
    import subprocess as sp

    from difftest.fragment_fuzz import Sample

    samples = [Sample("g0000", "wellformed", "# typed: true\n1\n"),
               Sample("g0001", "injected-literal", "# typed: true\n1 + nil\n")]
    raw = (
        "./g0001.rb:2: Expected `Integer` but found `NilClass` for argument "
        "`arg0` https://srb.help/7002\n"
        "     2 |1 + nil\n"        # continuation line, must be ignored
        "./nope.rb:1: stray https://srb.help/9999\n"  # unknown file, ignored
    )

    def fake_run(*a, **k):
        return sp.CompletedProcess(a, 100, raw, "")

    monkeypatch.setattr(sp, "run", fake_run)
    out = srb_batch(samples, srb="/bin/true")
    assert out["g0000"] == []
    assert len(out["g0001"]) == 1
    assert out["g0001"][0].code == 7002
    assert out["g0001"][0].line == 2
