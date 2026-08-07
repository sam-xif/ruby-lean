"""Invariants of the type-directed generator.

No toolchain. These guard the properties the siggen report's numbers rest on —
most importantly that the generator is **independent of the checker it tests**.
"""

import inspect
import random
import re

from difftest import sig_gen
from difftest.sig_gen import (
    ATOMS,
    BOOL,
    INT,
    MUTATIONS,
    OBJ,
    STR,
    build,
    incompatible,
    nilable,
    sample,
    supertypes,
)


# --------------------------------------------------------------------------
# Independence from the artifact under test
# --------------------------------------------------------------------------


def _code_only(obj) -> str:
    """Source of `obj` with comments and string literals removed, so prose that
    *discusses* the checker does not read as code that *calls* it."""
    import io
    import tokenize

    src = inspect.getsource(obj)
    out = []
    for tok in tokenize.generate_tokens(io.StringIO(src).readline):
        if tok.type in (tokenize.COMMENT, tokenize.STRING):
            continue
        out.append(tok.string)
    return " ".join(out)


# The generation path. `run_siggen` is deliberately excluded: it *records* the
# checker's verdict for the report, which is not the same as letting the checker
# decide what counts as well-typed.
GENERATION_PATH = (
    sig_gen.Ty, sig_gen.Gen, sig_gen.Method, sig_gen.Program,
    sig_gen.build, sig_gen._mutate, sig_gen.sample,
    sig_gen.incompatible, sig_gen.supertypes, sig_gen._ops_returning,
)


def test_generation_path_does_not_consult_the_checker():
    """If "well-typed" were defined by the checker under test, agreement would
    be guaranteed by construction and the harness would measure nothing. The
    generation path's only oracle is srb."""
    for obj in GENERATION_PATH:
        body = _code_only(obj)
        for forbidden in ("builtinSig", "StaticChecker", "rubycore", "check"):
            assert forbidden not in body, f"{obj.__name__} references {forbidden}"


def test_builtin_table_is_its_own():
    """A second, independent transcription of Sorbet's RBIs. It is allowed to
    disagree with `builtinSig` — Sorbet's `Integer#+` is wider — and that
    disagreement is a finding, so the tables must not be shared."""
    assert ("+", [INT], INT) in sig_gen.BUILTINS["Integer"]
    assert ("length", [], INT) in sig_gen.BUILTINS["String"]


# --------------------------------------------------------------------------
# The type algebra
# --------------------------------------------------------------------------


def test_object_has_no_incompatible_type():
    """Nothing is ill-typed against `Object`, so those sites must be skipped
    rather than mutated — otherwise the generator emits a program it wrongly
    believes is broken."""
    assert incompatible(OBJ) is None


def test_incompatible_is_never_the_type_itself():
    for t in ATOMS + (nilable(INT), sig_gen.anyof(INT, STR)):
        bad = incompatible(t)
        if bad is None:
            continue
        assert bad != t
        if t.head == "T.any":
            assert all(bad != a for a in t.args)
        if t.head == "T.nilable":
            assert bad != t.args[0]


def test_supertypes_include_object_and_nilable():
    for t in ATOMS:
        sups = supertypes(t)
        assert OBJ in sups
        assert nilable(t) in sups
        assert t not in sups


def test_render_round_trips_nesting():
    assert nilable(INT).render() == "T.nilable(Integer)"
    assert sig_gen.anyof(INT, STR).render() == "T.any(Integer, String)"
    assert BOOL.render() == "T::Boolean"


# --------------------------------------------------------------------------
# Program shape
# --------------------------------------------------------------------------


def test_seed_determines_the_program():
    assert [s.source for s in sample(10, 5)] == [s.source for s in sample(10, 5)]
    assert [s.source for s in sample(10, 5)] != [s.source for s in sample(10, 6)]


def test_preamble_is_present():
    for s in sample(12, 1):
        lines = s.source.splitlines()
        assert lines[0] == "# typed: true"
        assert 'require "sorbet-runtime"' in lines
        assert "extend T::Sig" in lines


def test_method_names_are_prefixed_for_batch_safety():
    """Toplevel `def`s land on Object, so a batched `srb --dir` run would have
    every program redefining `m0`. Uniqueness is what keeps batching legal."""
    seen = set()
    for s in sample(20, 2):
        names = re.findall(r"^def (\w+)", s.source, re.M)
        assert names, s.source
        for n in names:
            assert n.startswith(s.name + "_"), n
            assert n not in seen, f"duplicate method name {n} across the batch"
            seen.add(n)


def test_strict_sigil_sigs_every_method():
    """At `# typed: strict` an unsig'd method draws 7017, which would reject the
    program for a reason unrelated to types."""
    for s in sample(16, 4, sigil="strict", coverage=0.3):
        n_defs = len(re.findall(r"^def ", s.source, re.M))
        n_sigs = len(re.findall(r"^sig ", s.source, re.M))
        assert n_defs == n_sigs, s.source


def test_partial_coverage_actually_leaves_methods_unsigged():
    rng = random.Random(0)
    unsigged = 0
    for _ in range(40):
        p = build(rng, sigil="true", coverage=0.5)
        unsigged += sum(1 for m in p.methods if not m.sigged)
    assert unsigged > 0


# --------------------------------------------------------------------------
# Mutation
# --------------------------------------------------------------------------


def test_wellformed_programs_carry_no_mutation():
    for s in sample(20, 7):
        if s.intent == "wellformed":
            assert s.mutation is None


def test_illtyped_programs_always_record_one_mutation():
    """Exactly one thing broken per program, so a program srb accepts anyway is
    a clean candidate finding rather than a pile of confounded breakages."""
    for s in sample(30, 8):
        if s.intent == "illtyped":
            assert s.mutation in MUTATIONS, s.mutation


def test_intents_alternate_evenly():
    ss = sample(20, 9)
    assert sum(1 for s in ss if s.intent == "wellformed") == 10
    assert sum(1 for s in ss if s.intent == "illtyped") == 10


def test_every_mutation_kind_is_reachable():
    """A kind that never fires would silently shrink the injected population."""
    kinds = {s.mutation for s in sample(120, 11) if s.intent == "illtyped"}
    assert set(MUTATIONS) <= kinds, set(MUTATIONS) - kinds


# --------------------------------------------------------------------------
# The `sample` subcommand (display only — needs no toolchain)
# --------------------------------------------------------------------------


def _sample_args(**kw):
    from argparse import Namespace

    base = dict(kind="siggen", count=None, seed=0, intent=None,
                sigil="true", coverage=1.0, loose=0.25)
    base.update(kw)
    return Namespace(**base)


def test_sample_defaults_to_a_readable_handful(capsys):
    from difftest.cli import cmd_checker_sample

    assert cmd_checker_sample(_sample_args()) == 0
    out = capsys.readouterr().out
    assert out.count("# ---- ") == 4  # not the 60 the checking arms default to


def test_sample_intent_filter_still_yields_count_programs(capsys):
    """Filtering must over-generate, not return however many happen to land in
    the slice — otherwise `--count 3 --intent illtyped` silently shows fewer."""
    from difftest.cli import cmd_checker_sample

    assert cmd_checker_sample(_sample_args(count=3, intent="illtyped")) == 0
    out = capsys.readouterr().out
    assert out.count("# ---- ") == 3
    assert out.count("intent=illtyped") == 3
    assert "mutation=" in out


def test_sample_rejects_an_unknown_intent_and_lists_the_real_ones(capsys):
    from difftest.cli import cmd_checker_sample

    assert cmd_checker_sample(_sample_args(intent="nope")) == 2
    err = capsys.readouterr().err
    assert "wellformed" in err and "illtyped" in err


def test_sample_refuses_the_incoherent_knob_combination(capsys):
    from difftest.cli import cmd_checker_sample

    assert cmd_checker_sample(_sample_args(sigil="strict", coverage=0.5)) == 2
    assert "7017" in capsys.readouterr().err


def test_sample_can_draw_from_the_fragment_fuzzer(capsys):
    from difftest.cli import cmd_checker_sample

    assert cmd_checker_sample(_sample_args(kind="fuzz", count=2)) == 0
    out = capsys.readouterr().out
    # the plain-Ruby fragment carries no annotations at all
    assert "sorbet-runtime" not in out and "sig {" not in out
