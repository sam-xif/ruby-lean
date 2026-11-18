"""The harvested corpus against the recorded conformance baseline (issue #39).

`ran` in `difftest/coverage-baseline.json` is the size of the corpus its numbers
were measured on, and the corpus is harvested on demand rather than stored here.
A harvest change — a new `RUBY_REF`, a changed skip list, a harvest interrupted
between writing the programs and writing `manifest.json` — therefore leaves the
baseline describing a corpus that is no longer there. Nothing saw that before
`make conformance` had built the model and replayed every program.

The check must speak up for each way the two can disagree, and stay quiet when
they agree; a check that cannot go red is worth no more than no check.
"""

import json

import pytest
from difftest.sources import bootstraptest_baseline_problems

BASELINE = {"ran": 3, "agree": 2, "sut_unsupported": 1, "not_compared": 0, "disagree": 0}


def _corpus(tmp_path, programs=3, manifest=None):
    """A harvested corpus: `programs` programs, and a manifest listing them."""
    names = [f"program_{i:03d}.rb" for i in range(programs)]
    for name in names:
        (tmp_path / name).write_text("puts 1\n")
    if manifest is None:
        manifest = names
    if manifest is not False:
        (tmp_path / "manifest.json").write_text(json.dumps([{"file": n} for n in manifest]))
    return tmp_path


def test_the_corpus_the_baseline_was_measured_on_has_no_problems(tmp_path):
    assert bootstraptest_baseline_problems(_corpus(tmp_path), BASELINE) == []


def test_a_program_count_the_baseline_does_not_record_is_reported(tmp_path):
    (problems,) = bootstraptest_baseline_problems(_corpus(tmp_path, programs=4), BASELINE)
    assert "4 programs" in problems
    assert "records 3" in problems


def test_a_program_with_no_manifest_entry_is_reported(tmp_path):
    """The harvest writes each program before it writes the manifest, so a harvest
    killed in between leaves a corpus no run replays and the baseline does not count."""
    corpus = _corpus(tmp_path, manifest=["program_000.rb", "program_001.rb"])
    (problems,) = bootstraptest_baseline_problems(corpus, BASELINE)
    assert "no manifest entry" in problems
    assert "program_002.rb" in problems


def test_a_manifest_entry_with_no_program_is_reported(tmp_path):
    """A harvest only adds files, so a program the suite no longer has stays behind
    unless the corpus directory is deleted first."""
    corpus = _corpus(
        tmp_path, programs=2, manifest=["program_000.rb", "program_001.rb", "removed_002.rb"]
    )
    baseline = {"ran": 2, "agree": 1, "sut_unsupported": 1, "not_compared": 0, "disagree": 0}
    (problems,) = bootstraptest_baseline_problems(corpus, baseline)
    assert "have no program" in problems
    assert "removed_002.rb" in problems


def test_without_a_manifest_only_the_count_is_checked(tmp_path):
    assert bootstraptest_baseline_problems(_corpus(tmp_path, manifest=False), BASELINE) == []


@pytest.mark.parametrize(
    "edit",
    [{"agree": 3}, {"sut_unsupported": 2}, {"not_compared": 1}, {"disagree": 1}],
    ids=["agree", "sut_unsupported", "not_compared", "disagree"],
)
def test_a_baseline_whose_counts_do_not_add_up_is_reported(tmp_path, edit):
    """`--save` computes these; a baseline that does not add up was edited by hand,
    and every number in it is then worth less than it looks."""
    baseline = {**BASELINE, **edit}
    (problems,) = bootstraptest_baseline_problems(_corpus(tmp_path), baseline)
    assert "add up to 4, not its ran 3" in problems
