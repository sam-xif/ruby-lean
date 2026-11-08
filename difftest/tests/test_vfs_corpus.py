"""The VFS corpus (issue #43): the symbolic filesystem against CRuby.

The model's files are heap data, so a case declares a versioned fixture in its
sidecar and the control materializes the same tree before each run. These tests
run the corpus with the Lean SUT (skipped without a built `rubycore`) and check
that the fixture machinery restores the host's files.
"""

from pathlib import Path

import pytest
from difftest.compare import Verdict
from difftest.control import CRubyRunner
from difftest.runner import run_case
from difftest.sources import load_vfs_corpus
from difftest.sut import LeanSUT
from difftest.vfs import VFS_FIXTURES, UnknownVfsFixture, fixture_tree, materialized
from marks import requires_rubycore

EXPECTED = {
    "agree": Verdict.AGREE,
    "sut_unsupported": Verdict.SUT_UNSUPPORTED,
}


def test_every_case_declares_a_known_fixture():
    cases = load_vfs_corpus()
    assert cases
    for case in cases:
        assert case.provenance["vfs"] in VFS_FIXTURES, case.id


def test_unknown_fixture_is_rejected_by_the_loader(tmp_path):
    (tmp_path / "bad.rb").write_text('puts File.read("/tmp/readme.txt")\n')
    (tmp_path / "bad.json").write_text('{"vfs": "no-such-fixture"}\n')
    with pytest.raises(UnknownVfsFixture, match="no-such-fixture"):
        load_vfs_corpus(tmp_path)


def test_no_fixture_is_a_noop():
    with materialized(None):
        pass


def test_fixture_tree_rejects_an_unknown_name():
    with pytest.raises(UnknownVfsFixture, match="step1"):
        fixture_tree("no-such-fixture")


def test_existing_files_are_restored_and_created_files_removed(tmp_path, monkeypatch):
    existing = tmp_path / "existing.txt"
    existing.write_text("before\n")
    fresh = tmp_path / "fresh.txt"
    monkeypatch.setitem(
        VFS_FIXTURES, "test-restore", {str(existing): "during\n", str(fresh): "new\n"}
    )

    with materialized("test-restore"):
        assert existing.read_text() == "during\n"
        existing.write_text("mutated by program\n")
        assert fresh.read_text() == "new\n"

    assert existing.read_text() == "before\n"
    assert not fresh.exists()


def test_cleanup_keeps_directories_the_program_wrote_into(tmp_path, monkeypatch):
    root = tmp_path / "tree"
    monkeypatch.setitem(VFS_FIXTURES, "test-kept-dir", {str(root / "sub" / "data.txt"): "x\n"})

    with materialized("test-kept-dir"):
        (root / "sub" / "output.txt").write_text("program output\n")

    assert (root / "sub" / "output.txt").read_text() == "program output\n"
    assert not (root / "sub" / "data.txt").exists()


@requires_rubycore
def test_vfs_corpus_matches_cruby():
    cases = load_vfs_corpus()
    control = CRubyRunner()
    sut = LeanSUT()
    failures = []
    for case in cases:
        result = run_case(case, control, sut)
        expected = EXPECTED[case.provenance.get("expect", "agree")]
        if result.verdict is not expected:
            failures.append(f"{case.id}: {result.verdict.value} ({result.reason})")
    assert not failures, "VFS corpus did not meet its declarations:\n" + "\n".join(failures)


def test_the_corpus_covers_each_step_one_operation():
    sources = "\n".join(case.source for case in load_vfs_corpus())
    for operation in (
        "File.read",
        "File.write",
        "File.exist?",
        "File.file?",
        "File.directory?",
        "File.size",
        "Dir.exist?",
    ):
        assert operation in sources, operation


def test_fixture_paths_are_absolute():
    for tree in VFS_FIXTURES.values():
        for path in tree:
            assert Path(path).is_absolute(), path
