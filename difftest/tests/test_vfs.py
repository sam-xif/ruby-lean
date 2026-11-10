"""The filesystem fixture: materialization, restoration, and the case hook."""

import json
from pathlib import Path

import pytest
from difftest.control import CRubyRunner
from difftest.runner import run_case
from difftest.sources import load_vfs_corpus
from difftest.testcase import TestCase as Case  # aliased: pytest collects *TestCase
from difftest.vfs import V1, Materialized, VfsError, fixture_for

from difftest import vfs


def test_materialize_builds_the_model_tree(tmp_path):
    Materialized(V1, root=tmp_path)
    assert (tmp_path / "tmp" / "readme.txt").read_bytes() == b"hello\n"
    assert (tmp_path / "tmp" / "vfsdata" / "nums.txt").read_bytes() == b"1\n2\n3\n"


def test_restore_removes_everything_it_created(tmp_path):
    applied = Materialized(V1, root=tmp_path)
    applied.restore()
    assert not (tmp_path / "tmp").exists()  # the mount went too: the fixture made it


def test_restore_keeps_a_mount_that_was_already_there(tmp_path):
    (tmp_path / "tmp").mkdir()
    applied = Materialized(V1, root=tmp_path)
    applied.restore()
    assert (tmp_path / "tmp").is_dir()
    assert list((tmp_path / "tmp").iterdir()) == []


def test_restore_removes_files_a_program_added(tmp_path):
    applied = Materialized(V1, root=tmp_path)
    (tmp_path / "tmp" / "vfsdata" / "extra.txt").write_text("stray")
    applied.restore()
    assert not (tmp_path / "tmp" / "vfsdata").exists()


def test_reset_puts_the_tree_back(tmp_path):
    applied = Materialized(V1, root=tmp_path)
    (tmp_path / "tmp" / "readme.txt").write_text("bye")
    (tmp_path / "tmp" / "vfsdata" / "nums.txt").unlink()
    applied.reset()
    assert (tmp_path / "tmp" / "readme.txt").read_text() == "hello\n"
    assert (tmp_path / "tmp" / "vfsdata" / "nums.txt").read_text() == "1\n2\n3\n"


def test_restore_is_idempotent(tmp_path):
    applied = Materialized(V1, root=tmp_path)
    applied.restore()
    applied.restore()
    applied.reset()
    assert (tmp_path / "tmp" / "readme.txt").read_text() == "hello\n"


def test_materialize_refuses_to_overwrite(tmp_path):
    (tmp_path / "tmp").mkdir()
    (tmp_path / "tmp" / "readme.txt").write_text("mine")
    with pytest.raises(VfsError, match="readme.txt"):
        Materialized(V1, root=tmp_path)
    # Nothing was created beside the path it refused to touch.
    assert not (tmp_path / "tmp" / "vfsdata").exists()


def test_materialize_refuses_a_symlink_at_a_fixture_path(tmp_path):
    (tmp_path / "tmp").mkdir()
    (tmp_path / "tmp" / "readme.txt").symlink_to(tmp_path / "elsewhere")
    with pytest.raises(VfsError, match="readme.txt"):
        Materialized(V1, root=tmp_path)


def test_an_unwritable_root_is_a_vfs_error(tmp_path):
    not_a_directory = tmp_path / "file"
    not_a_directory.write_text("")
    with pytest.raises(VfsError, match="could not be written"):
        Materialized(V1, root=not_a_directory)


def test_fixture_for_unknown_name_names_the_known_ones():
    with pytest.raises(VfsError, match="known: v1"):
        fixture_for("v2")
    assert fixture_for(None) is None
    assert fixture_for("v1") is V1


# ─── The case hook: the control sees the fixture, the SUT sees it unchanged ──


def _vfs_case(tmp_path, source):
    return Case(id="vfs/case.rb", source=source, tier=5, provenance={"vfs": "v1"})


class _RecordingSUT:
    """Answers a fixed stdout and records the tree it was shown."""

    name = "recording"

    def __init__(self, path: Path):
        self.path = path
        self.seen: list[str | None] = []

    def run(self, source):
        from difftest.observation import Observation

        self.seen.append(self.path.read_text() if self.path.exists() else None)
        return Observation(stdout="hello\n", result_repr="nil", exception=None)


def test_run_case_materializes_the_fixture_and_removes_it(tmp_path, monkeypatch):
    monkeypatch.setattr(vfs, "ROOT", tmp_path)
    readme = tmp_path / "tmp" / "readme.txt"
    case = _vfs_case(tmp_path, f'print File.read("{readme}")\n')
    sut = _RecordingSUT(readme)

    result = run_case(case, CRubyRunner(), sut)

    assert result.verdict.value == "agree"
    assert result.control_obs.stdout == "hello\n"
    assert not readme.exists()
    assert not (tmp_path / "tmp").exists()


def test_run_case_resets_the_fixture_before_the_sut(tmp_path, monkeypatch):
    monkeypatch.setattr(vfs, "ROOT", tmp_path)
    readme = tmp_path / "tmp" / "readme.txt"
    # The control writes (twice, once per determinism run); the SUT must still
    # be shown the fixture's own bytes, not the control's last write.
    case = _vfs_case(tmp_path, f'File.write("{readme}", "bye")\n')
    sut = _RecordingSUT(readme)

    run_case(case, CRubyRunner(), sut)

    assert sut.seen == ["hello\n"]


def test_run_case_reports_an_unknown_fixture_as_a_harness_error(tmp_path):
    case = Case(id="vfs/x.rb", source="p 1\n", tier=5, provenance={"vfs": "v9"})
    result = run_case(case, CRubyRunner(), _RecordingSUT(tmp_path / "unused"))
    assert result.verdict.value == "harness_error"
    assert "v9" in result.reason


def test_the_corpus_requires_a_fixture_in_every_sidecar(tmp_path):
    (tmp_path / "case.rb").write_text("p 1\n")
    (tmp_path / "case.json").write_text(json.dumps({"tier": 5}))
    with pytest.raises(VfsError, match="must name the fixture"):
        load_vfs_corpus(tmp_path)


def test_an_empty_corpus_is_an_error(tmp_path):
    with pytest.raises(VfsError, match="no filesystem cases under"):
        load_vfs_corpus(tmp_path)


def test_the_corpus_loads_with_its_fixture(tmp_path):
    (tmp_path / "case.rb").write_text("p 1\n")
    (tmp_path / "case.json").write_text(json.dumps({"vfs": "v1"}))
    (cases,) = load_vfs_corpus(tmp_path)
    assert cases.tier == 5
    assert cases.provenance["vfs"] == "v1"
