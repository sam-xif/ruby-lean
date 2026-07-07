"""Corpus sources: bootstraptest loading and the generic corpus loader."""

import json

import pytest

from difftest.sources import load_bootstraptest, load_corpus_cases


def _write_bootstraptest(tmp_path, n=3):
    manifest = []
    for i in range(n):
        name = f"test_case_{i:03d}.rb"
        (tmp_path / name).write_text(f'print "case{i}"\n')
        manifest.append(
            {"file": name, "source": "test_case.rb", "assert": "assert_equal", "expected": f"case{i}"}
        )
    (tmp_path / "manifest.json").write_text(json.dumps(manifest))
    return tmp_path


def test_load_bootstraptest(tmp_path):
    cases = load_bootstraptest(_write_bootstraptest(tmp_path))
    assert len(cases) == 3
    assert all(c.tier == 0 for c in cases)
    assert cases[0].id == "bootstraptest/test_case_000"
    assert cases[0].source == 'print "case0"\n'
    assert cases[0].provenance["suite"] == "bootstraptest"
    assert cases[0].provenance["expected"] == "case0"


def test_load_bootstraptest_without_manifest(tmp_path):
    (tmp_path / "test_x_001.rb").write_text("p 1\n")
    cases = load_bootstraptest(tmp_path)
    assert len(cases) == 1
    assert cases[0].provenance == {"suite": "bootstraptest", "file": "test_x_001.rb"}


def test_load_bootstraptest_missing_dir_mentions_harvest_recipe(tmp_path):
    with pytest.raises(FileNotFoundError, match="harvest_bootstraptest"):
        load_bootstraptest(tmp_path / "nope")


def test_load_bootstraptest_empty_dir_mentions_harvest_recipe(tmp_path):
    with pytest.raises(FileNotFoundError, match="harvest_bootstraptest"):
        load_bootstraptest(tmp_path)


def test_load_corpus_cases_reads_sidecar(tmp_path):
    (tmp_path / "cat").mkdir()
    (tmp_path / "cat" / "000.rb").write_text("p 1\n")
    (tmp_path / "cat" / "000.json").write_text(json.dumps({"tier": 3, "category": "cat"}))
    (tmp_path / "bare.rb").write_text("p 2\n")
    cases = load_corpus_cases(tmp_path)
    by_id = {c.id: c for c in cases}
    assert by_id["cat/000.rb"].tier == 3
    assert by_id["cat/000.rb"].provenance["category"] == "cat"
    assert by_id["bare.rb"].tier == -1
