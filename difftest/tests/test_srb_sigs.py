"""The contract of `find_sorbet()`, the single definition of where Sorbet is.

`scripts/check-prereqs.sh` and the corpus pipeline both ask this function, so a
change that makes it honor a stale `$SORBET`, or that drops the gem lookup, must
fail here rather than show up as a silently different gate (issue #41).

No toolchain: `subprocess.run` is replaced, so the test runs anywhere.
"""

import importlib.util
import stat
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
SRB_SIGS = ROOT / "books" / "scripts" / "srb_sigs.py"


def _load_srb_sigs():
    spec = importlib.util.spec_from_file_location("srb_sigs", SRB_SIGS)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


srb_sigs = _load_srb_sigs()


def _executable(path: Path) -> Path:
    path.write_text("#!/bin/sh\nexit 0\n")
    path.chmod(path.stat().st_mode | stat.S_IXUSR)
    return path


def _gem_probe(binary: Path):
    def run(*_args, **_kwargs):
        return subprocess.CompletedProcess([], 0, stdout=str(binary), stderr="")

    return run


def test_executable_sorbet_override_wins(monkeypatch, tmp_path):
    fake = _executable(tmp_path / "sorbet")
    monkeypatch.setenv("SORBET", str(fake))
    assert srb_sigs.find_sorbet() == str(fake)


def test_missing_sorbet_override_falls_through(monkeypatch, tmp_path):
    gem = _executable(tmp_path / "gem-sorbet")
    monkeypatch.setenv("SORBET", str(tmp_path / "missing"))
    monkeypatch.setattr(srb_sigs.subprocess, "run", _gem_probe(gem))
    assert srb_sigs.find_sorbet() == str(gem)


def test_non_executable_sorbet_override_falls_through(monkeypatch, tmp_path):
    override = tmp_path / "not-executable"
    override.write_text("")
    gem = _executable(tmp_path / "gem-sorbet")
    monkeypatch.setenv("SORBET", str(override))
    monkeypatch.setattr(srb_sigs.subprocess, "run", _gem_probe(gem))
    assert srb_sigs.find_sorbet() == str(gem)


def test_gem_lookup_uses_the_active_ruby(monkeypatch, tmp_path):
    gem = _executable(tmp_path / "gem-sorbet")
    calls = []

    def run(argv, *_args, **_kwargs):
        calls.append(argv)
        return subprocess.CompletedProcess([], 0, stdout=str(gem), stderr="")

    monkeypatch.delenv("SORBET", raising=False)
    monkeypatch.setenv("RUBY", "/the/ruby")
    monkeypatch.setattr(srb_sigs.subprocess, "run", run)
    assert srb_sigs.find_sorbet() == str(gem)
    assert calls[0][0] == "/the/ruby"


def test_executable_srb_on_path_is_last(monkeypatch, tmp_path):
    srb = _executable(tmp_path / "srb")

    def run(*_args, **_kwargs):
        raise OSError

    monkeypatch.delenv("SORBET", raising=False)
    monkeypatch.setenv("PATH", str(tmp_path))
    monkeypatch.setattr(srb_sigs.subprocess, "run", run)
    assert srb_sigs.find_sorbet() == str(srb)


def test_nothing_found_still_names_srb(monkeypatch, tmp_path):
    def run(*_args, **_kwargs):
        raise OSError

    monkeypatch.delenv("SORBET", raising=False)
    monkeypatch.setenv("PATH", str(tmp_path))
    monkeypatch.setattr(srb_sigs.subprocess, "run", run)
    assert srb_sigs.find_sorbet() == "srb"


def test_print_sorbet_needs_no_file(monkeypatch, capsys):
    monkeypatch.setattr(srb_sigs, "find_sorbet", lambda: "/path/to/sorbet")
    assert srb_sigs.main(["--print-sorbet"]) == 0
    assert capsys.readouterr().out.strip() == "/path/to/sorbet"


def test_file_is_required_without_print_sorbet():
    with pytest.raises(SystemExit):
        srb_sigs.main([])
