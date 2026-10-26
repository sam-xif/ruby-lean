"""How the tools are found: CRuby (`ruby_path`), `srb` (`srb_path`) and the
Sorbet toolchain check (`require_toolchain`).

Which branch runs on its own depends on the machine (Homebrew or not, `srb` on
PATH or in the gem directory), so each is forced here. That also keeps the
suite's coverage the same on every machine, so the recorded baseline holds on
a laptop and in CI alike.
"""

import subprocess

import pytest

from difftest import control, sorbet

CACHED = [control.ruby_path, sorbet.srb_path, sorbet._gem_bin_dir, sorbet.sorbet_runtime_available]


@pytest.fixture(autouse=True)
def fresh_caches(monkeypatch):
    """Each lookup is cached for the process; start and end each test without."""
    monkeypatch.delenv("DIFFTEST_RUBY", raising=False)
    monkeypatch.delenv("DIFFTEST_SRB", raising=False)
    for f in CACHED:
        f.cache_clear()
    yield
    for f in CACHED:
        f.cache_clear()


def completed(stdout: str) -> subprocess.CompletedProcess:
    return subprocess.CompletedProcess(args=[], returncode=0, stdout=stdout, stderr="")


def missing(*_args, **_kwargs):
    raise FileNotFoundError("no such command")


def failing(*args, **_kwargs):
    raise subprocess.CalledProcessError(1, args[0])


# ── ruby_path ────────────────────────────────────────────────────────────────


def test_ruby_from_the_environment(monkeypatch):
    monkeypatch.setenv("DIFFTEST_RUBY", "/opt/ruby/bin/ruby")
    assert control.ruby_path() == "/opt/ruby/bin/ruby"


def test_ruby_from_homebrew(monkeypatch, tmp_path):
    (tmp_path / "bin").mkdir()
    (tmp_path / "bin" / "ruby").touch()
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: completed(f"{tmp_path}\n"))
    assert control.ruby_path() == str(tmp_path / "bin" / "ruby")


def test_ruby_when_homebrew_has_none(monkeypatch, tmp_path):
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: completed(f"{tmp_path}\n"))
    assert control.ruby_path() == "ruby"


@pytest.mark.parametrize("brew", [missing, failing])
def test_ruby_without_homebrew(monkeypatch, brew):
    monkeypatch.setattr(subprocess, "run", brew)
    assert control.ruby_path() == "ruby"


# ── srb_path ─────────────────────────────────────────────────────────────────


def test_srb_from_the_environment(monkeypatch):
    monkeypatch.setenv("DIFFTEST_SRB", "/opt/srb")
    assert sorbet.srb_path() == "/opt/srb"


def test_srb_on_path(monkeypatch):
    monkeypatch.setattr(sorbet.shutil, "which", lambda name: f"/usr/bin/{name}")
    assert sorbet.srb_path() == "/usr/bin/srb"


def test_srb_in_the_gem_directory(monkeypatch, tmp_path):
    (tmp_path / "bin").mkdir()
    (tmp_path / "bin" / "srb").touch()
    monkeypatch.setattr(sorbet.shutil, "which", lambda name: None)
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: completed(f"{tmp_path}\n"))
    assert sorbet.srb_path() == str(tmp_path / "bin" / "srb")


def test_srb_not_in_the_gem_directory(monkeypatch, tmp_path):
    (tmp_path / "bin").mkdir()
    monkeypatch.setattr(sorbet.shutil, "which", lambda name: None)
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: completed(f"{tmp_path}\n"))
    assert sorbet.srb_path() is None


def test_srb_when_the_gem_directory_has_no_bin(monkeypatch, tmp_path):
    monkeypatch.setattr(sorbet.shutil, "which", lambda name: None)
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: completed(f"{tmp_path}\n"))
    assert sorbet.srb_path() is None


@pytest.mark.parametrize("gem", [missing, failing])
def test_srb_without_gem(monkeypatch, gem):
    monkeypatch.setattr(sorbet.shutil, "which", lambda name: None)
    monkeypatch.setattr(subprocess, "run", gem)
    assert sorbet.srb_path() is None


# ── require_toolchain ────────────────────────────────────────────────────────


@pytest.mark.parametrize(
    ("srb", "runtime", "missing_parts"),
    [
        (None, True, ["srb"]),
        ("/usr/bin/srb", False, ["sorbet-runtime"]),
        (None, False, ["srb", "sorbet-runtime"]),
    ],
)
def test_require_toolchain_names_what_is_missing(monkeypatch, srb, runtime, missing_parts):
    monkeypatch.setattr(sorbet, "srb_path", lambda: srb)
    monkeypatch.setattr(sorbet, "sorbet_runtime_available", lambda: runtime)
    with pytest.raises(sorbet.SorbetUnavailable, match="missing") as err:
        sorbet.require_toolchain()
    for part in missing_parts:
        assert part in str(err.value)
    assert "gem install sorbet sorbet-runtime" in str(err.value)


def test_require_toolchain_passes_when_both_halves_exist(monkeypatch):
    monkeypatch.setattr(sorbet, "srb_path", lambda: "/usr/bin/srb")
    monkeypatch.setattr(sorbet, "sorbet_runtime_available", lambda: True)
    sorbet.require_toolchain()


def test_require_toolchain_checks_only_what_is_asked(monkeypatch):
    monkeypatch.setattr(sorbet, "srb_path", lambda: None)
    monkeypatch.setattr(sorbet, "sorbet_runtime_available", lambda: False)
    sorbet.require_toolchain(static=False, runtime=False)
