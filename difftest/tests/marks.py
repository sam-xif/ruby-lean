"""Shared pytest marks for tests that need an optional toolchain."""

import pytest
from difftest.sut import LeanSUT

# `make difftest-test` builds the model and sets DIFFTEST_NO_SKIPS=1, so a
# missing binary is a failure there. Bare `uv run pytest` may not have it.
requires_rubycore = pytest.mark.skipif(
    not LeanSUT().lean_bin.exists(),
    reason="Lean rubycore binary not built",
)
