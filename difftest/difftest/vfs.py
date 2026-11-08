"""Versioned virtual-filesystem fixtures for differential tests (issue #7, step 1).

The model's filesystem is initial heap data at absolute paths under `/tmp`
(`ruby-lean/RubyCore/Heap.lean` §The virtual filesystem fixture). CRuby has no
such tree, so a case that exercises the model's VFS declares a fixture by name;
the control materializes exactly those paths before each run and restores
whatever was there before. That keeps the fixture out of the tier-0 watermark
(issue #43): the corpus is advisory while the VFS surface is still growing.
"""

from __future__ import annotations

from collections.abc import Iterator
from contextlib import contextmanager
from pathlib import Path

# A fixture name is what a corpus sidecar writes in its `"vfs"` field. Bump a
# name only when the model's boot fixture changes; the two are coupled by hand.
VFS_FIXTURES: dict[str, dict[str, str]] = {
    "step1": {
        "/tmp/readme.txt": "hello\n",
        "/tmp/vfsdata/nums.txt": "1\n2\n3\n",
    },
}


class UnknownVfsFixture(ValueError):
    """A corpus sidecar names a fixture that no longer exists."""


def fixture_tree(name: str) -> dict[str, str]:
    """The files of fixture `name`. An unknown name is a configuration error,
    never an empty tree (which would silently weaken the case)."""
    try:
        return VFS_FIXTURES[name]
    except KeyError:
        known = ", ".join(sorted(VFS_FIXTURES))
        raise UnknownVfsFixture(f"unknown VFS fixture {name!r} (known: {known})") from None


@contextmanager
def materialized(name: str | None) -> Iterator[None]:
    """Materialize fixture `name` for the duration of the block.

    Files that already exist are restored afterwards, and files or directories
    this context created are removed. A file the *program* creates inside a
    fixture directory is left alone, so the directory is kept too.
    """
    if name is None:
        yield
        return

    saved: dict[Path, bytes] = {}
    created: list[Path] = []
    made_dirs: list[Path] = []
    for raw_path, contents in fixture_tree(name).items():
        path = Path(raw_path)
        missing: list[Path] = []
        parent = path.parent
        while not parent.exists():
            missing.append(parent)
            parent = parent.parent
        for directory in reversed(missing):
            directory.mkdir()
            made_dirs.append(directory)
        if path.exists():
            saved[path] = path.read_bytes()
        else:
            created.append(path)
        path.write_text(contents)
    try:
        yield
    finally:
        for path in created:
            path.unlink(missing_ok=True)
        for path, contents in saved.items():
            path.write_bytes(contents)
        for directory in reversed(made_dirs):
            try:
                directory.rmdir()
            except OSError:
                # The program put something there; that is its output, not ours.
                pass
