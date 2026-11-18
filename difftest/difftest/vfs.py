"""The symbolic filesystem fixture, materialized so CRuby sees it too.

The model has no ambient filesystem: its files are boot-heap data
(`ruby-lean/RubyCore/Heap.lean` §Virtual filesystem, issue #7 step 1). A program
that reads `/tmp/readme.txt` gets the fixture's bytes on the model side and
nothing at all under CRuby, so a filesystem program can only be compared when
the same tree exists at the same paths for the control.

A case declares the fixture it runs against in its sidecar (`{"vfs": "v1"}`);
`runner.run_case` then materializes that tree for the duration of the case and
restores it afterwards. Every CRuby run resets the tree first, so a program that
writes sees the same starting state on every run — including the control's
determinism double-run, which would otherwise fail as "nondeterministic".

The paths are absolute because the model's `VFS.resolve` refuses a relative path
(a relative path is outside the fragment), so the fixture cannot be redirected
into a temporary directory the way `CRubyRunner` redirects the program's working
directory. The fixture owns `/tmp/readme.txt` and `/tmp/vfsdata/`; applying it
refuses if either already exists, so nothing of the user's is ever overwritten,
and restoring it removes everything it created.

`FIXTURES` is the same tree `initHeap` builds. Keep the two in step: the comment
on each entry names where the model defines it.
"""

from __future__ import annotations

import shutil
from dataclasses import dataclass, field
from pathlib import Path


class VfsError(Exception):
    """A fixture cannot be used: unknown name, or its paths are occupied."""


@dataclass(frozen=True)
class Fixture:
    """A named directory tree, with paths relative to the filesystem root.

    `dirs` is written children-last (parents before children), which is the
    order `_materialize` creates them in; `restore` walks it backwards.
    """

    name: str
    dirs: tuple[str, ...]
    files: tuple[tuple[str, str], ...]

    def paths(self) -> tuple[str, ...]:
        return (*self.dirs, *(rel for rel, _ in self.files))


# `v1`: the step-1 boot fixture. `dirs`/`files` mirror `Boot.initHeap`'s
# `VFS` allocations: `/tmp` holds `readme.txt` (`hello\n`) and `vfsdata/`, and
# `vfsdata/` holds `nums.txt` (`1\n2\n3\n`). `/tmp` itself is the mount point:
# it is created if absent and never removed if it was there already.
V1 = Fixture(
    name="v1",
    dirs=("tmp/vfsdata",),
    files=(
        ("tmp/readme.txt", "hello\n"),
        ("tmp/vfsdata/nums.txt", "1\n2\n3\n"),
    ),
)

FIXTURES = {fixture.name: fixture for fixture in (V1,)}

MOUNT = "tmp"

#: The directory the fixture's absolute paths are resolved against. `/` in
#: production; a unit test points it at a temporary directory so that it never
#: touches the machine's `/tmp`.
ROOT = Path("/")


def fixture_for(name: str | None) -> Fixture | None:
    """The fixture a case's sidecar names, or `None` for a case that has none."""
    if name is None:
        return None
    try:
        return FIXTURES[name]
    except KeyError:
        known = ", ".join(sorted(FIXTURES)) or "none"
        raise VfsError(f"unknown vfs fixture {name!r} (known: {known})") from None


@dataclass
class Materialized:
    """A fixture applied to a real filesystem root.

    Constructing one materializes the tree; `reset` restores it and
    materializes it again (a fresh tree for the next run); `restore` removes
    everything it created. Both are idempotent.
    """

    fixture: Fixture
    root: Path = Path("/")
    _created_mount: bool = field(default=False, init=False, repr=False)

    def __post_init__(self) -> None:
        self.root = Path(self.root)
        self._created_mount = not (self.root / MOUNT).exists()
        self._materialize()

    def _materialize(self) -> None:
        occupied = [rel for rel in self.fixture.paths() if self._exists(self.root / rel)]
        if occupied:
            raise VfsError(
                f"the {self.fixture.name} fixture cannot be materialized: "
                f"{', '.join(str(self.root / rel) for rel in occupied)} already exists. "
                "Move it aside; the fixture is restored, never merged."
            )
        try:
            (self.root / MOUNT).mkdir(parents=True, exist_ok=True)
            for rel in self.fixture.dirs:
                (self.root / rel).mkdir(parents=True)
            for rel, text in self.fixture.files:
                (self.root / rel).write_bytes(text.encode("utf-8"))
        except OSError as e:
            self.restore()
            raise VfsError(f"the {self.fixture.name} fixture could not be written: {e}") from e

    def reset(self) -> None:
        """Put the tree back to its starting state (and back on disk, if restored)."""
        self.restore()
        self._created_mount = not (self.root / MOUNT).exists()
        self._materialize()

    def restore(self) -> None:
        """Remove everything the fixture created. Safe to call more than once."""
        for rel, _ in reversed(self.fixture.files):
            path = self.root / rel
            if path.is_symlink() or path.is_file():
                path.unlink()
            elif path.is_dir():
                shutil.rmtree(path, ignore_errors=True)
        # Children-last in `dirs`, so reversing removes a child before its parent.
        for rel in reversed(self.fixture.dirs):
            shutil.rmtree(self.root / rel, ignore_errors=True)
        if self._created_mount:
            mount = self.root / MOUNT
            # A program may have created files in the mount itself (`/tmp`); an
            # `rmdir` that cannot remove it is not an error — the mount existed
            # only because the fixture made it.
            try:
                mount.rmdir()
            except OSError:
                pass
            self._created_mount = False

    @staticmethod
    def _exists(path: Path) -> bool:
        return path.exists() or path.is_symlink()
