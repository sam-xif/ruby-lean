#!/usr/bin/env python3
"""Drop the default gems the playground cannot reach, from a staged ruby.wasm tree.

Called by `build.sh` between staging and packing. Every removal is checked
against the staging root before it happens -- this walks a tree of paths built
from variables, and a shell `rm -rf $VAR/...` with an empty or surprising `$VAR`
is not a risk worth carrying for a few megabytes.

What is dropped is documentation, the REPL, test frameworks, build tools and
network protocol clients. What is kept is the whole of the rest of the standard
library, deliberately: the CRuby oracle runs *user* source, and a `require` that
works in their terminal should work in the page.
"""
from __future__ import annotations

import shutil
import sys
from pathlib import Path

# Default gems with no path from `export-json`, the strip chain, or a corpus
# program. Names are matched as `<name>-<version>` gem directories and as
# `<name>` / `<name>.rb` under the stdlib directory.
DROP = [
    "debug", "irb", "minitest", "net-ftp", "net-imap", "net-pop", "net-smtp",
    "observer", "power_assert", "prime", "rake", "rbs", "rdoc", "reline",
    "repl_type_completor", "rexml", "rss", "syntax_suggest", "test-unit",
    "typeprof",
]


def main(stage: str) -> None:
    root = Path(stage).resolve()
    if not (root / "usr/local/lib/ruby").is_dir():
        sys.exit(f"{root} does not look like a staged ruby.wasm tree")

    def rm(p: Path) -> int:
        """Remove `p`, but only if it is genuinely inside the staging root."""
        p = p.resolve()
        if not p.exists():
            return 0
        if root not in p.parents:
            sys.exit(f"refusing to remove {p}: outside {root}")
        if p == root:
            sys.exit(f"refusing to remove the staging root itself")
        size = sum(f.stat().st_size for f in p.rglob("*") if f.is_file()) \
            if p.is_dir() else p.stat().st_size
        shutil.rmtree(p) if p.is_dir() else p.unlink()
        return size

    lib = root / "usr/local/lib/ruby"
    stdlib = next(lib.glob("[0-9]*.[0-9]*.[0-9]*"), None)
    gems = next((lib / "gems").glob("[0-9]*.[0-9]*.[0-9]*"), None)
    if stdlib is None or gems is None:
        sys.exit(f"cannot find the versioned stdlib/gems directories under {lib}")

    freed = 0
    for name in DROP:
        for d in (gems / "gems").glob(f"{name}-*"):
            freed += rm(d)
        for s in (gems / "specifications/default").glob(f"{name}-*.gemspec"):
            freed += rm(s)
        freed += rm(stdlib / name)
        freed += rm(stdlib / f"{name}.rb")

    print(f"  pruned {len(DROP)} default gems, {freed / 1048576:.1f} MB")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit("usage: prune.py <staging-dir>")
    main(sys.argv[1])
