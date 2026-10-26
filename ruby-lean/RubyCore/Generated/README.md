# Generated Lean sources (not committed)

Every `*.lean` file in this directory is a **build output**, regenerated from
its inputs and **not** checked into git (they are listed in the repository
`.gitignore`). Do not edit them by hand, and do not commit them.

`make gen` writes them, and every build target that compiles the model depends
on that step, so a normal `make lean` / `make books` / `make check` regenerates
them first. A bare `lake build` in a fresh checkout, with no prior `make`, will
not find them — run `make gen` (which needs Ruby) once first.

| File | Produced by | From |
|---|---|---|
| `PreludeJson.lean` | `scripts/gen_prelude.rb` | `prelude/prelude.rb`, `prelude/features/*.rb` (desugared) |
| `Prelude.lean` | `lake exe genprelude` | `PreludeJson.lean` (decoded to terms) |
| `CRubyNames.lean` | `scripts/gen_cruby_names.rb` | the CRuby oracle's constant/method names |
| `Unicode.lean` | `scripts/gen_unicode.rb` | the Unicode tables |
| `BootedHeap.lean` | `lake exe genbootedheap` | the model itself (the heap the prelude boot leaves) |

The CRuby-name and Unicode tables are snapshots of the oracle; regeneration is
hermetic with respect to the Ruby version the repo pins.

The require/require_relative fixture adds `VfsFixtureJson.lean` and
`VfsFixture.lean` (from `scripts/gen_vfs.rb` and `lake exe genvfs` over
`prelude/vfs/`) on the branches that carry it.
