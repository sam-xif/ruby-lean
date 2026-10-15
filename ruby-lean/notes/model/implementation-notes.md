# Model implementation notes

Running record of non-obvious model changes, newest first. The plan this builds
toward is in [`marshal-require-gem-plan.md`](marshal-require-gem-plan.md).

## M1 (first slice): `require_relative` over the VFS

**What.** `require_relative` now resolves its argument against the running
file's directory in the symbolic filesystem and runs the pre-desugared body of
the file it names. It previously gated (`Require.lean` "require_relative needs
source-file resolution"). Plain `require` is unchanged (still the name-keyed
modeled standard libraries); `$LOAD_PATH`-based `require` over the VFS is the
next slice.

**The pre-desugared fixture (two-step, like the prelude).** Every `.rb` under
`prelude/vfs/` is mounted into the VFS as a regular file (its bytes) and also
desugared to a RubyCore `Expr`. The model never parses Ruby at run time — the
desugarer is the untrusted front end, as for the prelude features. Generation
mirrors `PreludeJson` → `Prelude`: `scripts/gen_vfs.rb` writes the bodies as JSON
plus the raw bytes and **pre-split path components** into
`Generated/VfsFixtureJson.lean`; then the `genvfs` executable (`GenVfs.lean`)
decodes the JSON with the model's own `Decode.program` and writes
`Generated/VfsFixture.lean` as RubyCore **terms**. Boot imports only the terms.

Why terms, and why pre-split components: `boot_ok` (`books/Books/Lib/Boot.lean`)
`kernel_rfl`s the whole booted heap, so everything the overlay touches must
reduce in the kernel. `Json.parse` (a `partial` def) and `String.splitOn` (well-
founded recursion) do **not** reduce — a body defined as "decode this string", or
a mount that splits paths at boot, would leave `boot_ok` stuck. So the decode
runs in `genvfs` (not at boot) and the path components are split in the generator
(`["lib", "greeting.rb"]`), leaving the boot overlay a pure fold over literals.
Because bytes and body come from the same source file in one `make gen`,
`File.read` of a library file and the body `require_relative` runs cannot drift.

**Mounting (boot overlay, not `initHeap`).** `Prelude.initWithPrelude` mounts the
fixture files onto the booted heap as ordinary heap writes — new `.file`/`.dir`
objects, entries appended to existing directories (`Boot.mountFiles`). This is
*not* in `Boot.initHeap` (the heap the metatheory reasons about): it is boot-time
initial data layered on top, matching issue #7's framing of the fixture tree as a
boot parameter. So `Boot.initHeap` and every id it pins are untouched, and the
step-1 VFS fixture block is not edited.

**Resolution reuses the step-1 walk.** A relative argument is joined onto the
source file's directory into an absolute path, then handed to the existing
absolute `VFS.resolve`. `.`/`..` need no new rule: `VFS.components`/`walk` already
resolve them against the tree. No VFS primitive changed.

**Caching by object identity.** `require_relative` keys the loaded-feature cache
on the file's canonical path (1:1 with its heap id), so any spelling of the same
file (`greeting`, `./greeting`, `greeting.rb`) loads once — CRuby keys realpaths.
Re-entry/retry ride the existing `requireK` continuation unchanged.

**Honest gates.** A path that does not resolve, or resolves to a file with no
modeled body, gates by name (CRuby would raise `LoadError`; the error classes are
issue #7 step 7). `require_relative` with no source file (e.g. from `eval`) gates
("cannot infer basepath").

**Proof repair.** Restructuring `callRequire` and adding `callRequireRelative`/
`runLibraryBody` broke two metatheory proofs, both repaired by giving the new
helpers the lemma the restructured caller needs:
- `Metatheory/Machine/NotDone.lean`: `runLibraryBody_notDone` and
  `callRequireRelative_notDone` (`@[ndLem]`), so `callRequire_notDone`'s
  `fun_cases <;> nd_walk` discharges the new branches.
- `Metatheory/Framing/RootFrameCalls.lean`: `runLibraryBody_frame` and
  `callRequireRelative_frame` (`@[rootFrameLem]`), plus `pushRootK_requireBodies`
  in `RootFramePrimitives.lean` for the new `Machine` field.

**Evidence.** Model vs CRuby 4.0.5, byte-for-byte, via `make feature-loading`
(three new `require_relative` cases alongside the existing `require` ones): load
with a transitive `require_relative` from inside a required file; caching (a
repeat and a transitively-already-loaded file both return `false`); a circular
pair where the in-progress file is seen as `false` mid-load; and the explicit
`.rb` / `./` spellings loading the same object once. Directly checked besides:
`File.read`/`File.exist?` of a mounted library file match CRuby (no
"requireable but `exist?` false" split), and the two gates above.
