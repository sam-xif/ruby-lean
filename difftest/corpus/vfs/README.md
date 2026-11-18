# The filesystem corpus

Programs that exercise the model's filesystem: path resolution, the `File`
singleton operations of issue #7 step 1, and the descriptor operations of the
later steps. Each `.rb` has a `.json` sidecar naming the fixture it runs
against:

```json
{"vfs": "v1"}
```

```sh
cd difftest && uv run difftest run --tier vfs --sut lean
```

## Why it exists

The model's filesystem is *initial heap data*, a small tree allocated at boot
(`ruby-lean/RubyCore/Heap.lean` §Virtual filesystem), never the host's. Under
CRuby the same program therefore sees whatever the host has at those paths, so
before this corpus existed nothing compared the two at all and the whole surface
was validated by hand (issue #43; the first defect this would have caught is the
trailing-slash bug in PR #42).

`runner.run_case` materializes the fixture named by the sidecar — the tree
`difftest/vfs.py` describes — for the duration of the case, resets it before
every CRuby run, and removes it afterwards. Nothing of the user's is touched:
materializing refuses if a fixture path already exists.

## What the verdicts mean here

The model's filesystem is built one step at a time, so a **gate**
(`sut_unsupported`) is expected for a step that has not landed, and it is
printed as a coverage measurement rather than a pass. What fails the tier is a
**disagreement** (a wrong answer), a control failure, or a harness error. A case
that gates today therefore keeps working as a ratchet: when the step lands, the
same case is compared, and a wrong implementation turns it red.

## Writing a case

- Only touch the fixture's own paths (`/tmp/readme.txt`, `/tmp/vfsdata/` and
  their files). Anything else would be host state the model does not have, and
  the control would leave it behind.
- Keep the program deterministic and free of ambient facts (clocks, `$$`,
  permissions): the engine runs the control twice and rejects a program whose
  two runs differ.
- Do not add a case that *documents* a known wrong answer. A disagreement fails;
  file the bug and add the case with the fix.
