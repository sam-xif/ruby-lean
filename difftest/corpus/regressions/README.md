# The regressions corpus

Minimized reproducers of disagreements, one `.rb` per case with a `.json` sidecar.
Written **automatically** by `campaign.py` whenever a generative campaign shrinks a
disagreement; run by `difftest run --tier regressions`.

```sh
uv run difftest run --tier regressions --sut lean
```

## Why it exists

A generated-program campaign is randomized, so a defect it finds once may not be
found again by the next run. Every disagreement is therefore shrunk and saved
here, and this tier runs every case, every time, without sampling.
`make conformance` runs it on every build.

## Status, and the two ways this goes red

Every case declares a status in its sidecar. The tier checks the observed verdict
against it, so the corpus ratchets in **both** directions:

| status | expected | if it does the other thing |
|---|---|---|
| `open` | DISAGREE | `unexpectedly_fixed` — **fails**: someone fixed it, so the sidecar is now a lie |
| `fixed` | AGREE | `regressed` — **fails**: a defect has been reintroduced |

There is no `wontfix`: a case here either reproduces a live defect or guards a dead
one. An unknown status is a hard error, not a silent skip.

Two outcomes are neither pass nor fail, and are reported rather than hidden:

* `gated` — the SUT now *refuses* the program, so it no longer pins anything. **A
  gate is not a fix**; leave such a case `open`. If the gate is ever closed the
  case starts testing again on its own.
* `unusable` — the control could not run it (parse error, timeout,
  nondeterminism).

A `still_open` case disagrees **by design** and does not redden the run — otherwise
the corpus could not hold a known defect at all. The consequence to remember when
reading a report from this tier: the verdict table at the top will show
`disagree: N`, and the section below it is what the exit code is computed from.

## Filing by hand

Drop in `<name>.rb` and `<name>.json`. Status defaults to `open` when the sidecar
is missing, which is correct for a freshly found defect and wrong for a guard — so
write the sidecar for a guard. A re-filed case **never** has its status
overwritten by the machine: the status is a human judgement.

## The sidecar

```json
{
  "status": "open",
  "filed_by": "difftest campaign (automatic)",
  "arm": "tier1.5",
  "seed": null,
  "case_id": "tier1.5-00930",
  "diff": "stdout: '10\n5\n' vs '10\n' | exception: (...) vs (...)",
  "control": { "stdout": "…" },
  "sut": { "stdout": "…" },
  "note": "what this was filed for, in prose"
}
```

`diff`, `control` and `sut` are recorded at filing time so a reader does not have
to re-derive the defect from the program.
