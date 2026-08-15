
## N47 — `--timeout` never reached the SUT

R1's last gate was a timeout, on a program the model runs in 13 s. `--timeout 180` did not help,
and the reason is that it never could: `make_sut` built every SUT with `CRubyRunner()` and no
argument, so the flag bounded the **control** and left the model on the runner's own 10 s default.

The failure mode is the bad kind. A model run slower than 10 s came back `sut_unsupported` —
reported as a **gate**, indistinguishable in `difftest gates`' histogram from a construct the model
refuses — and the one knob that looks like it should fix it did nothing. Any number this repo has
quoted as a gate count could have contained slow programs; the histogram's `sut timeout` row is the
only place it was visible, and only if someone read it.

`make_sut(kind, inject_bug, timeout)` now threads the flag through, and the default is unchanged at
10 s, so no existing figure moves unless a recipe passes `--timeout`. R1's is
`--timeout 120`; with it the tier is **106 agree, 0 disagree, 0 gated**.

The general lesson is the one already in `HANDOFF.md` about checks that pass by producing no
output: a flag that is accepted, does nothing, and produces a plausible-looking result is worse
than one that errors.
