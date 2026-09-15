import RubyCore.PreludeBoot
import RubyCore.Proof.AncestorsGrow

/-!
Item 3 of the producer's bill (L144), measured before it was proved — and the
measurement changed which clause got proved.

`ancestors` and `modAncestors` take fuel `h.objs.size + 1`, so `ancestors_congr`
needs the size to be **equal** — twice, both times as a fuel rewrite and nothing
else (`Proof/HeapFacts.lean`). An allocating step therefore had no ancestor
congruence, which is the blocker three consecutive sessions named.

## The route `HANDOFF.md` proposed is false, and this script is why we know

The proposal: *the superclass chain descends in `ObjId`* — a subclass is allocated
after its superclass — so the walk from `k` is at most `k + 1` steps, any fuel
`≥ k + 1` agrees, and F0's `heapOkB` can absorb the clause since it is decidable
at the boot heap. Decidable it is. True it is not: the boot heap's ids are **fixed
constants** while `Kernel`, `Numeric`, `Comparable` and `Enumerable` are prelude
Ruby allocated afterwards, so the smallest ids point at the largest. `Object`
includes `Kernel`; `Integer < Numeric`; `String` includes `Comparable`.

## What is true is saturation, and that is what `Proof/AncestorsGrow.lean` assumes

The fuel does not need the walk to be *short*, only **finished** before it runs
out: one more unit of fuel changes nothing. That is what `Saturated` says, what
`saturatedB` decides, and what `ancestors_congr_grow` takes as its hypothesis.
This script is its certificate — the same shape as F0's `heapok_probe.lean`, for
the same reason (the booted heap is built by `Lean.Json.parse`, which does not
kernel-reduce, and L94 bans `native_decide`).

It also measures the clause the **class**-allocating case will need and this rung
does not: no in-bounds object has an edge pointing out of bounds.

    lake env lean --run scripts/probes/ancestors_probe.lean   # exit 0 iff saturatedB, 0 OOB edges
-/

open RubyCore
open RubyCore.Interp
open RubyCore.Proof

structure Edge where
  kind : String
  from_ : ObjId
  to : ObjId

def main : IO UInt32 := do
  match Prelude.boot with
  | .error e => IO.eprintln s!"prelude boot failed: {e}"; return 1
  | .ok mp =>
    let h := mp.heap
    let n := h.objs.size
    IO.println s!"booted: {n} objects"
    let mut nonDescending : Array Edge := #[]
    let mut oob : Array Edge := #[]
    let mut classes := 0
    for k in [0:n] do
      match h.classPayload? k with
      | none => pure ()
      | some c =>
        classes := classes + 1
        let mut edges : Array Edge := #[]
        match c.superclass with
        | none => pure ()
        | some s => edges := edges.push ⟨"superclass", k, s⟩
        for i in c.includes do edges := edges.push ⟨"include", k, i⟩
        for p in c.prepends do edges := edges.push ⟨"prepend", k, p⟩
        for e in edges do
          if !(e.to < n) then oob := oob.push e
          if !(e.to < k) then nonDescending := nonDescending.push e
    IO.println s!"class/module objects: {classes}"
    -- (a) the clause `HANDOFF.md` proposed, refuted.
    IO.println s!"\nnon-descending edges (HANDOFF's proposed clause, want 0): {nonDescending.size}"
    for e in nonDescending do
      IO.println s!"  {e.kind}: {className h e.from_} ({e.from_}) → \
{className h e.to} ({e.to})"
    -- (b) the clause the class-allocating case will need, and which holds.
    IO.println s!"\nedges pointing out of bounds (≥ {n}), the clause `classDef` will \
need: {oob.size}"
    for e in oob do
      IO.println s!"  OOB {e.kind}: {className h e.from_} ({e.from_}) → {e.to}"
    -- (c) the clause `ancestors_congr_grow` actually assumes. Reported per-class
    -- first, so a failure names the class rather than printing `false`.
    let mut fuelSensitive := 0
    for k in [0:n] do
      if ancestors.go h k (n + 1) != ancestors.go h k n ||
         modAncestors.go h k (n + 1) != modAncestors.go h k n then
        fuelSensitive := fuelSensitive + 1
        IO.println s!"  fuel-sensitive at {className h k} ({k})"
    IO.println s!"\nSaturated: ids whose walk changes with one more unit of fuel: \
{fuelSensitive}"
    let sat := saturatedB h
    IO.println s!"saturatedB (prelude-booted): {sat}"
    return if sat && oob.isEmpty then 0 else 1
