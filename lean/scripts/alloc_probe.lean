import RubyCore.Proof.Static.Locals
import RubyCore.PreludeBoot

/-!
The producer rung's measurement: **what does an `alloc` actually break?**

`HANDOFF.md` (ninth session) named one blocker for giving the class type a
producer — `ancestors_congr` requires `objs.size` to be *equal*, so an allocating
step wants a fuel-monotonicity lemma. That is real, and it is not the first one.

Before the bound went into `plainRecv`, an **out-of-bounds `ObjId` already had a
type**: `Heap.get` answers out of bounds with `default`, whose `klass` is `0`,
whose `eigen` is `none` and whose payload is `.none`, so `plainRecv` was `true`
there and L141's `.ref` arm read `.cls "BasicObject"` off it. Allocating then
*changes that value's type* — id 40 goes from `.cls "BasicObject"` to `.cls
"String"` — which refutes the first clause of `TypeAgree` at the fresh id. So the
transport condition was **false for any allocating step**, independently of any
question about fuel.

This script is that measurement, kept as a check rather than as a paragraph:
it exits non-zero if an unallocated id ever gets a type again.

**L143 adds a second measurement, for the second bound; L147 strengthens it.**
Relativizing `TypeAgree` to `< h.objs.size` needs the *class* id in bounds too — the
`.ref` arm's type is `className h (classOf h (.ref o))`, and `className` also answers
out of bounds with a default — so `plainRecv` gained a clause about the object's
`klass`. L147 strengthened it from `< h.objs.size` to `(classPayload? klass).isSome`,
which **subsumes** the bound (`classPayload?` is `none` out of bounds) and is what
`EntryOk`'s class-indexed resolution clause needs at the use site.

That clause is a **refusal**, and a refusal has to be priced: this script counts
the objects of the **prelude-booted** heap it costs. The answer must be zero, and
if it ever is not, the fragment has silently stopped typing real objects rather
than pathological ones. `typeAgree_alloc` is the proof that the relativization
achieved what it was for; this is the check that it cost nothing.

    lake env lean --run scripts/alloc_probe.lean      # exit 0 iff no OOB id has a type
-/

open RubyCore RubyCore.Types RubyCore.Proof.Static

def main : IO UInt32 := do
  let h : Heap := Boot.initHeap
  let n := h.objs.size
  let (_, h') := h.alloc { klass := Boot.stringId, payload := .none }
  IO.println s!"objs.size before = {n}, after = {h'.objs.size}, fresh id = {n}"
  IO.println s!"plainRecv h (oob {n})   = {plainRecv h n}      (want false)"
  IO.println s!"valueTy? h (.ref {n})   = {repr (valueTy? h (.ref n))}   (want none)"
  IO.println s!"valueTy? h' (.ref {n})  = {repr (valueTy? h' (.ref n))}"
  IO.println s!"classOf  h (.ref {n})   = {classOf h (.ref n)} → after alloc {classOf h' (.ref n)}"
  -- The diagnosis, restated as the check: only the *bound* keeps `TypeAgree`'s
  -- first clause reachable at an allocating step. `classOf` still disagrees at
  -- the fresh id — that is why the transport has to be relativized to ids the
  -- old heap had, rather than proved unrelativized.
  let ok := plainRecv h n = false && (valueTy? h (.ref n)).isNone
  -- L143's clause as L147 strengthened it, priced at the heap the interpreter really
  -- starts from: how many **allocated** objects does *the object's class is a class*
  -- refuse? A real heap never points an object at a non-class, so the answer is zero
  -- — but that is a measurement, not an argument, and it is the one this clause
  -- could get wrong.
  let mut oobKlass := 0
  let mut plainCount := 0
  let mut bootedSize := 0
  match Prelude.boot with
  | .error e => IO.eprintln s!"prelude boot failed: {e}"; return 1
  | .ok mp =>
    let hb := mp.heap
    bootedSize := hb.objs.size
    for o in [0:hb.objs.size] do
      if !(hb.classPayload? (hb.get o).klass).isSome then oobKlass := oobKlass + 1
      if plainRecv hb o then plainCount := plainCount + 1
  IO.println s!"booted heap: {bootedSize} objects, {plainCount} plain receivers, \
{oobKlass} refused because their class is not a class object (want 0)"
  if ok && oobKlass == 0 then
    IO.println "OK: an unallocated id has no type, so ValueTy implies in-bounds; \
and no allocated object is refused for its class"
    return 0
  else
    IO.eprintln "FAIL: an out-of-bounds ObjId has a type, or a real object's class \
is not a class — TypeAgree cannot survive an alloc"
    return 1
