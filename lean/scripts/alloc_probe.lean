import RubyCore.Proof.Static.Locals

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
  if ok then
    IO.println "OK: an unallocated id has no type, so ValueTy implies in-bounds"
    return 0
  else
    IO.eprintln "FAIL: an out-of-bounds ObjId has a type — TypeAgree cannot survive an alloc"
    return 1
