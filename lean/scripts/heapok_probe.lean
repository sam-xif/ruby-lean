import RubyCore.PreludeBoot
import RubyCore.HeapCert

/-!
F0's certificate (`homebrew/widening-the-fragment.md` §3/§4): does the
**prelude-booted** heap satisfy the heap half of `Proof/StaticSoundness.Inv` —
`TableOk` (the three tabulated `Integer` builtins still resolve: live, public,
unshadowed, not `fromPrelude`) and `NoHook` (no `Module#method_added` on
`Object`)?

The verdict line is `heapOkB` itself, the same function
`Proof/PreludeInv.heapOkB_sound` turns into `HeapOk`, so what this script checks
is exactly what `check_sound_withPrelude` assumes. The per-clause lines below it
are diagnostics only — they exist so that a failure names itself instead of
printing `false`.

This is not a proof, and it is not meant to be: `Prelude.program` is
`Lean.Json.parse Prelude.json`, `Lean.Json.parse` does not kernel-reduce even on
the input `"1"`, and L94 bans the `native_decide` escape. Deciding the predicate
by *running* it is the honest remaining option, and
`Proof/PreludeInv.heapOk_boot` is the route that removes even this.

    lake env lean --run scripts/heapok_probe.lean      # exit 0 iff heapOkB
-/

open RubyCore
open RubyCore.Interp

/-- One `intResolvesB` clause per line, so a failure names itself. -/
def report (h : Heap) (mname bid : String) : IO Unit := do
  match lookup h (.int 0) mname with
  | none => IO.println s!"  {mname}: does not resolve at all"
  | some (owner, md) =>
    let shadow := crubyShadow h ((ancestors h Boot.integerId).takeWhile (· != owner)) mname
    IO.println s!"  {mname}: owner={className h owner} builtin={md.builtin} \
undefined={md.undefined} vis={repr md.visibility} fromPrelude={md.fromPrelude} \
shadow={shadow} → {intResolvesB h mname bid}"

def main : IO UInt32 := do
  match Prelude.boot with
  | .error e => IO.println s!"prelude boot failed: {e}"; return 1
  | .ok mp =>
    let h := mp.heap
    IO.println s!"booted: {h.objs.size} objects"
    IO.println "TableOk:"
    report h "+" "Integer#+"
    report h "-" "Integer#-"
    report h "*" "Integer#*"
    -- L152's nullary row. Worth a line of its own because `abs` fails here and
    -- `zero?` does not: `ResolvesAt` requires `fromPrelude = false`, and the prelude
    -- defines `abs` twice.
    report h "zero?" "Integer#zero?"
    -- L153: quantified over every class object, not just `Object`. Reported as a
    -- count plus the offenders, because the *shape* of this clause was picked by
    -- measurement: the class-indexed reading (`lookup.go` over `ancestors h k`) is
    -- **false** here — `T::Sig` defines `method_added` as an instance method, which
    -- is how `sorbet-runtime` installs a sig — while this receiver-indexed one holds.
    let hookBad := (List.range h.objs.size).filter (fun k =>
      (h.classPayload? k).isSome && (lookup h (.ref k) "method_added").isSome)
    IO.println s!"NoHook:\n  Object is a class = \
{(h.classPayload? Boot.objectId).isSome}\n  class objects resolving \
method_added (want 0): {hookBad.length}"
    for k in hookBad.take 5 do IO.println s!"    {k} = {className h k}"
    IO.println s!"Integer ancestors: {(ancestors h Boot.integerId).map (className h)}"
    -- L148's third clause. `scripts/ancestors_probe.lean` reports it per-class and
    -- also reports the *false* route (descent in `ObjId`); here it is one line,
    -- because `heapOkB` now includes it and this probe is that Bool's report.
    IO.println s!"Saturated:\n  saturatedB = {saturatedB h}"
    -- L151's fourth clause, the producer's: a string literal is typed `.cls "String"`
    -- by name while the step allocates at the id `Boot.stringId`. Reported as two
    -- lines because the two halves fail differently — an absent `String` satisfies
    -- the name clause on its own, since `className` answers `"Object"` out of bounds.
    IO.println s!"StrClsOk:\n  String is a class = \
{(h.classPayload? Boot.stringId).isSome}\n  className String = \
{className h Boot.stringId}"
    let ok := heapOkB h
    IO.println s!"\nheapOkB (prelude-booted): {ok}"
    return if ok then 0 else 1
