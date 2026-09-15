import RubyCore.PreludeBoot
import RubyCore.Proof.Static.Decls

/-!
The measurement **rung 3** owes (`slice-verdict.md` §4a): with the class-object arm
built (L184/L185), the row that pays for it is `Module#===` — 123 of the slice's
337 receiver-position constant occurrences, `case x when String` and
`when AlphaToken`, and the only large population behind neither wall (L181).

This checks the row is *witnessable* before it is written. `DeclsOk` obliges two
things of a row on `.clsOf n`, and both are heap facts about the class object's
**dispatch chain** rather than about the type language:

1. **`ResolvesAt h k "===" "Module#==="`** at `k = classOf h (.ref o)` — the
   eigenclass when there is one, `Class` otherwise (L180). That needs
   `lookupIn` to find the *builtin* `Module#===` with `builtin = some …`,
   `undefined = false`, `visibility = .pub` and **`fromPrelude = false`**, and it
   needs `crubyShadow` to answer `none` over the chain in front of the owner.
2. **`ConformsAt`** — `Builtins.run "Module#===" recv [b] m = .ok w m` with the
   machine unchanged, which `Builtins/Modules.lean:37` satisfies by construction
   (`isA` reads the heap and writes nothing) *provided* the receiver's
   `classPayload?` is `isSome`, which is `classRecv`'s own clause.

**The hazard is clause 1, and it is not hypothetical.** `prelude/prelude.rb:44`
defines `Object#===` in **Ruby**, so it is a `fromPrelude` method — and `Object` is
on every class object's dispatch chain. The row is only witnessable if `Module`
comes *first*, and that is an ordering fact about `ancestors`, not something the
type language can promise. This reports the whole resolution so the answer is read
rather than assumed — the same move `names_probe` made for the declaration rows and
`consts_probe` for the constant table, both of which changed a clause.

    lake env lean --run scripts/probes/classeq_probe.lean
      -- exit 0 iff every keyable class object resolves `===` to the `Module#===`
      -- builtin with the four flags `ResolvesAt` demands and no `crubyShadow`
-/

open RubyCore
open RubyCore.Interp

def probeNames : List String :=
  ["Object", "String", "Integer", "Float", "Array", "Hash", "Symbol"]

def main : IO UInt32 := do
  match Prelude.boot with
  | .error e => IO.eprintln s!"prelude boot failed: {e}"; return 1
  | .ok mp =>
    let h := mp.heap
    IO.println s!"booted: {h.objs.size} objects"
    let mut bad := 0
    for nm in probeNames do
      match constOwn h Boot.objectId nm with
      | some (.ref o) =>
        let k := classOf h (.ref o)
        IO.println s!"\n{nm} (class object {o}): dispatch class {k} ({className h k})"
        match Proof.Static.lookupIn h k "===" with
        | none =>
          IO.println s!"  lookupIn … \"===\" = NONE"
          bad := bad + 1
        | some (owner, md) =>
          let shadow := crubyShadow h ((ancestors h k).takeWhile (· != owner)) "==="
          IO.println s!"  owner        = {owner} ({className h owner})"
          IO.println s!"  builtin      = {md.builtin}"
          IO.println s!"  undefined    = {md.undefined}"
          IO.println s!"  visibility   = {repr md.visibility}"
          IO.println s!"  fromPrelude  = {md.fromPrelude}"
          IO.println s!"  chain before = {(ancestors h k).takeWhile (· != owner)}"
          IO.println s!"  crubyShadow  = {shadow}"
          let ok := md.builtin == some "Module#===" && !md.undefined &&
            md.visibility == Visibility.pub && !md.fromPrelude && shadow.isNone
          IO.println s!"  ResolvesAt witnessable = {ok}"
          if !ok then bad := bad + 1
      | _ => IO.println s!"\n{nm}: not a class constant of Object"
    -- Where `Object#===` — the *prelude* definition — actually sits, since it is
    -- the one that would shadow if the ordering went the other way.
    IO.println "\nthe prelude's Object#===, for comparison:"
    match methodOn h Boot.objectId "===" with
    | none => IO.println "  Object does not define `===`"
    | some (_, md) =>
      IO.println s!"  builtin = {md.builtin}  fromPrelude = {md.fromPrelude}"
    -- And the conformance side's one heap condition.
    IO.println "\nConformsAt's side condition (deferTwin? must be none):"
    for nm in probeNames do
      match constOwn h Boot.objectId nm with
      | some (.ref o) =>
        let d := Builtins.deferTwin? h "Module#===" (.ref o) [.int 0]
        IO.println s!"  {nm}: deferTwin? = {d.isSome}"
        if d.isSome then bad := bad + 1
      | _ => pure ()
    -- **And over *every* class object**, not just the keyable ones: a row
    -- hard-wired at `declFor`'s `.clsOf` arm — which is how a `Module#===` row can
    -- avoid needing a table key at all — obliges `EntryOk` at every name, so the
    -- resolution has to hold for all 87 rather than for the 7 above.
    let mut allBad := 0
    for k in [0:h.objs.size] do
      match h.classPayload? k with
      | none => pure ()
      | some _ =>
        let dk := classOf h (.ref k)
        match Proof.Static.lookupIn h dk "===" with
        | none => allBad := allBad + 1
        | some (owner, md) =>
          let shadow := crubyShadow h ((ancestors h dk).takeWhile (· != owner)) "==="
          if !(md.builtin == some "Module#===" && !md.undefined &&
               md.visibility == Visibility.pub && !md.fromPrelude && shadow.isNone) then
            IO.println s!"  NOT WITNESSABLE: {className h k} (id {k}), owner \
{className h owner}, builtin {md.builtin}, fromPrelude {md.fromPrelude}, shadow {shadow}"
            allBad := allBad + 1
    IO.println s!"\nclass objects (all {h.objs.size} ids scanned) whose `===` does not \
resolve to the builtin (want 0): {allBad}"
    IO.println s!"\nkeyable classes whose `===` row is not witnessable (want 0): {bad}"
    return if bad == 0 && allBad == 0 then 0 else 1
