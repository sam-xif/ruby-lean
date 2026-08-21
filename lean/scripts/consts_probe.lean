import RubyCore.PreludeBoot
import RubyCore.Proof.Static.Decls

/-!
The measurement the **constant-table** rung owes before anything is proved — the
same move `names_probe.lean` made for the declaration rows and
`ancestors_probe.lean` for the fuel clause, and for the same reason
(`HANDOFF.md`: *measure the conclusion before proving the lemma*).

## The question, and why it is not the one the rung looks like

A constant *read* is **not** one table lookup. `evalExpr`'s `.const` arm
(`Interp.lean:158`) is artifact 03 §4's two phases:

```
cref.firstM (constOwn h · n)   |>.orElse (fun _ => constLookupFrom h defmod n)
```

— the lexical phase over the frame's `cref`, innermost first, and then the
inheritance phase over `ancestors h defmod`. So a table keyed on the *name*
alone can only be sound if, for every frame the fragment admits, that whole walk
reaches the one class the table is about. Two things can break it, and they are
what this probe measures:

1. **Shadowing.** Some class object other than `Object` has its own constant of
   the same name, and it comes earlier in the `cref` or in the ancestor chain.
   `X = 5` at toplevel writes `Object`'s table; `class String; Y = 7; end` writes
   **String's**, which the model gets right — so shadowing is a real
   possibility and not a hypothetical, and the rung's answer is to admit `casgn`
   only at toplevel *and* carry a clause saying the tabulated names are not
   shadowed. That clause is program-indexed, exactly like `ClassOk`'s, so it wants
   a **table of assignable names** whose every row is a `decide` — which is what
   this probe is for.
2. **`Object` not being reachable at all.** The inheritance phase only finds
   `Object`'s table if `Object ∈ ancestors h defmod`. True for a plain class
   chain, not automatic, and false for `BasicObject`.

## The answer, measured at the prelude-booted heap

**Both hazards are real and both are disposed of by the *reach*, which is two
classes wide.**

* 5 names are owned by **both `Object` and `T`** — `Struct`, `Enumerable`,
  `Range`, `Hash`, `Array` — so "no other class owns this name" is **false** as a
  clause, and a rung that stated it that way would be unprovable rather than
  merely strong. `T` is the sorbet shim, which is exactly what the slice's `sig`
  blocks are made of, so this is not an exotic collision.
* The classes strictly **in front of `Object`** on an admitted chain are
  `{String, Comparable}` — `ancestors Object = [Object, Kernel, BasicObject]`
  (`Object` at 0) and `ancestors String = [String, Comparable, Object, Kernel,
  BasicObject]` (`Object` at 2). They own **0** constants between them.

So the clause the rung wants is *no class strictly in front of `Object` on the
current definee's chain owns this name*, and at the booted heap it is discharged by
`decide` over two classes rather than over 87. `T` is not on any admitted chain,
which is why it is a report rather than a failure — and the moment
`reopenableClasses` grows to something under `T`, this probe stops exiting 0.

    lake env lean --run scripts/consts_probe.lean
      -- exit 0 iff `Object` is reachable from every keyable class and nothing
      -- strictly in front of it on an admitted chain owns a constant
-/

open RubyCore
open RubyCore.Interp

def main : IO UInt32 := do
  match Prelude.boot with
  | .error e => IO.eprintln s!"prelude boot failed: {e}"; return 1
  | .ok mp =>
    let h := mp.heap
    let n := h.objs.size
    IO.println s!"booted: {n} objects"
    -- Every class object that owns at least one constant.
    let mut owners : Array (ObjId × String × Nat) := #[]
    for k in [0:n] do
      match h.classPayload? k with
      | none => pure ()
      | some c =>
        if !c.consts.isEmpty then
          owners := owners.push (k, className h k, c.consts.length)
    IO.println s!"\nclass objects owning at least one constant: {owners.size}"
    for (k, nm, cnt) in owners do
      IO.println s!"  {nm} (id {k}): {cnt} constant(s)"
    -- The names `Object` owns, and the names everyone else owns. A table of
    -- assignable constants must avoid the second list.
    let objConsts : List String :=
      match h.classPayload? Boot.objectId with
      | some c => c.consts.map (·.1)
      | none => []
    IO.println s!"\nObject owns {objConsts.length} constant(s)"
    let mut elsewhere : Array (String × String) := #[]
    for (k, nm, _) in owners do
      if k != Boot.objectId then
        match h.classPayload? k with
        | some c => for (cn, _) in c.consts do elsewhere := elsewhere.push (cn, nm)
        | none => pure ()
    IO.println s!"constants owned by a class other than Object: {elsewhere.size}"
    for (cn, nm) in elsewhere do
      IO.println s!"  {nm}::{cn}"
    -- A name owned both by `Object` and by someone else is a shadowing hazard **if
    -- that someone else is in the reach of an admitted frame**. Reported first
    -- unconditionally, because the answer is not zero and the reason it is not a
    -- problem is the *reach*, which is measured below.
    let mut alsoOwned : Array (String × String) := #[]
    for (cn, nm) in elsewhere do
      if objConsts.contains cn then alsoOwned := alsoOwned.push (cn, nm)
    IO.println s!"\nnames owned by BOTH Object and another class: {alsoOwned.size}"
    for (cn, nm) in alsoOwned do
      IO.println s!"  {cn}: Object and {nm}"
    -- Is `Object` reachable by the inheritance phase from every class the
    -- fragment can be executing in, and **what is in front of it**? That prefix is
    -- the whole population a shadowing clause has to quantify away — not every
    -- class object, which is what makes the clause cheap.
    let keys := "Object" :: RubyCore.Types.reopenableClasses
    IO.println s!"\nthe classes a fragment frame's definee can be: {keys}"
    let mut unreachable := 0
    let mut reachBefore : Array ObjId := #[]
    for nm in keys do
      for k in [0:n] do
        match h.classPayload? k with
        | none => pure ()
        | some _ =>
          if className h k == nm then
            let anc := ancestors h k
            let pos := anc.findIdx? (· == Boot.objectId)
            IO.println s!"  {nm} (id {k}): ancestors = {anc}, Object at {pos}"
            match pos with
            | none => unreachable := unreachable + 1
            | some i =>
              for j in [0:i] do
                match anc[j]? with
                | some a => if !reachBefore.contains a then reachBefore := reachBefore.push a
                | none => pure ()
    IO.println s!"  keyable classes that cannot reach Object (want 0): {unreachable}"
    -- The clause, stated over exactly that prefix.
    IO.println s!"\nclasses strictly in front of Object on some admitted chain: \
{reachBefore.map (fun k => className h k)}"
    let mut hazards : Array (String × String) := #[]
    for k in reachBefore do
      match h.classPayload? k with
      | some c => for (cn, _) in c.consts do hazards := hazards.push (cn, className h k)
      | none => pure ()
    IO.println s!"constants they own — the shadowing hazard for a name-keyed table \
(want 0): {hazards.size}"
    for (cn, nm) in hazards do
      IO.println s!"  {nm}::{cn}"
    -- **The question the `.const` *read* rule turns on** (L189): for each name the
    -- rule can admit, is `Object` the **only** class object owning a constant of
    -- that name? If so the two-phase lookup lands on `Object`'s table from *any*
    -- frame — the lexical phase either finds it there or misses everything, and the
    -- inheritance phase then reaches `Object` with nothing in front of it owning
    -- anything (`NoShadowBefore`, L178). That is a **heap** clause, so it needs no
    -- `cref` clause on frames and no `ResolvesUser` change.
    IO.println "\nowners of each admissible constant name (want: Object only):"
    let mut ambiguous := 0
    for nm in RubyCore.Types.reopenableClasses do
      let mut who : Array String := #[]
      for k in [0:n] do
        match h.classPayload? k with
        | none => pure ()
        | some c =>
          if (c.consts.find? (·.1 == nm)).isSome then
            who := who.push s!"{className h k} (id {k})"
      IO.println s!"  {nm}: {who.size} owner(s) {who}"
      if who.size != 1 then ambiguous := ambiguous + 1
      else if !(who[0]!.startsWith "Object ") then ambiguous := ambiguous + 1
    IO.println s!"  names not owned by Object alone (want 0): {ambiguous}"
    return if hazards.isEmpty && unreachable == 0 && ambiguous == 0 then 0 else 1
