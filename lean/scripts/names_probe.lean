import RubyCore.PreludeBoot
import RubyCore.Proof.Static.Decls

/-!
Item 5 of the declaration-row rung, measured before anything is proved — the
same move `ancestors_probe.lean` made for the fuel clause, and for the same
reason (`HANDOFF.md`: *measure the conclusion before proving the lemma*).

## The question

A declaration row is keyed on a **class name**, because `infer` cannot name an
`ObjId`. So `DeclsOk`'s obligation for a row on `C` is quantified over every `k`
with `TyClass h (.cls C) k` — *every class object in the heap named `C`* — and a
`def` step installs the method on exactly **one** of them, the frame's definee.
The row is therefore only discharge-able if the name picks the class out
uniquely.

Two candidate clauses, and the probe reports both because they cost very
different amounts:

1. **`UniqueNames`** — no two distinct class objects share a name. General, and
   strong enough for any future rule, but it is a statement about all ~87 class
   objects and it has to survive every step that can name a class.
2. **Uniqueness at the names the fragment can actually key on** — today
   `reopenableClasses` plus `"Object"`. A table, like `ClassOk`'s, where a row
   costs a `decide`.

It also reports the *eigenclass* names, because those are the ones most likely
to collide: L124 fixed a family of them that were all called
`#<Class:Object>`, and a regression there would silently make a row
unprovable rather than wrong.

    lake env lean --run scripts/names_probe.lean   # exit 0 iff no class name is shared
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
    -- Every class object, with its name.
    let mut named : Array (String × ObjId) := #[]
    for k in [0:n] do
      match h.classPayload? k with
      | none => pure ()
      | some _ => named := named.push (className h k, k)
    IO.println s!"class/module objects: {named.size}"
    -- Collisions.
    let mut dupes : Array (String × ObjId × ObjId) := #[]
    for i in [0:named.size] do
      for j in [i+1:named.size] do
        let (ni, ki) := named[i]!
        let (nj, kj) := named[j]!
        if ni == nj then dupes := dupes.push (ni, ki, kj)
    IO.println s!"\nclass names shared by two distinct objects (want 0): {dupes.size}"
    for (nm, a, b) in dupes do
      IO.println s!"  {nm}: {a} and {b}"
    -- The names the fragment keys on today.
    let keys := "Object" :: RubyCore.Types.reopenableClasses
    IO.println s!"\nthe names a row can be keyed on today: {keys}"
    for nm in keys do
      let hits := named.filter (fun p => p.1 == nm)
      IO.println s!"  {nm}: {hits.size} class object(s) {hits.map (·.2)}"
    -- Eigenclasses, the family L124 fixed and the one most likely to regress.
    let eigen := named.filter (fun p => p.1.startsWith "#<Class:")
    IO.println s!"\neigenclass-named objects: {eigen.size}"
    return if dupes.isEmpty then 0 else 1
