import RubyCore.PreludeBoot
import RubyCore.Proof.Static.Decls

/-!
The measurement the **class-object arm of `Ty`** owes before anything is proved.
L179's `--consts` ratchet showed that arm gates all 28 of the slice's `const`
bodies — 45 of 48 constant assignments are initialized by a send on a class name,
and the reads are dominated by class and module names — so it is the next rung,
and this is the *fifth* probe in a row written because the previous four each
changed a clause rather than confirming one (`HANDOFF.md`: *measure the conclusion
before proving the lemma*).

## The questions, and why each one is a design decision and not a detail

A new arm `Ty.clsObj n` would mean *the class object named `n`*, and `EntryOk` is
stated over `∀ k, TyClass h τ k → ResolvesAt h k mname bid` — so the arm's
`TyClass` has to name **the id dispatch actually walks from**. For an ordinary
receiver that is `classOf`, which for a `.ref` is

```
match (h.get o).eigen with | some e => e | none => (h.get o).klass
```

so for a class object it is the **eigenclass** when one has been materialized and
`Class`/`Module` when one has not. That is the whole difficulty in one line, and
it splits into four measurable questions:

1. **Is the eigenclass materialized at boot?** If it is, `TyClass h (.clsObj n) k`
   can be *the eigenclass of the class named `n`* and be a fact about the heap. If
   it is not, `classOf` answers `klass` and a later `singleton_class` call would
   **move** the dispatch chain — the same hazard `HANDOFF.md` §Known wrong answers
   2 records about eigenclass *names*, one indirection along.
2. **What is on that chain?** `ResolvesAt` walks `ancestors h k`, so a singleton
   method installed by `def self.m` has to be findable there, and nothing may
   shadow it.
3. **Why exactly does `plainRecv` refuse a class**, and which of `invoke`'s
   receiver-shape special cases the refusal was buying. `entry_dispatch` discharges
   them from `plainRecv`; a class receiver hits them head-on.
4. **Does `Object#class`-style dispatch differ from `.new`?** `invoke` has an
   `invokeMaybeNew` arm, so `Regexp.new` and `Token.from` are *different* paths and
   only one of them is a plain send.

## What it reports

For `Object`, each `reopenableClasses` entry, and the boot classes the slice's
constants are built from (`Regexp`, `String`, `Integer`, `Float`, `Array`, `Hash`):
the class object's id, whether `eigen` is materialized, what `classOf` answers,
the first few ancestors of that answer, and `plainRecv`.

Then the aggregate: how many of the heap's class objects have a materialized
eigenclass, which is the population question `TyClass` for the new arm has to be
total over.

## The answers, measured at the prelude-booted heap

**Only 27 of 87 class objects have a materialized eigenclass.** For the other 60,
`classOf` answers `klass`, which is `Class` or `Module`. So a `TyClass` for the new
arm cannot be *the eigenclass of the class named `n`*: it is not total. And the
split runs straight through the classes the slice's constants are built from —

```
Object   eigen ✓  classOf = #<Class:Object>   ancestors [45, 44, 3, 2, 1]…
String   eigen ✓  classOf = #<Class:String>   ancestors [47, 45, 44, 3, 2]…
Array    eigen ✓  classOf = #<Class:Array>
Regexp   eigen ✓  classOf = #<Class:Regexp>
Integer  eigen ✗  classOf = Class             ancestors [3, 2, 1, 33, 0]…
Float    eigen ✗  classOf = Class
Hash     eigen ✗  classOf = Class
Symbol   eigen ✗  classOf = Class
```

— so the arm's dispatch id is **heterogeneous across exactly the classes that
matter**, and no uniform clause describes it. It has to be *whatever `classOf`
says*, carried.

**And carrying it is the hard part, because materialization moves it.**
`eigenclassOf` mutates `eigen` on an *existing* id, so a step that materializes
`Integer`'s eigenclass changes `classOf (.ref Integer)` from `Class` to the fresh
id — falsifying any stored `TyClass` fact about it. That is `HANDOFF.md` §What is
not next item 1 (*`TypeAgree`'s first clause is false as stated because
`eigenclassOf.go` mutates `eigen` on existing ids*) arriving at the class-object
arm rather than at the allocating `class'` branch, and it is the reason
`plainRecv` excludes classes in the first place. Nothing in today's fragment
materializes one (`defs`, `sclass`, `singleton_class` are all out), so the clause
is *establishable* — but it is a clause, not a free consequence, and it is the arm's
real price rather than the `Ty` constructor.

    lake env lean --run scripts/probes/classobj_probe.lean
      -- exit 0 iff no class object is `plainRecv` — the fact today's `valueTy?`
      -- rests on, and the one a regression here would break silently
-/

open RubyCore
open RubyCore.Interp

/-- The classes the slice's constants are built from, plus the two the fragment's
    frames can be executing in. -/
def probeNames : List String :=
  ["Object", "String", "Integer", "Float", "Array", "Hash", "Regexp", "Symbol"]

def main : IO UInt32 := do
  match Prelude.boot with
  | .error e => IO.eprintln s!"prelude boot failed: {e}"; return 1
  | .ok mp =>
    let h := mp.heap
    let n := h.objs.size
    IO.println s!"booted: {n} objects"
    -- Per class of interest: the four facts the new arm's `TyClass` depends on.
    for nm in probeNames do
      match constOwn h Boot.objectId nm with
      | some (.ref k) =>
        let o := h.get k
        let eig := o.eigen
        let dispatch := classOf h (.ref k)
        let anc := ancestors h dispatch
        IO.println s!"\n{nm}: id {k}"
        IO.println s!"  eigen materialized = {eig.isSome}  ({eig})"
        IO.println s!"  classOf (.ref {k}) = {dispatch} \
({className h dispatch})"
        IO.println s!"  ancestors of that = {anc.take 5}…"
        IO.println s!"  plainRecv = {Proof.Static.plainRecv h k}"
      | some _ => IO.println s!"\n{nm}: Object's constant is not a reference"
      | none => IO.println s!"\n{nm}: not a constant of Object"
    -- The population question. A `TyClass` for `.clsObj n` that names the
    -- eigenclass is only total if every class object has one.
    let mut cls := 0
    let mut withEigen := 0
    for k in [0:n] do
      match h.classPayload? k with
      | none => pure ()
      | some _ =>
        cls := cls + 1
        if (h.get k).eigen.isSome then withEigen := withEigen + 1
    IO.println s!"\nclass/module objects: {cls}"
    IO.println s!"  of which have a materialized eigenclass: {withEigen}"
    IO.println s!"  of which do NOT (so `classOf` answers `klass`): {cls - withEigen}"
    -- And what `klass` is for a class object that has no eigenclass — the id
    -- `ResolvesAt` would have to walk in that case.
    let mut klasses : Array (ObjId × String) := #[]
    for k in [0:n] do
      match h.classPayload? k with
      | none => pure ()
      | some _ =>
        if !(h.get k).eigen.isSome then
          let kl := (h.get k).klass
          if !klasses.any (fun p => p.1 == kl) then
            klasses := klasses.push (kl, className h kl)
    IO.println s!"  the distinct `klass` values of those: \
{klasses.map (fun p => p.2)}"
    -- **The ratchet.** `valueTy?` gives a `.ref` a type only when `plainRecv`, and
    -- `entry_dispatch` discharges `invoke`'s three receiver-shape special cases from
    -- exactly that. If a class object ever became `plainRecv`, the dispatch lemma
    -- would be false and nothing else in the build would notice.
    let mut plainCls := 0
    for k in [0:n] do
      match h.classPayload? k with
      | none => pure ()
      | some _ => if Proof.Static.plainRecv h k then plainCls := plainCls + 1
    IO.println s!"\nclass objects that are `plainRecv` (want 0): {plainCls}"
    return if plainCls == 0 then 0 else 1
