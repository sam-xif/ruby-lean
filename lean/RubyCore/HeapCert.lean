import RubyCore.Interp.Support
import RubyCore.Types.Decls

/-!
# The heap certificate — `HeapOk` as a `Bool`

F0 (`homebrew/widening-the-fragment.md` §3/§4). `Proof/StaticSoundness.lean`'s
invariant has two conjuncts that are facts about the heap alone — `TableOk` (the
three tabulated `Integer` builtins still resolve, live, public, unshadowed, not
`fromPrelude`) and `NoHook` (`Object` has no `method_added`). Static soundness at
the **prelude-booted** heap needs them there, and they cannot be decided in the
kernel: `Prelude.program` is `Lean.Json.parse Prelude.json` and `Lean.Json.parse`
does not kernel-reduce even on the input `"1"` (measured), while L94 bans the
`native_decide` escape.

So they are decided by *running* this function, and
`Proof/PreludeInv.heapOkB_sound` is the bridge: `heapOkB h = true → HeapOk h`.
The hypothesis of `check_sound_withPrelude` is then one `Bool` about the machine
actually in hand, which `scripts/heapok_probe.lean` computes and
`scripts/check-proofs.sh` fails on.

**This lives outside `Proof/` on purpose.** The alternative — defining it next to
the soundness lemma — means the probe cannot see it (`Proof/` is off the default
target, and an executable must not depend on the metatheory), so the probe would
end up re-implementing the predicate and could silently drift from the one the
theorem is about. One definition, two readers.

It is deliberately **not** wired into `Prelude.boot`: a prelude that redefined
`Integer#+` would be a legitimate model change that breaks the *static* route
only, and refusing to execute would be the wrong response to it. The check
belongs where the proofs are checked.
-/

namespace RubyCore

open Interp

/-- Executable form of `Proof.Static.IntBuiltinResolves`
    (`Proof/BuiltinConformance.lean`). Clause order matches that definition. -/
def intResolvesB (h : Heap) (mname bid : String) : Bool :=
  match lookup h (.int 0) mname with
  | none => false
  | some (owner, md) =>
      (md.builtin == some bid) && !md.undefined && (md.visibility == .pub) &&
        !md.fromPrelude &&
        (crubyShadow h ((ancestors h Boot.integerId).takeWhile (· != owner)) mname).isNone

/-- Executable form of `Proof.Saturated` (L144/L148): **the ancestor walk has
    finished before its fuel runs out**, one more unit of fuel changing nothing.

    Here rather than in `Proof/` for `heapOkB`'s reason — the probe must compute *the*
    predicate the theorem is about, not a copy — and folded into `heapOkB` below
    because it is a heap clause of the invariant exactly like `TableOk` and `NoHook`,
    and for the same reason: `DeclsOk_grow` needs it at an allocating step, and only
    the invariant can carry it there.

    `0 < objs.size` is not hygiene: at size `0` the class walk's fuel is `0`, whose arm
    is `[]` rather than `[k]`, and the out-of-bounds argument in `saturated_oob` needs
    a successor. No heap the interpreter builds is empty. -/
def saturatedB (h : Heap) : Bool :=
  0 < h.objs.size &&
    (List.range h.objs.size).all (fun k =>
      (modAncestors.go h k (h.objs.size + 1) == modAncestors.go h k h.objs.size) &&
        (ancestors.go h k (h.objs.size + 1) == ancestors.go h k h.objs.size))

/-- Executable form of `NoHook` (L153): no **class object** resolves `method_added`.
    Quantified over `List.range h.objs.size` because `classPayload?` answers `none`
    out of bounds, so every id outside the range satisfies the clause vacuously.

    Note it is `lookup h (.ref k)` — the receiver-indexed walk, through `k`'s
    eigenclass chain — and *not* `lookup.go h m (ancestors h k)`. The two differ, and
    the difference is not academic: `T::Sig` defines `method_added` as an instance
    method (that is how `sorbet-runtime` installs a sig), so the class-indexed reading
    is **false** at the prelude-booted heap while this one is true. -/
def noHookB (h : Heap) : Bool :=
  (h.classPayload? Boot.objectId).isSome &&
  ((List.range h.objs.size).all fun k =>
    (h.classPayload? k).isNone ||
      ((lookup h (.ref k) "method_added").isNone &&
       (lookup h (.ref k) "define_method").isNone)) &&
  -- J44: the fresh-chain half — `Class`'s chain (a fresh class's eigenclass) and
  -- `Module`'s chain (a fresh module's — `RubyCore.Interp.eigenclassOf`'s
  -- `isModule` arm), separately: `Module` is *in* `Class`'s chain, but nothing
  -- says the reverse, so checking one does not decide the other.
  (ancestors h Boot.classId).all (fun j =>
    match h.classPayload? j with
    | some cp => (cp.methods.find? (·.1 == "method_added")).isNone &&
                 (cp.methods.find? (·.1 == "define_method")).isNone
    | none => true) &&
  (ancestors h Boot.moduleId).all fun j =>
    match h.classPayload? j with
    | some cp => (cp.methods.find? (·.1 == "method_added")).isNone &&
                 (cp.methods.find? (·.1 == "define_method")).isNone
    | none => true

/-- L178's constant-table clause, decided. The `takeWhile` is the population
    `scripts/consts_probe.lean` measured: `{String, Comparable}` on the slice's
    admitted chains, not the heap's 87 class objects. -/
def noShadowBeforeB (h : Heap) (k : ObjId) : Bool :=
  (ancestors h k).contains Boot.objectId &&
    ((ancestors h k).takeWhile (· != Boot.objectId)).all fun j =>
      match h.classPayload? j with
      | some cp => cp.consts.isEmpty
      | none => true

/-- J56: `NamesUnique`, decided — quadratic over the ids, name-compares only
    where both are classes and the shared name is not machine-minted. -/
def namesUniqueB (h : Heap) : Bool :=
  (List.range h.objs.size).all fun j =>
    (List.range h.objs.size).all fun k =>
      match h.classPayload? j, h.classPayload? k with
      | some cpj, some cpk =>
        !(cpj.name == cpk.name) || cpj.name.data.head? == some '#' || j == k
      | _, _ => true

/-- J56: `Registered` at a boot-shaped heap, decided — every '#'-free-named
    class is registered on `Object` under its own (`::`-free) name. Stronger
    than `Registered` (the witness is pinned to `Object`), which is what makes
    it decidable; `classOkB_sound` weakens it to the existential. -/
def registeredBootB (h : Heap) : Bool :=
  (List.range h.objs.size).all fun j =>
    match h.classPayload? j with
    | some cp =>
      cp.name.data.head? == some '#' ||
      (j == Boot.objectId && cp.name == "Object") ||
      ((match constOwn h Boot.objectId cp.name with
        | some (.ref k) => k == j
        | _ => false) &&
        !(cp.name.data.contains ':'))
    | none => true

/-- Executable form of `ClassOk` (L156): every reopenable class name is bound, in
    `Object`'s **own** constant table, to a class object that is not a module.

    Those are the three tests `enterClassBody` applies before it takes the reopen
    branch, and computing them is what makes `reopenableClasses` a table one can add
    a row to rather than a promise one has to re-argue. `constOwn` rather than
    `constLookupFrom` on purpose: the interpreter's reopen detection is deliberately
    *not* the cref walk (`Interp/Dispatch.lean:228`), and a certificate that decided
    the wrong lookup would be worse than none. -/
def classOkB (h : Heap) : Bool :=
  (className h Boot.objectId == "Object") &&
  -- J56: global name uniqueness.
  namesUniqueB h &&
  -- J56: registration (boot-shaped: on `Object`, own name).
  registeredBootB h &&
  -- J56: `Object` is a class.
  (match h.classPayload? Boot.objectId with
   | some cp => !cp.isModule
   | none => false) &&
  -- L178, at `Object` itself: the toplevel frame's definee.
  noShadowBeforeB h Boot.objectId &&
  -- J41: no anonymous classes (the clause that makes `nameIfAnonymous` inert).
  ((List.range h.objs.size).all fun o =>
    match h.classPayload? o with
    | some cp => !cp.name.isEmpty
    | none => true) &&
  -- L194: quantified over the *read* table, with the reopen-only clauses guarded by
  -- membership in the smaller one — mirroring `ClassOk`'s own shape.
  Types.readableClasses.all fun n =>
    match constOwn h Boot.objectId n with
    | some (.ref k) =>
      match h.classPayload? k with
      | some cp =>
        className h k == n &&
          -- The uniqueness clause (F1b.9). Quadratic in the class objects only if
          -- every name is in the table; `reopenableClasses` has one row, so this is
          -- one linear scan per row. `scripts/names_probe.lean` reports the general
          -- fact this restricts.
          ((List.range h.objs.size).all fun j =>
            !((h.classPayload? j).isSome && className h j == n) || j == k) &&
          -- L189's two clauses for the `.const` read: the class object is a legal
          -- receiver, and `Object` is the sole owner of a constant of this name —
          -- the second is what makes a `cref` clause unnecessary.
          (k != Boot.regexpId) && (k != Boot.mathId) &&
          ((List.range h.objs.size).all fun j =>
            !((h.classPayload? j).isSome && j != Boot.objectId) ||
              (constOwn h j n).isNone) &&
          -- L194: the three the *reopen* rule needs, decided only where it applies.
          (!Types.reopenableClasses.contains n ||
            (!cp.isModule &&
              -- F1b.10: the chain starts at the class, so a `def` on it is what
              -- `lookup` finds. `prepends` come first in `ancestors`, so this is a
              -- real condition and not a restatement.
              ((ancestors h k).head? == some k) &&
              -- L178, at this class: a method body of it is the other frame a
              -- constant read can happen in.
              noShadowBeforeB h k))
      | none => false
    | _ => false

/-- Executable form of `Proof.Static.HeapOk` — `TableOk`, `NoHook`, since L148
    `Saturated`, and since L151 `LitClsOk`.

    The last is the producer's clause: a string literal is typed `.cls "String"`, a
    claim about a *name*, while the step allocates an object whose class is the *id*
    `Boot.stringId`. Two conjuncts rather than one because `className` answers
    `"Object"` at an id that is not a class, so the name alone would be satisfied by
    an absent `String`. -/
def heapOkB (h : Heap) : Bool :=
  intResolvesB h "+" "Integer#+" && intResolvesB h "-" "Integer#-" &&
    intResolvesB h "*" "Integer#*" &&
    -- L152's nullary row. Resolution knows nothing about arity, so this is the same
    -- `intResolvesB` at a fourth name.
    intResolvesB h "zero?" "Integer#zero?" &&
    noHookB h &&
    saturatedB h &&
    (h.classPayload? Boot.stringId).isSome &&
    (className h Boot.stringId == "String") &&
    -- L174's array-literal producer, folded into the same certificate for the same
    -- reason: `LitClsOk` is one clause per *literal-allocating* rule, and each rule
    -- claims a name where the step writes a boot id.
    (h.classPayload? Boot.arrayId).isSome &&
    (className h Boot.arrayId == "Array") &&
    (h.classPayload? Boot.procId).isSome &&
    (h.classPayload? Boot.hashId).isSome &&
    -- J52's regexp-literal producer.
    (h.classPayload? Boot.regexpId).isSome &&
    (className h Boot.regexpId == "Regexp") &&
    -- J53: `Object`'s eigenclass realized.
    (h.classPayload? Boot.objectId).isSome &&
    ((h.get Boot.objectId).eigen).isSome &&
    -- L156's sixth conjunct, folded in for the same reason L148 folded `saturatedB`:
    -- one certificate, decided once, rather than a second probe to keep in step.
    classOkB h

end RubyCore
