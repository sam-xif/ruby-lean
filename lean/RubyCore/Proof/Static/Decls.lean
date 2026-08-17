import RubyCore.Proof.Static.Locals

/-!
# F1a — the refinement invariant

`PLAN.md` **D10**, `homebrew/typing-a-mutable-method-table.md` §2 and §7. The
heap-side clause of the machine invariant, restated from an equality into a lower
bound:

> **For every method the declarations name, `lookup` resolves it to something
> conforming to its declared signature.**

## Why this, and not "the table matches the declarations"

The equality reading excludes ordinary Ruby, and — the counterexample that forced
the change — it excludes **`sorbet-runtime` itself**, which installs a `sig` by
replacing the method-table entry with a validating wrapper. So the
declaration-matching fragment could not type a single annotated method
(`Types/Fragment.lean`'s header, L139).

The lower bound has the property the equality was reaching for anyway: a
type-stuck outcome comes from a method being **missing** or **wrong-typed**, never
from one being present and unmentioned. So `DeclsOk` says nothing at all about
undeclared names, is therefore **monotone in the method table**, and every
additive step preserves it with no side condition. `DeclsOk_defineMethod` is that
statement, and the only side condition it carries is that the `def` does not
displace a *declared* name — a redefinition, which is F1c's checkable case.

## The decomposition, which is the substance rather than the restatement

Each entry splits into two clauses that behave differently under a heap write:

* **`ResolvesTo`** — resolution: the name reaches a builtin, live, public,
  unshadowed. Heap-dependent, and the *only* thing preservation has to re-derive.
  `Proof/HeapFacts.lean`'s `defineMethod` chain is exactly what discharges it.
* **`ConformsAt`** — conformance: applied to arguments of the declared parameter
  types, that builtin answers a value of the declared return type. Its two
  conclusions are **heap-uniform** (`∀ h'`), which is what makes it transport for
  free; its hypotheses read the invariant's heap, which is where F1b's nominal
  types will need to read it.

That split is why P0's three `int_*_dispatch` rewrites collapse into one
`entry_dispatch`, and why §7's *"the ~128 `builtinSig` conformance lemmas become
per-entry witnesses of the invariant rather than a parallel obligation"* is now
literally true: a new entry is a `ConformsAt` proof and nothing else.

`TableOk` is kept, unchanged, as the **certificate-shaped** form of the same fact
— `heapOkB` decides it and `scripts/heapok_probe.lean` reports it, so F0 is
untouched — and `tableOk_declsOk` is the bridge. That direction (concrete ⇒
general) is deliberate: the invariant carries the general statement, and the
runtime checks the concrete one.
-/

namespace RubyCore
namespace Proof
namespace Static

open Interp
open RubyCore.Types

set_option maxRecDepth 100000

/-! ## 1. Resolution and conformance -/

/-- **Resolution.** In heap `h`, sending `mname` to `recv` reaches the builtin
    `bid`: the table resolves it, the entry is live, public and not
    prelude-suppressed, and neither shadow gate fires.

    Generalizes `IntBuiltinResolves` from the fixed receiver `.int 0` to an
    arbitrary value, and costs **no** extra clause, which is worth recording
    because it was not obvious: `crubySingletonShadow` looked like it would need
    carrying for an abstract receiver, and does not — `invoke` consults that gate
    only when lookup did *not* resolve to a builtin, so an entry satisfying this
    predicate never reaches it. Measured by the proof of `entry_dispatch` not
    using it.

    **Re-measured at F1b and still true** (L141), against a prediction that it
    would not be: `HANDOFF.md` expected an object receiver to bring the singleton
    gate back. It does not, because the gate is a fact about which *branch* runs
    (`md.builtin = none`) and not about which *receiver* arrives, and this
    predicate pins the branch. -/
def ResolvesTo (h : Heap) (recv : Value) (mname bid : String) : Prop :=
  ∃ owner md,
    lookup h recv mname = some (owner, md) ∧
    md.builtin = some bid ∧
    md.undefined = false ∧
    md.visibility = .pub ∧
    md.fromPrelude = false ∧
    crubyShadow h ((ancestors h (classOf h recv)).takeWhile (· != owner)) mname = none

/-- The method-table walk from a **class**, which is all `lookup` ever does with a
    receiver (`lookup h v m = lookup.go h m (ancestors h (classOf h v))`, definitionally). -/
def lookupIn (h : Heap) (k : ObjId) (mname : String) : Option (ObjId × MethodDef) :=
  lookup.go h mname (ancestors h k)

/-- **Resolution, indexed by the dispatch class instead of by a receiver** (L147).
    Every clause of `ResolvesTo` is this predicate at `classOf h recv` — L145's
    `ResolvesTo_classOf` is the observation, and this is the observation taken
    seriously.

    Why it matters, and it is not aesthetics: the inhabitant-indexed clause is
    **not preservable across an allocation**. A fresh object of a declared class
    needs resolution, and the only receiver-shaped hypothesis available is about
    receivers the *old* heap had — of which there may be none, because a class can be
    declared before it has any instances. Indexed by the class, the same fact is
    carried by a hypothesis a growing heap can transport, and `DeclsOk_grow` loses
    its side condition entirely. -/
def ResolvesAt (h : Heap) (k : ObjId) (mname bid : String) : Prop :=
  ∃ owner md,
    lookupIn h k mname = some (owner, md) ∧
    md.builtin = some bid ∧
    md.undefined = false ∧
    md.visibility = .pub ∧
    md.fromPrelude = false ∧
    crubyShadow h ((ancestors h k).takeWhile (· != owner)) mname = none

/-- The two are the same statement at `k = classOf h recv`, definitionally — which is
    why every existing consumer of `ResolvesTo` keeps working unchanged. -/
theorem resolvesTo_of_resolvesAt {h : Heap} {recv : Value} {mname bid : String}
    (hr : ResolvesAt h (classOf h recv) mname bid) : ResolvesTo h recv mname bid := hr

/-- **The dispatch classes a type names.** The ground arms are boot ids and read no
    heap at all; the class arm is a name *and* the requirement that the id really is
    a class — without which an out-of-bounds id would satisfy `.cls "Object"`
    (`className` answers `"Object"` there) and the clause would demand resolution
    from a heap slot that does not exist.

    `valueTy_tyClass` is the bridge from the value judgement, and `plainRecv`'s L147
    clause is what makes the class arm's first component available there. -/
def TyClass (h : Heap) (τ : Ty) (k : ObjId) : Prop :=
  match τ with
  | .int => k = Boot.integerId
  | .bool => k = Boot.trueClassId ∨ k = Boot.falseClassId
  | .nilT => k = Boot.nilClassId
  | .sym => k = Boot.symbolId
  | .cls n => (h.classPayload? k).isSome ∧ className h k = n

theorem valueTy_tyClass {h : Heap} {v : Value} {τ : Ty} (hv : ValueTy h v τ) :
    TyClass h τ (classOf h v) := by
  cases v with
  | int a => cases τ <;> simp_all [ValueTy, valueTy?, TyClass, classOf]
  | bool b =>
    have : τ = .bool := by simpa [ValueTy, valueTy?] using hv.symm
    subst this
    cases b
    · exact Or.inr rfl
    · exact Or.inl rfl
  | nil => have : τ = .nilT := by simpa [ValueTy, valueTy?] using hv.symm
           subst this; rfl
  | sym s => have : τ = .sym := by simpa [ValueTy, valueTy?] using hv.symm
             subst this; rfl
  | ref o =>
    have hp := valueTy_ref_plain hv
    have : τ = .cls (className h (classOf h (.ref o))) := by
      simpa [ValueTy, valueTy?, hp] using hv.symm
    subst this
    exact ⟨valueTy_ref_klass_isSome hv, rfl⟩
  | flt f => simp [ValueTy, valueTy?] at hv

/-! ### Resolution to a **user-defined** method

`ResolvesAt` pins `md.builtin = some bid`, and that is not a restriction anyone
chose — it is what `ConformsAt`'s conclusion forces (`Builtins.run … m = .ok w m`,
the machine back unchanged in one step). A method with `builtin = none` reaches
`enterUserMethod`, which **pushes a frame**: the send produces no value at all,
and the declared return type is a claim about what the activation eventually
returns.

So `EntryOk` has to become a disjunction, and this is the second disjunct's
resolution half. Every clause is a gate on `invoke`'s path to `enterUserMethod`,
read off `Interp/Send.lean` in order, and there is nothing here that is not one:

| clause | gate |
|---|---|
| `lookupIn … = some (owner, md)` | the walk resolves |
| `builtin = none` | takes the user branch rather than `Builtins.run` |
| `undefined = false` | not an `undef` tombstone |
| `visibility = .pub` | `visError?` at an `.explicit` site |
| `crubyShadow … = none` | the between-classes fidelity gate |
| `params = []`, `declared = []` | `enterUserMethod` binds nothing, so the callee's environment is `[]` |
| `capturedFrame = none` | `FrameConforms`'s first clause — the frame is self-contained |
| `(classPayload? md.owner).isSome` | `FrameConforms`'s definee clause; the frame's `defmod` **is** `md.owner` |

**Note what is absent: `fromPrelude`.** `ResolvesAt` requires
`fromPrelude = false` because a prelude method has no `bid` to run. The user arm
has no such need — a prelude-Ruby method is *exactly* a `MethodDef` with
`builtin = none`, and every gate above is one it can pass. That is D8's dominant
category (`widening-the-fragment.md` §5.1: 153 of 285 prelude methods rising to
269) becoming **expressible**, which `HANDOFF.md` §constraint 1 records as
blocked. The shadow clause keeps the `fromPrelude` conditional `invokeDispatch`
itself applies, rather than dropping it.

`crubySingletonShadow` — the other gate on this branch, and the one three rungs
predicted would come back — costs nothing again: it answers `none` unless the
receiver's payload is `.cls`, which `plainRecv` refutes. Third prediction, third
time it is free. -/
def ResolvesUser (h : Heap) (k : ObjId) (mname : String) (md : MethodDef) : Prop :=
  ∃ owner,
    lookupIn h k mname = some (owner, md) ∧
    md.builtin = none ∧
    md.undefined = false ∧
    md.visibility = .pub ∧
    md.params = [] ∧
    md.declared = [] ∧
    md.capturedFrame = none ∧
    (h.classPayload? md.owner).isSome ∧
    crubyShadow h
      (if md.fromPrelude then [] else (ancestors h k).takeWhile (· != owner)) mname = none

/-- **Conformance for a user method is discharged by the checker, not by running
    anything**: the body infers at the declared return type in the environment
    `enterUserMethod` builds, which for a zero-parameter method is the empty one.

    This is the reflexive step, and it is worth naming as such. Every obligation
    the invariant has carried until now is a fact about a *Lean builtin*, proved
    once, externally, and independent of the checker. This one makes `infer`'s own
    verdict on a method body a conjunct of the soundness invariant — the checker
    appears inside the statement of its own soundness theorem. That is sound (the
    recursion is on the *heap*, not on the proof), and it is the reason a user
    witness cannot be a lemma about `startArgs` the way `ConformsAt` is: the fact
    it asserts is not about one step.

    **The body's output table must be the one it was checked at** (F1b.8). A
    method whose body itself declares a method would leave rows in force that the
    caller's continuation was not typed against, and `frameK` — which resumes the
    caller at a table fixed when the frame was pushed — has no way to carry them.
    Requiring `md.body` to leave the table alone is what makes the pop total, and
    it is the same shape as `LoopOk`'s stability condition and for the same
    reason. It costs nothing today, since no rule grows the table at all. -/
def UserConforms (D : Decls) (c : String) (md : MethodDef) (d : MethodDecl) : Prop :=
  d.params = [] ∧ ∃ Γ', infer D [] md.body false c = some (d.ret, Γ', D)

/-- **Conformance to a declared signature.** On a receiver of the declared class
    and arguments of the declared parameter types, `bid` answers a value of the
    declared return type without touching the machine, and defers to no prelude
    twin.

    The name clause excludes `send`/`public_send`/`__send__`, which `invoke` treats
    specially: their *first argument* is the real method name, so a declared
    signature for them would describe the wrong call. This is the same exclusion
    `int_bin_dispatch` carried as an explicit hypothesis, promoted to part of what
    conformance means.

    The deferral clause is `∀ h'` on purpose. L116 put a **prelude-twin deferral**
    in front of every builtin — one whose answer would need a dispatch it cannot
    perform hands the call to prelude Ruby instead of running — and `deferTwin?`
    reads the *method table*, so a heap write can change it. Requiring the
    deferral to be absent in every heap is what makes conformance survive a `def`;
    for arithmetic over two Integers it is true by computation, and an entry for
    which it is false does not belong in the table at all.

    **Heap-uniform since L146, and that is a change of statement rather than of
    strength.** It used to be indexed by the invariant's heap, with the machine
    quantified *inside* the existential — so `∀ m, run … m = .ok w m` (heap-uniform
    conclusion) sat under `ValueTy h recv τr` (heap-*dependent* hypothesis). The
    asymmetry cost a transport: `ConformsAt_defineMethod` had to read its hypotheses
    in the old heap and its conclusion in the new one, which is the only reason
    `TypeAgree` needed a backward direction at all (L143) — and the backward
    direction **does not exist for a growing heap**, so the producer could not have
    had it.

    Quantifying the machine over the whole statement fixes both: conformance is now
    a fact about a builtin and a declaration, mentioning no heap, so it is not a
    clause preservation has to re-establish. `DeclsOk`'s heap-dependent half is
    exactly `ResolvesTo` — which is what L140's split said it should be, one level
    more honestly than L140 achieved. Every witness's *proof* is unchanged: the
    hypotheses it actually used were `valueTy_int`-shaped inversions, and those are
    heap-independent. -/
def ConformsAt (τr : Ty) (mname bid : String) (d : MethodDecl) : Prop :=
  (mname == "send" || mname == "public_send" || mname == "__send__") = false ∧
  bid ≠ "Object#raise" ∧
  ∀ (m : Machine) recv args, ValueTy m.heap recv τr → ValuesTy m.heap args d.params →
    (∀ h' : Heap, Builtins.deferTwin? h' bid recv args = none) ∧
    ∃ w, ValueTy m.heap w d.ret ∧ Builtins.run bid recv args m = .ok w m

/-- One declared method, satisfied: **some** builtin both resolves for every
    receiver of the class and conforms. Existential in `bid` rather than pinning
    it, which is what makes the condition a lower bound — the invariant never says
    *which* implementation answers, only that a conforming one does. -/
def BuiltinEntryOk (h : Heap) (τr : Ty) (mname : String) (d : MethodDecl) : Prop :=
  ∃ bid, (∀ k, TyClass h τr k → ResolvesAt h k mname bid) ∧ ConformsAt τr mname bid d

/-- **The user witness** (L157): resolution to a `MethodDef` with `builtin = none`,
    with conformance discharged by the *checker* rather than by running anything.

    The table is the invariant's own. A witness that carried a *smaller* one,
    related by `SubDecls`, is what the arm will need once a `def` grows the table
    — a body is checked where it is written and called later — and it is
    deliberately not here yet: nothing in this commit grows the table, so the
    clause would be a speculative one with no proof to justify its shape.
    `SubDecls` is defined (`Types/Decls.lean`) and unused, which is the honest
    place to leave it. -/
def UserEntryOk (D : Decls) (h : Heap) (τr : Ty) (mname : String) (d : MethodDecl) :
    Prop :=
  ∃ md c, (∀ k, TyClass h τr k → ResolvesUser h k mname md) ∧
    className h md.owner = c ∧ UserConforms D c md d

/-- A declared method is satisfied by **either** kind of witness. A disjunction
    rather than a generalization because the two produce *different steps*:
    `entry_dispatch` lands a value in one step, `user_dispatch` lands a frame with
    the body still to run. `HANDOFF.md` §constraint 1 predicted this shape ("a
    disjunction of two witness kinds") and predicted the reason. -/
def EntryOk (D : Decls) (h : Heap) (τr : Ty) (mname : String) (d : MethodDecl) : Prop :=
  BuiltinEntryOk h τr mname d ∨ UserEntryOk D h τr mname d

/-- The receiver-shaped form the send cases want, recovered from the class-indexed
    one. This direction is all anything needs, and it is the direction that is
    available: a receiver hands over its dispatch class (`valueTy_tyClass`), while a
    class does not hand over a receiver — which is the asymmetry L147 is about. -/
theorem EntryOk.resolves {h : Heap} {τr : Ty} {mname bid : String} {recv : Value}
    (hres : ∀ k, TyClass h τr k → ResolvesAt h k mname bid)
    (hrv : ValueTy h recv τr) : ResolvesTo h recv mname bid :=
  resolvesTo_of_resolvesAt (hres (classOf h recv) (valueTy_tyClass hrv))

/-- **The refinement invariant.** Note what is *not* here: no clause about names
    the table does not declare, and no upper bound on the heap's method table.
    That absence is the whole content of D10. -/
def DeclsOk (D : Decls) (h : Heap) : Prop :=
  ∀ τr mname d, declFor D τr mname = some d → EntryOk D h τr mname d

/-! ## 2. The uniform dispatch step

What the `argsK` case of preservation needs, once per declared method instead of
once per tabulated builtin. This is `int_bin_dispatch` with the three
`Integer`-specific hypotheses replaced by `EntryOk`.
-/

theorem entry_dispatch {m : Machine} {τr : Ty} {mname : String} {d : MethodDecl}
    {recv : Value} {args : List Value}
    (he : BuiltinEntryOk m.heap τr mname d)
    (hrv : ValueTy m.heap recv τr) (hargs : ValuesTy m.heap args d.params) :
    ∃ w, ValueTy m.heap w d.ret ∧
      startArgs m recv .explicit mname args [] .none
        = .next (withCtl m (.value w)) := by
  obtain ⟨bid, hres, hns, hraise, hconf⟩ := he
  obtain ⟨owner, md, hlook, hb, hu, hvis, hpre, hbtw⟩ := EntryOk.resolves hres hrv
  obtain ⟨hdefer, w, hw, hrun⟩ := hconf m recv args hrv hargs
  refine ⟨w, hw, ?_⟩
  simp only [startArgs, finishSend]
  rw [invoke.eq_def]
  -- The receiver has to be case-split, and the reason is worth stating: `invoke`
  -- has receiver-shape special cases *before* the resolved-builtin path (a `.proc`
  -- answers `call`, a `.hsh` with a proc default answers `[]`, and a `.cls` reaches
  -- `invokeMaybeNew` or the `Math`/`Regexp` singleton arms), so an abstract
  -- receiver leaves them standing.
  --
  -- **F1a closed them by there being no inhabitant** — every one is a `.ref` and
  -- `valueTy?` had no `.ref` arm. F1b closes them by a hypothesis instead:
  -- `plainRecv` is exactly the negation of the three payload shapes, and it is part
  -- of what the class arm of `valueTy?` *means*, so the inversion hands it over
  -- (`valueTy_shapes`). The special cases are still discharged by the type
  -- judgement; what changed is that the judgement now has to say so out loud.
  rcases valueTy_shapes hrv with ⟨a, rfl⟩ | ⟨b, rfl⟩ | rfl | ⟨sy, rfl⟩ | ⟨o, rfl, hplain⟩
  -- The four immediate cases are F1a's, unchanged: `invoke`'s receiver-shape arms
  -- are all `.ref`, so the outer match falls straight through.
  case' inr.inr.inr.inr =>
    -- The `.ref` case, which is F1b's whole bill. Case on the payload: `plainRecv`
    -- refutes the three special arms and the rest reach `invokeDispatch`, which is
    -- what `ResolvesTo` describes. Note this does **not** need
    -- `crubySingletonShadow`: that gate sits on `invoke`'s `md.builtin = none`
    -- branch (`Interp/Send.lean:246`) and `ResolvesTo` pins `md.builtin = some bid`,
    -- so F1a's measurement survives an abstract object receiver unchanged.
    cases hpl : (m.heap.get o).payload
    -- The three special shapes, refuted by `plainRecv` rather than reasoned about.
    case proc => exact absurd hplain (by simp [plainRecv, hpl])
    case hsh => exact absurd hplain (by simp [plainRecv, hpl])
    case cls => exact absurd hplain (by simp [plainRecv, hpl])
    -- Everything else is the uniform path, and identical to the immediate cases.
    all_goals
      simp [invoke.invokeDispatch, hpl, hlook, hb, hu, hbtw, hpre, visError?, hvis,
        appendKwHash, hrun, hns, hdefer, hraise]
  all_goals
    simp [invoke.invokeDispatch, hlook, hb, hu, hbtw, hpre, visError?, hvis,
      appendKwHash, hrun, hns, hdefer, hraise]

/-- The activation `enterUserMethod` builds for a zero-parameter, non-closure
    method. Named rather than left to an existential because unification cannot
    find a twelve-field literal from inside a `simp`, and because the two fields
    `FrameConforms` reads are then `rfl`. -/
def userFrame (recv : Value) (md : MethodDef) (mname : String) : Frame :=
  { self := recv, locals := [], defmod := md.owner, cref := md.cref,
    blk := none, callBlk := none, kind := .method,
    meth := md.superName.getD mname, runParams := [], runFromDM := false,
    captured := none }

set_option maxHeartbeats 1000000 in
/-- **The user-method dispatch step** (L157) — `entry_dispatch`'s sibling, and the
    reason the two had to split rather than generalize.

    `entry_dispatch` concludes `.next (withCtl m (.value w))`: one step, a value,
    the machine otherwise unchanged. This concludes a **frame push** with the body
    in `ctl` and nothing in hand. Same hypothesis shape, different `StepResult`
    argument, so no common statement covers both — which is exactly what
    `HANDOFF.md` §constraint 1 predicted ("`entry_dispatch` splits in two, because
    the two branches have different step results"). -/
theorem user_dispatch {m : Machine} {τr : Ty} {mname : String} {md : MethodDef}
    {recv : Value}
    (hres : ResolvesUser m.heap (classOf m.heap recv) mname md)
    (hrv : ValueTy m.heap recv τr) :
    startArgs m recv .explicit mname [] [] .none
      = .next { m with frames := m.frames.push (userFrame recv md mname),
                       stack := m.frames.size :: m.stack,
                       kont := .frameK m.frames.size :: m.kont,
                       ctl := .eval md.body } := by
  obtain ⟨owner, hlook, hb, hu, hvis, hpar, hdec, hcap, hown, hbtw⟩ := hres
  -- **Two stages, and the split is not cosmetic.** Unfolding `invoke` and
  -- `enterUserMethod` in one `simp` exhausts the heartbeat budget: the first is a
  -- nest of receiver-shape and gate `match`es, the second a hundred lines of
  -- parameter binding, and `simp` interleaves them. Reducing the dispatch to a
  -- *named call* first keeps each stage's search space small.
  -- `lookup h v m` *is* `lookupIn h (classOf h v) m` (`lookupIn`'s docstring), so
  -- this is the same equation with the definitional factoring made visible —
  -- `resolvesTo_of_resolvesAt`'s move, at the user arm.
  have hlook' : lookup m.heap recv mname = some (owner, md) := hlook
  have hinv : invoke m recv .explicit mname [] none []
      = enterUserMethod m recv mname md [] none [] := by
    rw [invoke.eq_def]
    -- Exactly `entry_dispatch`'s receiver split, and for the same reason: `invoke`'s
    -- three receiver-shape arms are all `.ref`, and `plainRecv` refutes them. The
    -- `.cls` refutation does double duty on this branch — it is also what makes
    -- `crubySingletonShadow`, the gate `ResolvesTo` never has to mention, answer
    -- `none`.
    rcases valueTy_shapes hrv with ⟨a, rfl⟩ | ⟨b, rfl⟩ | rfl | ⟨sy, rfl⟩ | ⟨o, rfl, hplain⟩
    case' inr.inr.inr.inr =>
      cases hpl : (m.heap.get o).payload
      case proc c => exact absurd hplain (by simp [plainRecv, hpl])
      case hsh xs => exact absurd hplain (by simp [plainRecv, hpl])
      case cls c => exact absurd hplain (by simp [plainRecv, hpl])
      all_goals
        simp [invoke.invokeDispatch, hpl, hlook', hb, hu, hbtw, hvis, visError?,
          crubySingletonShadow]
    all_goals
      simp [invoke.invokeDispatch, hlook', hb, hu, hbtw, hvis, visError?,
        crubySingletonShadow]
  simp only [startArgs, finishSend, hinv]
  simp [enterUserMethod, classifyFull, hpar, hdec, hcap, userFrame, withCtl,
    appendKwHash]

/-! ## 3. Preservation: the additive step is free

The D10 claim, as a lemma. `defineMethod` of a name the declarations do not
mention leaves every declared entry alone: `lookup` is unchanged by
name-disjointness (`Proof/HeapFacts.lean`), and conformance is heap-uniform where
it has to be.
-/

/-- A declared method's name is declared. Needed to turn the *syntactic* side
    condition `declaresName D name = false` — what `infer` checks on a `def` —
    into the name-disjointness `lookup_defineMethod` wants. -/
theorem declOf?_declaresName {D : Decls} {cls name : String} {d : MethodDecl}
    (h : declOf? D cls name = some d) : declaresName D name = true := by
  unfold declOf? declsFor at h
  cases hf : D.find? (·.1 == cls) with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some cd =>
    rw [hf] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨e, he, _⟩ := h
    have hp := List.find?_some he
    exact List.any_eq_true.mpr
      ⟨cd, List.mem_of_find?_eq_some hf,
        List.any_eq_true.mpr ⟨e, List.mem_of_find?_eq_some he, hp⟩⟩

theorem declFor_declaresName {D : Decls} {τ : Ty} {mname : String} {d : MethodDecl}
    (h : declFor D τ mname = some d) : declaresName D mname = true := by
  have key : ∀ (c : String) (cs : List String),
      (match declOf? D c mname with
       | none => none
       | some d0 =>
         if cs.all (fun c' => declOf? D c' mname == some d0) then some d0 else none)
        = some d → declaresName D mname = true := by
    intro c cs hh
    cases hd : declOf? D c mname with
    | none => rw [hd] at hh; exact absurd hh (by simp)
    | some d0 => exact declOf?_declaresName hd
  -- The class arm (F1b) is the only one that is not immediate: the key is a
  -- variable, and `tyClassNames` can answer `[]` (for a ground name), which
  -- `declFor` reads as no declaration.
  cases τ <;> (unfold declFor at h; simp only [tyClassNames] at h)
  case cls n =>
    by_cases hg : groundClassNames.contains n = true
    · rw [if_pos hg] at h; exact absurd h (by simp)
    · rw [if_neg hg] at h; exact key n [] h
  all_goals
    first
      | exact key "Integer" [] h
      | exact key "TrueClass" ["FalseClass"] h
      | exact key "NilClass" [] h
      | exact key "Symbol" [] h

/-! ~~`ResolvesTo_defineMethod`~~ is **withdrawn** (L150): L147 moved its only caller
(`DeclsOk_defineMethod`) to `ResolvesAt_defineMethod`, and a receiver-shaped resolution
transport has had no consumer since. The receiver-shaped *predicate* `ResolvesTo` stays
— `entry_dispatch` reads it, via `EntryOk.resolves` — but nothing transports it. -/

/-! ~~`ResolvesTo_classOf`~~ and ~~`ResolvesTo_grow`~~ (L145) are **superseded by
L147's class indexing** and withdrawn. `ResolvesTo_classOf` said resolution factors
through `classOf`; `ResolvesAt` *is* that factoring, so the lemma became `rfl`.
`ResolvesTo_grow` transported the receiver-shaped form and needed the receiver to be
an id the old heap had — which is exactly the restriction that could not reach a fresh
object, i.e. the reason the indexing changed. `ResolvesAt_grow` below needs no such
hypothesis. -/

/-- **Resolution survives an allocating step, for every class, with no side
    condition** (L147). Every clause of `ResolvesAt` is a fact about the method
    table, the ancestor walk or the shadow gate at a *class id*, and `PlainGrow` pins
    all three at every id — so unlike the receiver-shaped version this says something
    about classes the old heap had no instances of, which is the case a producer
    creates.

    `Saturated` enters once, through `ancestors` (L144). Contrast
    `ResolvesAt_defineMethod`, whose side condition is *name* disjointness: a write to
    an existing table can displace an entry, an allocation cannot. -/
theorem ResolvesAt_grow {h h' : Heap} {k : ObjId} {mname bid : String}
    (hg : PlainGrow h h') (hsat : Saturated h)
    (hr : ResolvesAt h k mname bid) : ResolvesAt h' k mname bid := by
  obtain ⟨owner, md0, hlook, hb, hu, hvis, hpre, hbtw⟩ := hr
  refine ⟨owner, md0, ?_, hb, hu, hvis, hpre, ?_⟩
  · unfold lookupIn at hlook ⊢
    rw [hg.ancestors_eq hsat, lookup_go_grow hg]; exact hlook
  · rw [hg.ancestors_eq hsat, crubyShadow_grow hg]; exact hbtw

/-- **The user arm's growth transport** (L157). Clause for clause the same argument
    as `ResolvesAt_grow`, plus one: `(classPayload? md.owner).isSome`, which
    `PlainGrow` pins at *every* id. That extra clause is the frame's definee, and it
    is the only place the user arm reads the heap somewhere `ResolvesAt` does not. -/
theorem ResolvesUser_grow {h h' : Heap} {k : ObjId} {mname : String} {md : MethodDef}
    (hg : PlainGrow h h') (hsat : Saturated h)
    (hr : ResolvesUser h k mname md) : ResolvesUser h' k mname md := by
  obtain ⟨owner, hlook, hb, hu, hvis, hpar, hdec, hcap, hown, hbtw⟩ := hr
  refine ⟨owner, ?_, hb, hu, hvis, hpar, hdec, hcap, by rw [hg.payload]; exact hown, ?_⟩
  · unfold lookupIn at hlook ⊢
    rw [hg.ancestors_eq hsat, lookup_go_grow hg]; exact hlook
  · rw [hg.ancestors_eq hsat, crubyShadow_grow hg]; exact hbtw

/-- **And across a `def` of a different name** — the same name-disjointness
    `ResolvesAt_defineMethod` needs, since a write to an existing table can displace
    an entry. `classPayload?_isSome_defineMethod` covers the definee clause. -/
theorem ResolvesUser_defineMethod {h : Heap} {k : ObjId} {mname : String}
    {md : MethodDef} {cls : ObjId} {name : String} {md' : MethodDef}
    (hr : ResolvesUser h k mname md) (hne : ¬ (mname = name)) :
    ResolvesUser (defineMethod h cls name md') k mname md := by
  obtain ⟨owner, hlook, hb, hu, hvis, hpar, hdec, hcap, hown, hbtw⟩ := hr
  refine ⟨owner, ?_, hb, hu, hvis, hpar, hdec, hcap,
    by rw [classPayload?_isSome_defineMethod]; exact hown, ?_⟩
  · unfold lookupIn at hlook ⊢
    rw [ancestors_defineMethod, lookup_go_defineMethod h cls name mname md' hne]
    exact hlook
  · rw [ancestors_defineMethod, crubyShadow_defineMethod]; exact hbtw

/-- The `defineMethod` case, class-indexed. Same proof as the receiver-shaped one it
    replaces, with `classOf_defineMethod` no longer needed — a class id is not a
    receiver, so there is nothing to re-derive about dispatch. -/
theorem ResolvesAt_defineMethod {h : Heap} {k : ObjId} {mname bid : String}
    {cls : ObjId} {name : String} {md : MethodDef}
    (hr : ResolvesAt h k mname bid) (hne : ¬ (mname = name)) :
    ResolvesAt (defineMethod h cls name md) k mname bid := by
  obtain ⟨owner, md0, hlook, hb, hu, hvis, hpre, hbtw⟩ := hr
  refine ⟨owner, md0, ?_, hb, hu, hvis, hpre, ?_⟩
  · unfold lookupIn at hlook ⊢
    rw [ancestors_defineMethod, lookup_go_defineMethod h cls name mname md hne]
    exact hlook
  · rw [ancestors_defineMethod, crubyShadow_defineMethod]; exact hbtw

/-! ### `TyClass` transports backwards, which is the point

The clause is `∀ k, TyClass h τr k → ResolvesAt h k mname bid`, so preserving it means
reading `TyClass` in the **new** heap and needing it in the old one. That direction is
available for both steps, and for the same reason in both: `TyClass` reads only
`className` and `classPayload?`-ness, which `defineMethod` preserves exactly and a
`PlainGrow` preserves at every id — including the ids the old heap did not have, where
both answer `"Object"` and `none`.

This is where the inhabitant-indexed clause failed. `ValueTy` does **not** transport
backwards across a growing heap (L143), because a fresh object *is* a new inhabitant;
a fresh object is not a new class.
-/

theorem TyClass_defineMethod {h : Heap} {τr : Ty} {k cls : ObjId} {name : String}
    {md : MethodDef} (ht : TyClass (defineMethod h cls name md) τr k) : TyClass h τr k := by
  cases τr with
  | cls n =>
    exact ⟨by rw [← classPayload?_isSome_defineMethod h cls k name md]; exact ht.1,
      by rw [← className_defineMethod h cls k name md]; exact ht.2⟩
  | _ => exact ht

theorem TyClass_grow {h h' : Heap} {τr : Ty} {k : ObjId} (hg : PlainGrow h h')
    (ht : TyClass h' τr k) : TyClass h τr k := by
  cases τr with
  | cls n => exact ⟨by rw [← hg.payload k]; exact ht.1, by rw [← hg.className_eq k]; exact ht.2⟩
  | _ => exact ht

/-! ~~`ConformsAt_defineMethod`~~ is **withdrawn** (L146) rather than repaired.
`ConformsAt` no longer mentions a heap, so a heap-writing step has nothing to
re-establish about it and the lemma has no content. It is worth recording what it
*was*: the only consumer of `TypeAgree`'s backward direction — the one L143 had to
supply specially, and the one a growing step cannot supply at all. Deleting the
clause deleted the obligation. -/

/-- **The additive step preserves the invariant, with no condition beyond
    non-displacement.** D10's claim, and the reason `infer`'s `def` rule checks
    `declaresName` rather than a list of names. -/
theorem DeclsOk_defineMethod {D : Decls} {h : Heap} {cls : ObjId} {name : String}
    {md : MethodDef} (hd : DeclsOk D h) (hfresh : declaresName D name = false) :
    DeclsOk D (defineMethod h cls name md) := by
  intro τr mname decl hdecl
  have hne : ¬ (mname = name) := by
    intro heq
    rw [heq] at hdecl
    exact absurd (declFor_declaresName hdecl) (by simp [hfresh])
  -- `hconf` passes straight through (L146): it is a fact about `bid` and `decl`, not
  -- about this heap. What is left is resolution, and after L147 that is
  -- class-indexed — so the hypothesis read backwards is `TyClass`, not `ValueTy`.
  -- **That is what retired `TypeAgree`'s backward direction**: `TyClass` transports
  -- both ways for any step that preserves `className` and `classPayload?`-ness.
  --
  -- L157: two arms now, and the *same* argument twice. `UserConforms` mentions no
  -- heap either — it is a fact about `infer` and a body — so both conformance halves
  -- pass through and only the resolution halves transport.
  rcases hd τr mname decl hdecl with ⟨bid, hres, hconf⟩ | ⟨mdu, cu, hres, hnm, hconf⟩
  · exact Or.inl ⟨bid,
      fun k ht => ResolvesAt_defineMethod (hres k (TyClass_defineMethod ht)) hne, hconf⟩
  · exact Or.inr ⟨mdu, cu,
      fun k ht => ResolvesUser_defineMethod (hres k (TyClass_defineMethod ht)) hne,
      by rw [className_defineMethod]; exact hnm, hconf⟩

/-- **The invariant survives an allocating step, unconditionally** (L147).

    L146 proved this with a side condition — *every receiver the new heap types was
    already typed by some receiver of the same dispatch class* — which was the honest
    form of an inhabitant-indexed clause and would have become real work the moment a
    user class had a declared row. L147's class indexing removes it: `TyClass`
    transports backwards (`TyClass_grow`), `ResolvesAt` forwards
    (`ResolvesAt_grow`), and conformance mentions no heap at all (L146). There is
    nothing left to assume.

    ~~`DeclsOk_grow_ground`~~ and ~~`declsOk_baseDecls_grow`~~ (L146) are withdrawn
    with the side condition they discharged. Their content was *"the base table
    declares nothing at a class type, so the fresh object inhabits nothing declared"*
    — true, still true, and no longer load-bearing. That is the good kind of
    withdrawal: the theorem got stronger, so its scaffolding stopped being needed.

    What a producer still owes is not here: it is the **step**, i.e. that the rule
    really does produce a `PlainGrow`-related machine, and `Saturated` for the heap it
    starts from (`saturatedB`, checked by `check-proofs.sh`). -/
theorem DeclsOk_grow {D : Decls} {h h' : Heap} (hg : PlainGrow h h') (hsat : Saturated h)
    (hd : DeclsOk D h) : DeclsOk D h' := by
  intro τr mname decl hdecl
  rcases hd τr mname decl hdecl with ⟨bid, hres, hconf⟩ | ⟨mdu, cu, hres, hnm, hconf⟩
  · exact Or.inl ⟨bid,
      fun k ht => ResolvesAt_grow hg hsat (hres k (TyClass_grow hg ht)), hconf⟩
  · exact Or.inr ⟨mdu, cu,
      fun k ht => ResolvesUser_grow hg hsat (hres k (TyClass_grow hg ht)),
      by rw [hg.className_eq]; exact hnm, hconf⟩

/-! ## 4. The bridge from `TableOk`

`TableOk` stays exactly as it was, because F0's two theorems and the runtime
certificate (`heapOkB`, `scripts/heapok_probe.lean`) are stated over it. What
changes is that it is no longer what the invariant carries: it is the *concrete
witness* for `baseDecls`, and this section is the derivation.
-/

/-- Every entry of `baseDecls` still resolves in this heap, spelled out at the
    three concrete names. A *heap* condition, so preservation must re-establish
    it.

    **This is no longer what the invariant carries** (F1a): `DeclsOk` is, and this
    is its concrete witness for `baseDecls` via `tableOk_declsOk`. It is kept
    exactly as it was because it is the *certificate-shaped* form — `HeapCert.lean`
    reflects it into a `Bool`, `scripts/heapok_probe.lean` reports it per clause,
    and `check-proofs.sh` fails if it stops holding at the booted heap. Moved here
    from `Proof/Static/Konts.lean` with the rest of the heap conditions, since the
    file that defines the refinement invariant is where its instances belong. -/
def TableOk (h : Heap) : Prop :=
  IntBuiltinResolves h "+" "Integer#+" ∧
  IntBuiltinResolves h "-" "Integer#-" ∧
  IntBuiltinResolves h "*" "Integer#*" ∧
  -- L152's nullary row. `IntBuiltinResolves` is arity-agnostic — it is a fact about
  -- the method table, not about the call — so the fourth clause is the same shape as
  -- the first three and `intResolvesB` decides it unchanged.
  IntBuiltinResolves h "zero?" "Integer#zero?"

/-- **No `def` hook is installed on any class** (generalized in L153).

    `Interp.lean:2625` fires `Module#method_added` on the defining module right after
    installing a method, and the hook body is arbitrary Ruby we cannot type — so the
    fragment has to exclude it rather than reason about it.

    It is excludable because the prelude installs the hook **lazily**: the
    `Object.define_singleton_method(:method_added)` in `T.__toplevel_sig`
    (`prelude/prelude.rb:1187`) runs only when a toplevel `sig` is evaluated. A
    sig-free program therefore never has one, and `lookup` simply misses [V —
    `rfl` on the boot heap, and measured over all 105 ids at the prelude-booted one].

    **Quantified over class objects as receivers, and the indexing is the content.**
    L149's version fixed the receiver at `Boot.objectId`, which is all a fragment with
    no `class` can ever define into; a class body's `def` installs on the class it is
    inside, so the clause has to hold at *every* possible definee. Two ways to say
    that, and **only one of them is true**:

    * `∀ k, (classPayload? k).isSome → lookup h (.ref k) "method_added" = none` —
      the hook lookup `evalExpr` actually performs, which walks
      `ancestors (classOf h (.ref k))`, i.e. the class object's **eigenclass** chain.
      **True**, at 0 of 105 ids.
    * `∀ k, (classPayload? k).isSome → lookupIn h k "method_added" = none` — the
      class-*indexed* walk, over `k`'s own instance chain. **False**: `T::Sig`
      defines `method_added` as an instance method, because that is how
      `sorbet-runtime` installs a sig (D9/D10, and `T.__wrap`'s comment says so).

    So this is L147's lesson with the answer the other way round — the content depends
    on the *receiver*, not on the class-indexed walk — and `T::Sig` is the witness that
    picking by analogy rather than by measurement would have produced a false clause.

    The first conjunct **replaces** L149's `Boot.objectId < h.objs.size` with a
    strictly stronger fact at the same price: it is what lets the `def` case
    *instantiate* the quantifier at the definee a toplevel `def` uses. Being a class
    implies being in bounds (`classPayload?_isSome_lt`), so the bound is subsumed —
    the same put-the-condition-in-the-judgement trade, measured for the fifth time.

    A pure *heap* fact, with the frame's definee carried by `FrameConforms` instead —
    phrasing it at the current frame's `defmod` makes it unprovable across `frameK`,
    which resumes a different frame. -/
def NoHook (h : Heap) : Prop :=
  (h.classPayload? Boot.objectId).isSome ∧
    ∀ k, (h.classPayload? k).isSome → lookup h (.ref k) "method_added" = none

/-- **`NoHook` survives an allocating step** (L149, restated at L153's indexing).

    Simpler than L149's version, and the reason is the indexing: `PlainGrow` pins
    `classPayload?` at **every** id, so the set of class objects is unchanged and
    there is no fresh-id case to discharge at all. L149 needed an explicit
    `Boot.objectId < h.objs.size` to rule out the pathological case where `Object` is
    the id being allocated; here `classPayload?_isSome_lt` supplies the bound from the
    quantifier's own hypothesis. -/
theorem NoHook_grow {h h' : Heap} (hg : PlainGrow h h') (hsat : Saturated h)
    (hh : NoHook h) : NoHook h' := by
  refine ⟨by rw [hg.payload]; exact hh.1, fun k hk => ?_⟩
  have hk' : (h.classPayload? k).isSome := by rw [← hg.payload k]; exact hk
  rw [lookup_grow hg hsat (fun o hEq => by cases hEq; exact classPayload?_isSome_lt hk')]
  exact hh.2 k hk'

/-- **And a `def`** (L153). The receiver's dispatch class is unchanged
    (`classOf_defineMethod`) and the name differs, so `lookup_defineMethod` applies at
    every class object — the same argument L149's Object-only version made, now made
    once per definee rather than once. -/
theorem NoHook_defineMethod {h : Heap} {cls : ObjId} {name : String} {md : MethodDef}
    (hh : NoHook h) (hne : ¬ ("method_added" = name)) :
    NoHook (defineMethod h cls name md) := by
  refine ⟨by rw [classPayload?_isSome_defineMethod]; exact hh.1, fun k hk => ?_⟩
  have hk' : (h.classPayload? k).isSome := by
    rw [← classPayload?_isSome_defineMethod h cls k name md]; exact hk
  rw [lookup_defineMethod _ _ name "method_added" md _ hne
    (classOf_defineMethod _ _ _ _ _)]
  exact hh.2 k hk'

/-- `noHookB` reflects `NoHook` (L153). The out-of-range ids are the only interesting
    step: `classPayload?` answers `none` there, so the clause holds vacuously and the
    bounded `all` really does decide an unbounded `∀`. -/
theorem noHookB_sound {h : Heap} (hb : noHookB h = true) : NoHook h := by
  unfold noHookB at hb
  simp only [Bool.and_eq_true] at hb
  obtain ⟨hobj, hb⟩ := hb
  refine ⟨hobj, fun k hk => ?_⟩
  by_cases hlt : k < h.objs.size
  · have := List.all_eq_true.mp hb k (List.mem_range.mpr hlt)
    simp only [Bool.or_eq_true, Option.isNone_iff_eq_none] at this
    rcases this with h1 | h2
    · exact absurd hk (by rw [h1]; simp)
    · exact h2
  · exact absurd hk (by rw [classPayload?_oob h k hlt]; simp)

/-- **The boot `String` id is a class named `"String"`** (L151), and it is the
    fourth heap conjunct for the same reason the other three are conjuncts rather
    than theorems: nothing in the `Heap` *type* forbids a heap where it is false,
    and no step a program can take makes it false.

    It exists because `infer` types a string literal `.cls "String"` — a claim about
    a **name** — while the step allocates an object whose class is the **id**
    `Boot.stringId`. Something has to join the two, and the invariant is where it
    is cheapest: the alternative is for the producer's consecution case to re-derive
    it at the use site, which is the trade L142/L143/L147/L149 each priced and each
    resolved the same way.

    Both halves are needed and neither implies the other: `className` answers
    `"Object"` at an id that is not a class, so the name clause alone would be
    satisfied by an *absent* `String`, and `plainRecv` separately requires the
    allocated object's class to *be* a class. -/
def StrClsOk (h : Heap) : Prop :=
  (h.classPayload? Boot.stringId).isSome ∧ className h Boot.stringId = "String"

/-- **`StrClsOk` survives an allocating step**, and unlike `NoHook_grow` it needs
    neither a bound nor saturation: `PlainGrow` pins `classPayload?` at *every* id
    (that is exactly what the non-class restriction buys, `lookup_go_grow`'s note)
    and `className` is a function of it. -/
theorem StrClsOk_grow {h h' : Heap} (hg : PlainGrow h h') (hs : StrClsOk h) :
    StrClsOk h' :=
  ⟨by rw [hg.payload]; exact hs.1, by rw [hg.className_eq]; exact hs.2⟩

/-- **And a `def`**, from the same two facts `TyClass_defineMethod` uses. A
    `defineMethod` at `Boot.stringId` itself rewrites the payload, but
    `setClassPayload` changes the method table and nothing else, so the class stays
    a class and keeps its name. -/
theorem StrClsOk_defineMethod {h : Heap} {cls : ObjId} {name : String}
    {md : MethodDef} (hs : StrClsOk h) : StrClsOk (defineMethod h cls name md) :=
  ⟨by rw [classPayload?_isSome_defineMethod h cls Boot.stringId name md]; exact hs.1,
   by rw [className_defineMethod h cls Boot.stringId name md]; exact hs.2⟩

/-! ### The reopen promise

`ClassOk` is `Inv`'s **fifth** heap conjunct (L156) and the first that is indexed
by something the *program* chooses rather than by a boot id. It is the D10-shaped
program-indexed clause `HANDOFF.md` §What is left item 4 asked for, in the only
form that is preserved: not *absent or a class* — "absent" is falsified by the
very step that would need it — but **present and a non-module class**, which every
step in the fragment leaves alone.
-/

/-- **Every reopenable class name really names a reopenable class**: `Object`'s own
    constant table binds it to a class object that is not a module.

    Those are exactly the three tests `enterClassBody` applies before `pushFrame`
    (`Interp/Dispatch.lean:236–246`), and stating them as one clause is what lets
    the `class'` consecution case be a rewrite rather than a case analysis over
    branches it must then refute one at a time.

    The `isModule = false` conjunct is not redundant with being a class: a
    `ClassPayload` describes modules too, and `enterClassBody` compares the flag
    against the head keyword. A `module M` reopened as `class M` is a `TypeError`,
    which is a `.jump`, which `CtlOk` refuses — so the flag has to be pinned here
    rather than derived. -/
def ClassOk (h : Heap) : Prop :=
  -- **`Object` is named `"Object"`** (F1b.9). `BottomObj` says the outermost
  -- activation's definee is the `Object` *id*; `StackCtx` needs its *name*, because
  -- a declaration row is keyed on one. Folded in here rather than made a seventh
  -- conjunct of `Inv` because it is the same kind of fact as the rows below and
  -- `classOkB` decides it in the same pass.
  className h Boot.objectId = "Object" ∧
  ∀ n ∈ reopenableClasses, ∃ k cp,
    constOwn h Boot.objectId n = some (.ref k) ∧
    h.classPayload? k = some cp ∧ cp.isModule = false ∧
    -- **The constant's object is a class *named* `n`** (F1b.9). Without this the
    -- class-body frame has a definee the invariant cannot name, and a declaration
    -- row — which is keyed on a name, because `infer` cannot name an `ObjId` — has
    -- nothing to attach to.
    className h k = n ∧
    -- **and it is the only one.** `TyClass h (.cls n) j` quantifies over *every*
    -- class object named `n`, so a row on `n` obliges all of them while a `def`
    -- installs on exactly one. Measured before it was assumed
    -- (`scripts/names_probe.lean`): at the prelude-booted heap no two of the 87
    -- class objects share a name at all, so the general clause is true and this
    -- restriction of it to the table's own names is what a row costs — the same
    -- shape, and the same argument, as the row above it.
    (∀ j, (h.classPayload? j).isSome → className h j = n → j = k)

/-- The `Bool` decides the `Prop`. Same shape as `noHookB_sound`: the certificate
    computes, the invariant quantifies, and this is the one place they meet. -/
theorem classOkB_sound {h : Heap} (hb : classOkB h = true) : ClassOk h := by
  simp only [classOkB, Bool.and_eq_true, beq_iff_eq] at hb
  refine ⟨hb.1, ?_⟩
  intro n hn
  have := List.all_eq_true.mp hb.2 n hn
  revert this
  cases hc : constOwn h Boot.objectId n with
  | none => simp
  | some v =>
    cases v with
    | ref k =>
      cases hp : h.classPayload? k with
      | none => simp [hc, hp]
      | some cp =>
        intro hm
        simp only [hc, hp, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
          List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hm
        obtain ⟨⟨hmod, hnm⟩, huniq⟩ := hm
        refine ⟨k, cp, rfl, hp, hmod, hnm, fun j hj hjn => ?_⟩
        -- The bound comes from the payload, exactly as `StackCtx`'s does
        -- (`classPayload?_isSome_lt`), so the `List.range` scan really is a scan
        -- over every id that can satisfy the hypothesis.
        have hlt : j < h.objs.size := classPayload?_isSome_lt hj
        rcases huniq j (List.mem_range.mpr hlt) with hno | heq
        · have : ¬ ((h.classPayload? j).isSome = true ∧ className h j = n) := by
            simpa using hno
          exact absurd ⟨hj, hjn⟩ this
        · exact heq
    | _ => simp [hc]

/-- **`ClassOk` survives an allocating step**, and it needs nothing but
    `PlainGrow`'s third clause: `constOwn` is `classPayload?` composed with a
    lookup in `consts`, and `PlainGrow` pins `classPayload?` at *every* id. That is
    the same one-line argument `StrClsOk_grow` makes, for the same reason. -/
theorem ClassOk_grow {h h' : Heap} (hg : PlainGrow h h') (hc : ClassOk h) :
    ClassOk h' := by
  refine ⟨by rw [hg.className_eq]; exact hc.1, ?_⟩
  intro n hn
  obtain ⟨k, cp, h1, h2, h3, h4, h5⟩ := hc.2 n hn
  refine ⟨k, cp, by unfold constOwn at h1 ⊢; rw [hg.payload]; exact h1,
    by rw [hg.payload]; exact h2, h3, ?_, fun j hj hjn => ?_⟩
  -- `PlainGrow` pins `classPayload?` at every id and `className` with it, so both
  -- new clauses transport by the same rewrite the old ones do.
  · rw [hg.className_eq]; exact h4
  · exact h5 j (by rw [← hg.payload]; exact hj) (by rw [← hg.className_eq]; exact hjn)

/-- **And a `def`** — including a `def` in the body of the very class being
    reopened, which is the case that makes the clause worth carrying rather than
    re-deriving. `defineMethod` writes `methods`; `constOwn` and `isModule` read
    neither. -/
theorem ClassOk_defineMethod {h : Heap} {cls : ObjId} {name : String}
    {md : MethodDef} (hc : ClassOk h) : ClassOk (defineMethod h cls name md) := by
  refine ⟨by rw [className_defineMethod]; exact hc.1, ?_⟩
  intro n hn
  obtain ⟨k, cp, h1, h2, h3, h4, h5⟩ := hc.2 n hn
  refine ⟨k, ?_⟩
  rw [constOwn_defineMethod h cls Boot.objectId name n md]
  -- The payload at `k` may genuinely differ — this is the in-body `def` case — so
  -- the witness is the *new* payload, and what carries over is its `isModule`.
  have hsh := shape_defineMethod h cls k name md
  cases hk : (defineMethod h cls name md).classPayload? k with
  | none => rw [hk, h2] at hsh; exact absurd hsh (by simp)
  | some cp' =>
    refine ⟨cp', h1, rfl, ?_, ?_, fun j hj hjn => ?_⟩
    -- `isModule` is not in `clsShape`, but it *is* in `clsName_defineMethod` — L124
    -- put it there because the anonymous-class fallback renders by it. Reused rather
    -- than reproved.
    · have hnm := clsName_defineMethod h cls k name md
      rw [hk, h2] at hnm
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hnm
      rw [hnm.2]; exact h3
    -- The two F1b.9 clauses need `className` unmoved by a method-table write, which
    -- is `clsName_defineMethod` at *every* id rather than at the definee only.
    · rw [className_defineMethod]; exact h4
    · exact h5 j (by rw [← classPayload?_isSome_defineMethod]; exact hj)
        (by rw [← className_defineMethod]; exact hjn)

/-- **`TableOk` survives a user `def`.** Still needed, because `HeapOk` — F0's
    heap half — is stated over `TableOk`, and `PreludeInv.heapOk_defineMethod` is
    its `defineMethod` case. `DeclsOk_defineMethod` is the general version of the
    same claim; this one stays because the certificate does.

    The side condition is what the fragment checks syntactically — a `def` may not
    shadow a tabulated builtin name. It holds for *any* target class `cls`, so
    reopening `Integer` itself is fine as long as the name differs. -/
theorem TableOk_defineMethod {h : Heap} {cls : ObjId} {name : String}
    {md : MethodDef} (ht : TableOk h)
    (h1 : ¬ (name = "+")) (h2 : ¬ (name = "-")) (h3 : ¬ (name = "*"))
    (h4 : ¬ (name = "zero?")) :
    TableOk (defineMethod h cls name md) :=
  ⟨IntBuiltinResolves_defineMethod ht.1 (fun hh => h1 hh.symm),
   IntBuiltinResolves_defineMethod ht.2.1 (fun hh => h2 hh.symm),
   IntBuiltinResolves_defineMethod ht.2.2.1 (fun hh => h3 hh.symm),
   IntBuiltinResolves_defineMethod ht.2.2.2 (fun hh => h4 hh.symm)⟩

/-- The `Integer` entries of `baseDecls`, from the corresponding
    `IntBuiltinResolves`. The `hrun`/`hdefer` hypotheses are the ones
    `Proof/BuiltinConformance.lean` already discharges by `rfl` and `simp`. -/
theorem entryOk_int {h : Heap} {mname bid : String} {op : Int → Int → Int}
    (hres : IntBuiltinResolves h mname bid)
    (hns : (mname == "send" || mname == "public_send" || mname == "__send__") = false)
    (hraise : bid ≠ "Object#raise")
    (hrun : ∀ (x y : Int) (m' : Machine),
      Builtins.run bid (.int x) [.int y] m' = .ok (.int (op x y)) m')
    (hdefer : ∀ (h' : Heap) (x y : Int),
      Builtins.deferTwin? h' bid (.int x) [.int y] = none) :
    BuiltinEntryOk h .int mname { params := [.int], ret := .int } := by
  refine ⟨bid, ?_, hns, hraise, ?_⟩
  · -- L147: the clause is now indexed by the dispatch class, and `TyClass h .int k`
    -- *is* `k = Boot.integerId` — so the `valueTy_int` inversion and the
    -- `lookup_int_const`/`classOf_int` rewrites all go away. `IntBuiltinResolves` is
    -- already a statement about `lookup h (.int 0)`, which is `lookupIn` at that
    -- class definitionally.
    intro k hk
    subst hk
    exact hres
  · -- L146: the conformance half is now quantified over the machine, and the proof
    -- did not move — every hypothesis it used was a `valueTy_int` inversion, which
    -- is heap-independent. That is the evidence the heap index was carrying nothing.
    intro m recv args hrv hargs
    obtain ⟨a, rfl⟩ := valueTy_int hrv
    -- `d.params = [.int]`, so `ValuesTy` pins the argument list to one integer.
    match args, hargs with
    | [b], ⟨hb, _⟩ =>
      obtain ⟨y, rfl⟩ := valueTy_int hb
      exact ⟨fun h' => hdefer h' a y, .int (op a y), rfl, hrun a y m⟩

/-- **The nullary sibling of `entryOk_int`** (L152). The same three-clause shape with
    `ValuesTy` pinning the argument list to `[]` instead of to one integer — which is
    the whole difference an arity makes to the *invariant*, as against the difference
    it makes to the machine (a whole `KontOk` constructor and consecution case, because
    a zero-argument send dispatches in the `recvK` step rather than a step later).

    The return type is a parameter because a nullary builtin need not answer its own
    receiver type; `zero?` answers `.bool`. -/
theorem entryOk_int_nullary {h : Heap} {mname bid : String} {τret : Ty}
    {f : Int → Value}
    (hres : IntBuiltinResolves h mname bid)
    (hns : (mname == "send" || mname == "public_send" || mname == "__send__") = false)
    (hraise : bid ≠ "Object#raise")
    (hty : ∀ (hp : Heap) (x : Int), ValueTy hp (f x) τret)
    (hrun : ∀ (x : Int) (m' : Machine),
      Builtins.run bid (.int x) [] m' = .ok (f x) m')
    (hdefer : ∀ (h' : Heap) (x : Int),
      Builtins.deferTwin? h' bid (.int x) [] = none) :
    BuiltinEntryOk h .int mname { params := [], ret := τret } := by
  refine ⟨bid, ?_, hns, hraise, ?_⟩
  · intro k hk
    subst hk
    exact hres
  · intro m recv args hrv hargs
    obtain ⟨a, rfl⟩ := valueTy_int hrv
    match args, hargs with
    | [], _ => exact ⟨fun h' => hdefer h' a, f a, hty m.heap a, hrun a m⟩

/-- **The base table declares nothing at a class type.** `baseDecls`'s only key is
    `"Integer"`, and `tyClassNames` subtracts the ground names from the class arm's
    range (L141) precisely so that `.cls "Integer"` — whose inhabitants are objects
    of *some* class merely named `Integer` — cannot read `Integer`'s row.

    Pulled out of `tableOk_declsOk`'s class arm in L146, where it discharged the
    side condition `DeclsOk_grow` then had. L147 removed that side condition, so this
    is back to being one refutation used once — kept split out because the class arm
    of a `declFor` computation is worth a name. -/
theorem declFor_baseDecls_cls (n mname : String) :
    declFor baseDecls (.cls n) mname = none := by
  unfold declFor
  simp only [tyClassNames]
  by_cases hg : groundClassNames.contains n = true
  · rw [if_pos hg]
  · rw [if_neg hg]
    have hne : ("Integer" == n) = false := by
      by_cases he : "Integer" = n
      · exact absurd (by subst he; simp [groundClassNames]) hg
      · simpa using he
    simp [declOf?, declsFor, baseDecls, hne]

theorem tableOk_declsOk {h : Heap} (ht : TableOk h) : DeclsOk baseDecls h := by
  intro τr mname d hd
  -- Only `Integer` has declarations, and only three names on it, so the table
  -- lookup either pins `mname` or refutes `hd`.
  cases τr with
  | int =>
    by_cases h1 : mname = "+"
    · subst h1
      have : d = { params := [Ty.int], ret := Ty.int } := by
        simpa [declFor, tyClassNames, declOf?, declsFor, baseDecls] using hd.symm
      subst this
      exact Or.inl <| entryOk_int ht.1 (by decide) (by decide) run_int_add
        (fun _ _ _ => by simp [Builtins.deferTwin?, Builtins.reprDefer?,
          Builtins.coerceDefer?, Builtins.toAryDefer?, Builtins.num?])
    · by_cases h2 : mname = "-"
      · subst h2
        have : d = { params := [Ty.int], ret := Ty.int } := by
          simpa [declFor, tyClassNames, declOf?, declsFor, baseDecls] using hd.symm
        subst this
        exact Or.inl <| entryOk_int ht.2.1 (by decide) (by decide) run_int_sub
          (fun _ _ _ => by simp [Builtins.deferTwin?, Builtins.reprDefer?,
            Builtins.coerceDefer?, Builtins.toAryDefer?, Builtins.num?])
      · by_cases h3 : mname = "*"
        · subst h3
          have : d = { params := [Ty.int], ret := Ty.int } := by
            simpa [declFor, tyClassNames, declOf?, declsFor, baseDecls] using hd.symm
          subst this
          exact Or.inl <| entryOk_int ht.2.2.1 (by decide) (by decide) run_int_mul
            (fun _ _ _ => by simp [Builtins.deferTwin?, Builtins.reprDefer?,
              Builtins.coerceDefer?, Builtins.toAryDefer?, Builtins.num?])
        -- L152's nullary row, and the only line of this proof that differs in shape:
        -- the return type is `.bool` rather than the receiver's, so the witness has
        -- to say what a `.bool` value *is* (`hty`).
        · by_cases h4 : mname = "zero?"
          · subst h4
            have : d = { params := [], ret := Ty.bool } := by
              simpa [declFor, tyClassNames, declOf?, declsFor, baseDecls] using hd.symm
            subst this
            -- `f` is given explicitly: elaborating `hty` first would leave it an
            -- undetermined metavariable, since nothing in `ValueTy _ (f x) .bool`
            -- pins the function.
            exact Or.inl <| entryOk_int_nullary (f := fun x => .bool (x == 0))
              ht.2.2.2 (by decide) (by decide)
              (fun _ _ => rfl) run_int_zero
              (fun _ _ => by simp [Builtins.deferTwin?, Builtins.reprDefer?,
                Builtins.coerceDefer?, Builtins.toAryDefer?])
          · exact absurd hd (by
              simp [declFor, tyClassNames, declOf?, declsFor, baseDecls,
                show ("+" == mname) = false from by simp [Ne.symm h1],
                show ("-" == mname) = false from by simp [Ne.symm h2],
                show ("*" == mname) = false from by simp [Ne.symm h3],
                show ("zero?" == mname) = false from by simp [Ne.symm h4]])
  | bool =>
    exact absurd hd (by simp [declFor, tyClassNames, declOf?, declsFor, baseDecls])
  | nilT =>
    exact absurd hd (by simp [declFor, tyClassNames, declOf?, declsFor, baseDecls])
  | sym =>
    exact absurd hd (by simp [declFor, tyClassNames, declOf?, declsFor, baseDecls])
  -- The class arm (F1b): refuted by `declFor_baseDecls_cls` below — `baseDecls` has
  -- one key, `"Integer"`, and `tyClassNames` subtracts it from the class arm's
  -- range, so a class type has no declarations in the base table by construction.
  | cls n => exact absurd hd (by rw [declFor_baseDecls_cls]; simp)

end Static
end Proof
end RubyCore
