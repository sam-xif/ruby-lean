import RubyCore.Proof.StaticSoundness
import RubyCore.PreludeBoot
import RubyCore.HeapCert

/-!
# F0 — the static-soundness invariant at the **prelude-booted** heap

`homebrew/widening-the-fragment.md` §3/§4, `homebrew/PLAN.md` D7. The prerequisite
for every later rung of the static route, and the place it could have died.

`StaticSoundness.check_sound` is stated over `Machine.init p`, whose heap is
`Boot.initHeap` — **no core library**. `static-soundness-poc.md` §5 says such a
theorem "says nothing": with no prelude there is no `Comparable`, no `Enumerable`,
no `T`, and every Sorbet program dies on `NameError`. `sound_from` was written so
that the prelude-booted start would be *an instance rather than a restatement*,
and until this file **nobody had produced the instance**.

## What has to survive phase 1, and what cannot

`Inv` is four conjuncts (`Proof/Static/Konts.lean`): `TableOk`, `NoHook`,
`FramesOk`, `CtlOk`. Only the first two are about the heap, and only they can be
carried across the prelude's own execution:

* `CtlOk` **cannot hold during phase 1**. The prelude is 3,259 lines of exactly
  what `Types/Fragment.lean` excludes by design — 43 classes, 22 `define_method`,
  59 `yield` — so `infer` returns `none` on it and there is no environment to index
  the continuation stack by. This is why F0 is *heap-half* preservation and not
  "run the invariant through the boot".
* `FramesOk`/`CtlOk` at phase 2's start are re-established from scratch, exactly as
  in `initiation`: `initWithPrelude` builds a **fresh** toplevel frame
  (`Machine.initOn`) and carries over only `heap` and `globals`, neither of which
  `FramesOk` reads. That is `initiation_on` below, and it is why the heap half is
  the whole problem.

## Two routes to the heap half, and this file has both

`HeapOk` is **decidable** — it is two `lookup`s and a `crubyShadow` on a fixed
heap. What is *not* available is deciding it in the kernel: `Prelude.program` is
`Lean.Json.parse Prelude.json`, and `Lean.Json.parse` does not kernel-reduce even
on the input `"1"` (measured, §4), while L94 bans the `native_decide` escape. So:

1. **The certificate route** (§2, `inv_of_cert`). Reflect `HeapOk` into a `Bool`
   and prove the reflection sound. The hypothesis of the theorem is then
   `heapOkB m₀.heap = true` — *one Bool about the machine actually in hand*, which
   `scripts/heapok_probe.lean` computes and `scripts/check-proofs.sh` fails on.
   Nothing is assumed about the prelude's text or its steps.
2. **The preservation route** (§3, `heapOk_boot`). Carry the heap half across
   arbitrary steps of phase 1 and hand off at the phase boundary, reducing
   `HeapOk` at the booted heap to a **per-step** obligation `PreservesHeapOk`.
   That obligation is the honest residue: it is left as an explicit hypothesis
   rather than an `axiom`, per the D8 discipline that *a trusted assumption must
   be an artifact, not a residue*. `TableOk_defineMethod` is already its
   `defineMethod` case; the other sixteen heap-writing sites in `Interp/` are the
   work that discharges it.

Both end at the same theorem, `sound_from`, unchanged — which is the payoff of it
having been stated over an arbitrary `m₀` in the first place.

**Measured, 2026-08-15:** `HeapOk` *does* hold at the prelude-booted heap
(`scripts/heapok_probe.lean`: all three `Integer` builtins resolve as tabulated —
public, live, not `fromPrelude`, unshadowed — and `Object` has no `method_added`).
So F0 is not where D6 dies.
-/

namespace RubyCore
namespace Proof
namespace Static

open Interp
open RubyCore.Types

-- `heapOk_initHeap`'s `TableOk` half walks the whole boot method table, exactly as
-- `tableOk_initHeap` does.
set_option maxRecDepth 100000

/-! ## 1. The heap half of the invariant -/

/-- The conjuncts of `Inv` that are facts about the heap alone, hence the only ones
    that can be carried across phase 1. **Three since L148**: `Saturated` joined
    `TableOk` and `NoHook` when the invariant started needing it for `DeclsOk_grow`,
    and it belongs here for the same reason the other two do — it is a fact about the
    heap, decided by the same certificate, at the same point. -/
def HeapOk (h : Heap) : Prop :=
  TableOk h ∧ NoHook h ∧ Saturated h ∧ LitClsOk h ∧ ClassOk h

/-- The bare boot heap satisfies it — `TableOk` by `tableOk_initHeap`'s walk of
    the method table, `NoHook` by `rfl`, and `Saturated` by `decide`: the boot heap is
    a *literal*, so unlike at the prelude-booted heap the walk's saturation really is
    a kernel computation. This is the *start* of phase 1, not its end; the whole
    difficulty of F0 is the other end. -/
theorem heapOk_initHeap : HeapOk Boot.initHeap :=
  ⟨tableOk_initHeap, noHookB_sound (by decide), saturatedB_sound (by decide),
   ⟨⟨by decide, by rfl⟩, ⟨by decide, by rfl⟩⟩, classOkB_sound (by decide)⟩

/-! ### 1.1 Initiation at an arbitrary heap

`initiation` generalizes to *any* heap satisfying the heap half, with the frames
and control halves re-established exactly as before: they read `frames`, `stack`,
`kont` and `ctl`, all of which `Machine.initOn` builds fresh, and none of which
depends on the heap. `globals` is quantified over because `initWithPrelude`
carries phase 1's globals into phase 2 and `Inv` does not mention them.
-/

theorem initiation_on {p : Expr} {h : Heap} {g : List (String × Value)}
    (hchk : check p = .accept) (hh : HeapOk h) :
    Inv { Machine.initOn h p with globals := g } := by
  -- F1a: the invariant's heap clause is `DeclsOk`, and `HeapOk`'s `TableOk` half
  -- is its concrete witness for `baseDecls`. That is the whole reason F0 needed no
  -- restatement — `heapOkB` still decides exactly what it decided before.
  -- L155's sixth conjunct is heap-independent, so it comes out the same here as at
  -- `Machine.init`: `initOn` builds one frame and it is the toplevel one.
  refine ⟨hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2,
    (by simp [Machine.initOn, BottomObj]),
    -- F1b.8: the table is existential in `Inv`, and `declsOf p` is what pins it at
    -- the start of the run — the same instantiation `initiation` makes, at a heap
    -- the certificate rather than the kernel vouches for.
    (by simp [Machine.initOn, frameKLabels]),
    declsOf p, { cls := "Object" }, [], [],
    tableOk_declsOk hh.1 hh.2.2.2.2, ?_, ?_, ?_, ?_⟩
  · show FramesOk _ _ _ ([] :: [])
    -- L154: the toplevel frame's definee has to be a *class*, and at an arbitrary
    -- heap that is not decidable — it is `NoHook`'s first conjunct, which is exactly
    -- what that conjunct is for.
    simp [Machine.initOn, FramesOk, FrameConforms, envGet?]
    exact hh.2.1.1
  · -- F1b.9: the outermost activation's context is `"Object"`. The `isSome` half is
    -- `NoHook`'s first conjunct, as it is for `FrameConforms` above; the *name* half
    -- is `ClassOk`'s new clause, which is why that clause is folded into `ClassOk`
    -- rather than being a seventh conjunct — the certificate already decides it.
    show StackCtx _ _ _ ({ cls := "Object" } :: [])
    -- L189's cref clause: `initOn` sets `cref := [Boot.objectId]`, so it is a
    -- computation on the frame literal whatever the heap is.
    exact ⟨hh.2.1.1, hh.2.2.2.2.1, fun hz => absurd rfl hz,
      fun sc hsc => absurd hsc (by simp),
      by simp [Machine.initOn, Array.getD], Or.inr rfl,
      fun mn h => absurd h (by simp), trivial⟩
  · -- **L228: the globals conjunct**, and here — unlike at `Machine.init` — the list is
    -- *quantified*, because `initWithPrelude` carries phase 1's globals into phase 2. So
    -- it is not vacuous, and what discharges it is `declsOf p`: the checker's own table
    -- declares no global, so the lookup is `none` at every name.
    intro x pr σ _ _ hd
    exact absurd hd (by simp [declsOf, baseDecls, globalTy?])
  · unfold check at hchk
    show CtlOk (declsOf p) { cls := "Object" } [] [] _
    unfold CtlOk
    split at hchk
    · rename_i r hr
      obtain ⟨τ, Γ', D'⟩ := r
      exact ⟨τ, τ, Γ', D', hr, by simp, KontOk.nil (by simp) (by simp)⟩
    · exact absurd hchk (by split <;> simp)

/-! ## 2. The certificate route

`HeapOk` reflected into a `Bool`, with the reflection proved sound. The point of
the reflection is *not* to decide the property in the kernel — §4's measurement
rules that out — but to make the hypothesis of the theorem something the running
executable can establish and act on: one `Bool`, on the heap in hand, checked
outside the kernel.

`intResolvesB`/`heapOkB` themselves live in `RubyCore/HeapCert.lean`, outside
`Proof/`, so that `scripts/heapok_probe.lean` computes *the* predicate these
lemmas are about rather than a copy of it.
-/

theorem intResolvesB_sound {h : Heap} {mname bid : String}
    (hb : intResolvesB h mname bid = true) : IntBuiltinResolves h mname bid := by
  unfold intResolvesB at hb
  cases hl : lookup h (.int 0) mname with
  | none => rw [hl] at hb; exact absurd hb (by simp)
  | some p =>
    obtain ⟨owner, md⟩ := p
    rw [hl] at hb
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Option.isNone_iff_eq_none] at hb
    obtain ⟨⟨⟨⟨hbid, hu⟩, hvis⟩, hpre⟩, hsh⟩ := hb
    exact ⟨owner, md, hl, hbid, hu, hvis, hpre, hsh⟩

theorem heapOkB_sound {h : Heap} (hb : heapOkB h = true) : HeapOk h := by
  unfold heapOkB at hb
  simp only [Bool.and_eq_true] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, hz⟩, hnh⟩, h5⟩, h6⟩, h7⟩, h6a⟩, h7a⟩, h8⟩ := hb
  exact ⟨⟨intResolvesB_sound h1, intResolvesB_sound h2, intResolvesB_sound h3,
      intResolvesB_sound hz⟩,
    noHookB_sound hnh, saturatedB_sound h5,
    ⟨⟨h6, by simpa using h7⟩, ⟨h6a, by simpa using h7a⟩⟩, classOkB_sound h8⟩

/-- **F0, certificate form.** A checked `Bool` about the machine in hand plus an
    accepting `check` gives the invariant — for *any* start configuration, so in
    particular for the prelude-booted one. -/
theorem inv_of_cert {p : Expr} {h : Heap} {g : List (String × Value)}
    (hchk : check p = .accept) (hcert : heapOkB h = true) :
    Inv { Machine.initOn h p with globals := g } :=
  initiation_on hchk (heapOkB_sound hcert)

/-- **F0's headline, certificate form.** Static soundness for a program running
    on the heap the interpreter really starts from, conditional on one Bool the
    interpreter itself checks. Note `sound_from` is reused *unchanged*. -/
theorem check_sound_on {p : Expr} {h : Heap} {g : List (String × Value)}
    (hchk : check p = .accept) (hcert : heapOkB h = true) :
    ∀ r, ReachableResult { Machine.initOn h p with globals := g } r → ¬ typeStuck r :=
  sound_from (inv_of_cert hchk hcert)

/-- The same, phrased over `initWithPrelude` so the starting configuration is
    literally the one `Main.lean:132` runs. -/
theorem check_sound_withPrelude {p : Expr} {m₀ : Machine}
    (hchk : check p = .accept) (hb : Prelude.initWithPrelude p = .ok m₀)
    (hcert : heapOkB m₀.heap = true) :
    ∀ r, ReachableResult m₀ r → ¬ typeStuck r := by
  -- `initWithPrelude` *is* `{ Machine.initOn mp.heap p with globals := mp.globals }`,
  -- so the certificate form applies once the boot's `Except` is inverted.
  unfold Prelude.initWithPrelude at hb
  cases hboot : Prelude.boot with
  | error e => rw [hboot] at hb; simp [Except.map] at hb
  | ok mp =>
    rw [hboot] at hb
    simp only [Except.map, Except.ok.injEq] at hb
    subst hb
    exact check_sound_on hchk hcert

/-- **D12's headline, and the reason making the verdict total costs nothing.**
    The same theorem as `check_sound_withPrelude`, stated over the *reported*
    decision: an `accept` from `decisionOf` licenses type-safety-by-reachability
    at the heap the interpreter really starts from.

    Read what is *not* here, because it is the content of D12: there is no
    theorem about `reject`, and none is wanted. `reject` says the checker did not
    certify the program — a claim about the checker, not about the program — so
    the asymmetry that makes the decision total is the same asymmetry that keeps
    it sound. -/
theorem decision_sound_withPrelude {p : Expr} {m₀ : Machine}
    (hchk : (Types.decisionOf p).1 = .accept)
    (hb : Prelude.initWithPrelude p = .ok m₀)
    (hcert : heapOkB m₀.heap = true) :
    ∀ r, ReachableResult m₀ r → ¬ typeStuck r :=
  check_sound_withPrelude ((Types.decision_accept_iff p).mp hchk) hb hcert

/-! ## 3. The preservation route

The heap half carried across arbitrary steps of phase 1, with the hand-off at the
phase boundary. This is the route `widening-the-fragment.md` §4 recommends, and
what it buys over §2 is that nothing is checked at runtime: the residue is a
**per-step** obligation, which is where the existing `defineMethod` chain
(`Proof/HeapFacts.lean`) already applies.

`.done` is admitted alongside `.next` because the boot's final step is one:
`applyKont` on an empty continuation stack answers `.done v m` (`Interp/Kont.lean:20`),
and `run` reports that machine as the booted heap. Including it here is what lets
§3.1's induction avoid inverting `stepFn`.
-/

/-- One step preserves the heap half. Stated over the *step results that carry a
    machine forward* — `.next` during the boot, `.done` at its end. -/
def PreservesHeapOk (m : Machine) : Prop :=
  HeapOk m.heap → ∀ m', (stepFn m = .next m' ∨ ∃ v, stepFn m = .done v m') →
    HeapOk m'.heap

/-- The `def` case, for the record: it is `TableOk_defineMethod` plus the hook
    lookup, and it is the only one of the seventeen heap-writing sites in
    `Interp/` that is already proved. The other sixteen are F0's remaining work
    (`Interp.lean:238,279`, `Interp/Dispatch.lean:173,509,526,540,571,572`,
    `Interp/Kont.lean:103,490`, `Interp/Reflect.lean:87,193,200,310,317,359`,
    `Builtins/Modules.lean:183`). -/
theorem heapOk_defineMethod {h : Heap} {cls : ObjId} {name : String}
    {md : MethodDef} (hh : HeapOk h)
    (h1 : ¬ (name = "+")) (h2 : ¬ (name = "-")) (h3 : ¬ (name = "*"))
    (h4 : ¬ ("method_added" = name)) (h5 : ¬ (name = "zero?")) :
    HeapOk (defineMethod h cls name md) :=
  ⟨TableOk_defineMethod hh.1 h1 h2 h3 h5,
   NoHook_defineMethod hh.2.1 h4,
   -- L148's third clause, and it needs no side condition: a method-table write moves
   -- no id, so the walk cannot become fuel-sensitive.
   Saturated_defineMethod hh.2.2.1 cls name md,
   -- L151's fourth, and the same argument once more: `setClassPayload` rewrites the
   -- method table and leaves the payload a `.cls` with the name it had.
   LitClsOk_defineMethod hh.2.2.2.1,
   -- L156's, and the case that makes it worth stating: a `def` in the body of
   -- the very class being reopened. `constOwn` reads `consts`; `defineMethod` writes
   -- `methods`.
   ClassOk_defineMethod hh.2.2.2.2⟩

/-! ### 3.1 Carrying it along a run -/

/-- The heap half survives a whole `run`, given per-step preservation at every
    configuration that run reaches. The hypothesis is re-based at each step via
    `Reaches.head`, so it never has to be strengthened to *all* machines — which
    would be false, since a program may reopen `Integer` and redefine `+`. -/
theorem run_heapOk {fuel : Nat} {m₀ : Machine} {v : Value} {mf : Machine}
    (hrun : run fuel m₀ = .value v mf) (h0 : HeapOk m₀.heap)
    (hp : ∀ m, Reaches m₀ m → PreservesHeapOk m) : HeapOk mf.heap := by
  induction fuel generalizing m₀ with
  | zero => simp [run] at hrun
  | succ n ih =>
    rw [run] at hrun
    cases hs : stepFn m₀ with
    | next m' =>
      rw [hs] at hrun
      exact ih hrun (hp m₀ .refl h0 m' (.inl hs))
        (fun m hr => hp m (Reaches.head hs hr))
    | done v' m' =>
      rw [hs] at hrun
      simp only [Interp.RunResult.value.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      exact hp m₀ .refl h0 _ (.inr ⟨v', hs⟩)
    | uncaught e m' => rw [hs] at hrun; exact absurd hrun (by simp)
    | unsupported r => rw [hs] at hrun; exact absurd hrun (by simp)
    | stuck msg => rw [hs] at hrun; exact absurd hrun (by simp)

/-- Phase 1's start configuration, named so the preservation hypothesis can be
    quantified over the machines it reaches rather than over all machines. -/
def bootStart (p : Expr) : Machine := { Machine.init p with preludeMode := true }

/-- **F0, preservation form.** The booted heap satisfies the heap half, given
    per-step preservation across phase 1. Nothing is decided in the kernel and
    nothing is checked at runtime; the residue is `hp`. -/
theorem heapOk_boot {mp : Machine} (hb : Prelude.boot = .ok mp)
    (hp : ∀ p, Prelude.program = .ok p →
      ∀ m, Reaches (bootStart p) m → PreservesHeapOk m) :
    HeapOk mp.heap := by
  -- `rw [← hstart]` rather than unfolding `bootStart`: the boot's own term is the
  -- structure-update literal, so rewriting *it* into the named form is what lets
  -- `cases hr : run … (bootStart p)` land syntactically in `hb`.
  unfold Prelude.boot at hb
  cases hprog : Prelude.program with
  | error e => rw [hprog] at hb; simp at hb
  | ok p =>
    rw [hprog] at hb
    dsimp only at hb
    rw [show ({ Machine.init p with preludeMode := true } : Machine) = bootStart p from rfl] at hb
    cases hr : run Prelude.bootFuel (bootStart p) with
    | value v m =>
      rw [hr] at hb
      simp only [Except.ok.injEq] at hb
      subst hb
      exact run_heapOk hr heapOk_initHeap (hp p hprog)
    | uncaught e m => rw [hr] at hb; simp at hb
    | unsupported r m => rw [hr] at hb; simp at hb
    | outOfFuel m => rw [hr] at hb; simp at hb
    | stuck msg m => rw [hr] at hb; simp at hb

/-- **F0's headline, preservation form.** Static soundness for a program on the
    prelude-booted heap, with no runtime certificate: the only residue is
    per-step heap-half preservation across the prelude's own execution. -/
theorem check_sound_withPrelude' {p : Expr} {m₀ : Machine}
    (hchk : check p = .accept) (hb : Prelude.initWithPrelude p = .ok m₀)
    (hp : ∀ q, Prelude.program = .ok q →
      ∀ m, Reaches (bootStart q) m → PreservesHeapOk m) :
    ∀ r, ReachableResult m₀ r → ¬ typeStuck r := by
  unfold Prelude.initWithPrelude at hb
  cases hboot : Prelude.boot with
  | error e => rw [hboot] at hb; simp [Except.map] at hb
  | ok mp =>
    rw [hboot] at hb
    simp only [Except.map, Except.ok.injEq] at hb
    subst hb
    exact sound_from (initiation_on hchk (heapOk_boot hboot hp))

/-! ## 4. Axiom hygiene

Both routes inherit `sound_from`'s baseline. The certificate route's `Bool` is
*not* discharged by `native_decide` here — it is a hypothesis, so no
`ofReduceBool` appears; discharging it is the executable's job (L94's rule is
that the Lean compiler must not get into the trust base of a metatheorem, and a
hypothesis the harness checks at boot is not the compiler proving anything).
-/

/-- info: 'RubyCore.Proof.Static.check_sound_withPrelude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms check_sound_withPrelude

/-- info: 'RubyCore.Proof.Static.check_sound_withPrelude'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms check_sound_withPrelude'

/-- info: 'RubyCore.Proof.Static.decision_sound_withPrelude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decision_sound_withPrelude

end Static
end Proof
end RubyCore
