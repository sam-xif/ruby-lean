import Denote.Examples.Derivations
import Denote.Clink.Certify
import Denote.Sem.Closure.Dispatch

/-!
# `Denote/Bridge.lean` — the syntactic judgment lands in the certified one

The one lemma that composes the ladder's two halves into a statement about the **checker**:

* `Ratchet/Check/Check.lean`'s `validateD_typed` ends at `DJudge` — the syntactic inductive, which
  is what `check` returns and what the certificate is about;
* `Denote/Clink/Registry.lean`'s `dregistry_safe` starts at `DJudgeC dclinks` — the certified
  judgment, the one every registered clink closes.

Until now nothing joined them. The only bridge in the tree ran the *other* way
(`dregistry_syn : DJudgeC dclinks → DJudge`, which is `closed_source`), so "the checker
accepted it" and "it is safe" were two facts about each rung, glued per rung by hand in
`Denote/Examples/CorpusSafety.lean` and cross-checked by `semladder` at report time. §F32.

## Why this direction is a theorem now and was not before

`djudge_certified` is a completeness statement about the **registry**: every `DJudge`
constructor has a clink to discharge its case. That is exactly `dUnregisteredRules = []`, and
it became true only when `seq`, `prim`, `if'` and the four list companions were registered.
Before that, three cases of this induction had nothing to close them.

So the lemma is self-gating, and that is its second job: **it cannot compile if a rule is
added to `DJudge` without a semantic proof.** A new constructor is a new case, and the case
needs a `derivD_*` builder, which needs a clink, which needs `SemA.<rule>`. The `#guard` in
`Clink.lean` says the same thing as a `Bool`; this says it as a proof obligation.

## Why the bridge, rather than making `check` return a `DJudgeC` derivation

Both close §F32. The bridge keeps the syntactic world ignorant of the semantic one:
`Ratchet/` still mentions no `Denote/`, `check` still returns the plain inductive, and
`DJudgeC dclinks` quantifies over **every** `DFam` closed under the clinks. So a second
semantic backend — a different `dsemFam`, a different notion of "safe" — reuses this lemma
unchanged and needs no new bridge. Threading `DJudgeC` through the checker would have fixed
one target into the checker's return type and made the second backend a rewrite.

The mutual recursor replaces each constructor with its registered rule, including list and
scoped recursive families. Induction is on the derivation, not expression size: a call's stored body
need not be smaller than the call. The list induction hypotheses stay inside this proof.
-/

set_option autoImplicit false

namespace Ratchet.Denote.Typed

open RubyCore Ratchet Ratchet.Denote

/-! ## §1 Twelve-family mutual induction, using the initializer registry bridge -/

/-- **Every syntactic derivation is a certified one.** The registry covers `DJudge`, so the
judgment `check` returns lands in the judgment `dregistry_safe` consumes. -/
theorem djudge_certified {κ κ' : Ctx} {I I' : Ty} {Γ Γ' : Env} {e : Ratchet.Expr} {τ : Ty}
    (h : DJudge Γ e τ Γ' κ I κ' I') : (DJudgeC dclinks).judge Γ e τ Γ' κ I κ' I' := by
  intro F hF
  certify_djudgments DJudge.rec h F hF

/-- Callback methods cross the same registry, uniformly over the entire declared signature. -/
theorem dmethod_certified {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret τ : Ty}
    {Γ Γ' : Env} {e : Ratchet.Expr} (h : DMethod κ I fr ps ret Γ e τ Γ') :
    (DJudgeC dclinks).method κ I fr ps ret Γ e τ Γ' := by
  intro F hF
  certify_djudgments DMethod.rec h F hF

/-- Fundamental lemma at arbitrary method contexts, not just the top-level specialization. -/
theorem djudge_context {κ κ' : Ctx} {I I' : Ty} {Γ Γ' : Env} {e : Ratchet.Expr} {τ : Ty}
    (h : DJudge Γ e τ Γ' κ I κ' I') : SemSafeCtxA κ Γ I e τ κ' Γ' I' :=
  dregistry_context (djudge_certified h)

/-- Every registered rule proves the strengthened escape contract, including checked
method bodies at arbitrary contexts. Untyped block-control escapes are impossible. -/
theorem djudge_escape_only_raise {κ κ' : Ctx} {I I' : Ty} {Γ Γ' : Env}
    {e : Ratchet.Expr} {τ : Ty} (h : DJudge Γ e τ Γ' κ I κ' I')
    {m n : Machine} (hm : StateOk κ Γ I m) {fuel rest : Nat} {j : Jump}
    (hr : runA fuel (evalFrom m e) = .ans (.esc j) n rest) :
    ∃ exc, j = .raiseJ exc ∧ Semantics.isTypeError n.heap exc = false :=
  (((djudge_context h) m hm).2 fuel (.esc j) n rest hr).2.1.only_raise

/-- Every certified evaluation retains existing Proc descriptors, including a receiver
saved before evaluating arguments. Captured frame contents are a separate obligation. -/
theorem djudge_saved_proc {κ κ' : Ctx} {I I' : Ty} {Γ Γ' : Env}
    {e : Ratchet.Expr} {τ : Ty} (h : DJudge Γ e τ Γ' κ I κ' I')
    {m n : Machine} (hm : StateOk κ Γ I m) {fuel rest : Nat} {a : Answer}
    {v : Value} {cl : Closure} (hp : procClosure? m.heap v = some cl)
    (hr : runA fuel (evalFrom m e) = .ans a n rest) :
    procClosure? n.heap v = some cl :=
  (((djudge_context h) m hm).2 fuel a n rest hr).1.procs.payload v cl hp

/-- A saved Proc's dispatch class also survives argument/body evaluation. Retaining
its payload or nominal Proc type alone would not establish this equality. -/
theorem djudge_saved_proc_dispatch {κ κ' : Ctx} {I I' : Ty} {Γ Γ' : Env}
    {e : Ratchet.Expr} {τ : Ty} (h : DJudge Γ e τ Γ' κ I κ' I')
    {m n : Machine} (hm : StateOk κ Γ I m) {fuel rest : Nat} {a : Answer}
    {v : Value} {cl : Closure} (hp : procClosure? m.heap v = some cl)
    (hr : runA fuel (evalFrom m e) = .ans a n rest) :
    classOf n.heap v = classOf m.heap v :=
  (((djudge_context h) m hm).2 fuel a n rest hr).1.procs.dispatch v cl hp

/-- Every certified answer preserves prelude-loading mode, including bodies whose
runtime activation permissions were dropped at captured entry. -/
theorem djudge_phase {κ κ' : Ctx} {I I' : Ty} {Γ Γ' : Env} {e : Ratchet.Expr} {τ : Ty}
    (h : DJudge Γ e τ Γ' κ I κ' I') {m n : Machine} (hm : StateOk κ Γ I m)
    {fuel rest : Nat} {a : Answer} (hr : runA fuel (evalFrom m e) = .ans a n rest) :
    n.preludeMode = m.preludeMode :=
  (((djudge_context h) m hm).2 fuel a n rest hr).1.phase

/-- Certified evaluation retains every old binding and preserves the exact binding
domain of each saved frame, even when captured writes change its values. -/
theorem djudge_bindings {κ κ' : Ctx} {I I' : Ty} {Γ Γ' : Env} {e : Ratchet.Expr} {τ : Ty}
    (h : DJudge Γ e τ Γ' κ I κ' I') {m n : Machine} (hm : StateOk κ Γ I m)
    {fuel rest : Nat} {a : Answer} (hr : runA fuel (evalFrom m e) = .ans a n rest) :
    BindingsPres m n :=
  (((djudge_context h) m hm).2 fuel a n rest hr).1.frames.bindings

/-- Existing lookup owners survive every certified answer within the source fuel
budget, provided the source capture chain is live. -/
theorem djudge_owners {κ κ' : Ctx} {I I' : Ty} {Γ Γ' : Env} {e : Ratchet.Expr} {τ : Ty}
    (h : DJudge Γ e τ Γ' κ I κ' I') {m n : Machine} (hm : StateOk κ Γ I m)
    {fuel rest : Nat} {a : Answer} (hr : runA fuel (evalFrom m e) = .ans a n rest) :
    OwnersPres m n :=
  (((djudge_context h) m hm).2 fuel a n rest hr).1.frames.owners

/-- An initially bound active local protects every saved same-named slot, even when
the active frame captures its caller. Parameter types therefore cannot overwrite caller types. -/
theorem djudge_shadows {κ κ' : Ctx} {I I' : Ty} {Γ Γ' : Env} {e : Ratchet.Expr} {τ : Ty}
    (h : DJudge Γ e τ Γ' κ I κ' I') {m n : Machine} (hm : StateOk κ Γ I m)
    {fuel rest : Nat} {a : Answer} (hr : runA fuel (evalFrom m e) = .ans a n rest) :
    ShadowPres m n :=
  (((djudge_context h) m hm).2 fuel a n rest hr).1.frames.shadows

/-- Every checked value state retains native Proc dispatch while call is unreserved.
A declaration that reserves the selector removes this capability instead of carrying
an assumption about the old method table past a possible write. -/
theorem djudge_proc_call {κ κ' : Ctx} {I I' : Ty} {Γ Γ' : Env} {e : Ratchet.Expr} {τ : Ty}
    (h : DJudge Γ e τ Γ' κ I κ' I') (hf : nameFreeN κ' "call" = true)
    {m n : Machine} (hm : StateOk κ Γ I m) {fuel rest : Nat} {v : Value}
    (hr : runA fuel (evalFrom m e) = .ans (.val v) n rest) : ProcCallReady n.heap :=
  ((((djudge_context h) m hm).2 fuel (.val v) n rest hr).2.2 v rfl).procCall hf

/-- A checker result carries the generic semantic contract, including a method frame. -/
theorem certified_context {κ : Ctx} {I : Ty} {Γ : Env} {e : Ratchet.Expr}
    (c : Certified Γ e κ I) : SemSafeCtxA κ Γ I e c.ty c.ctx c.out c.spine :=
  djudge_context c.judged

theorem certified_safe {κ : Ctx} {I : Ty} {Γ : Env} {e : Ratchet.Expr}
    (c : Certified Γ e κ I) {m : Machine} (hm : StateOk κ Γ I m) : StuckFree m e :=
  (certified_context c).closed hm

/-- An annotation-based body derivation crosses the same registry as whole programs. -/
theorem annotated_add_judgment {κ : Ctx} {I : Ty} (hf : nameFreeN κ "+" = true) :
    DJudge [("x", .int), ("y", .int)]
      (.send (some (.var .lvar "x")) "+" [.var .lvar "y"] none)
      .int [("x", .int), ("y", .int)] κ I :=
  .prim (.var rfl rfl) (.cons (.var rfl rfl) .nil rfl) .intAdd hf (by intro h; cases h)

example {κ : Ctx} {I : Ty} (hf : nameFreeN κ "+" = true) :
    SemSafeCtxA κ [("x", .int), ("y", .int)] I
      (.send (some (.var .lvar "x")) "+" [.var .lvar "y"] none)
      .int κ [("x", .int), ("y", .int)] I := djudge_context (annotated_add_judgment hf)

/-! ## §2 …and therefore the checker's `Bool` is an end-to-end safety claim

The three theorems this composes were each on file; nothing here is new work beyond §1.
What is new is that the hypothesis is **`validateD`** — the thing the untrusted pipeline
actually produces a certificate for — rather than a `DJudgeC` derivation someone wrote by
hand to match a rung.

    validateD p d = true                     -- the checker accepted the certificate
      → DJudge [] p τ Γ'                     -- validateD_typed  (Ratchet/Check/Check.lean)
      → (DJudgeC dclinks).judge [] p τ Γ'    -- djudge_certified (§1)
      → StuckFree m p                        -- dregistry_safe   (Denote/Clink/Registry.lean)

Stated first at **any** conformant machine, because that is the reusable form and the boot
machine is one instance of it. -/

/-- **The end-to-end theorem.** If the checker accepts a certificate for `p`, then running `p`
from any conformant machine never reaches a type-stuck outcome — at any fuel, whether it
returns, escapes, diverges or gates. -/
theorem validateD_safe {p : Ratchet.Expr} {d : Deriv} (h : validateD p d = true)
    {m : Machine} (hm : StateOk Ratchet.ctx0 [] .ivar0 m) : StuckFree m p := by
  obtain ⟨_, _, _, _, hj⟩ := validateD_typed h
  exact dregistry_safe (djudge_certified hj) hm

/-- …at the **fresh prelude-booted machine**, which is the one the difftest harness runs a
rung from and the one `Denote/Examples/CorpusSafety.lean`'s per-rung theorems are stated at.

This is the statement the ladder exists to produce, and the corpus rungs are now instances of
it rather than eight-and-then-thirty-two separate facts: `validateD` accepting a rung *is* the
safety claim for that rung. -/
theorem validateD_safe_boot {p : Ratchet.Expr} {d : Deriv} (h : validateD p d = true)
    (hb : bootOkB = true) : StuckFree bootMachine p :=
  validateD_safe h (stateOk_boot hb)

/-- The executable ratchet runner, not just a separately named initial machine.
On boot failure the runner reports Unsupported; on success the initial states agree. -/
theorem validateD_safe_run {p : Ratchet.Expr} {d : Deriv} (h : validateD p d = true)
    (hb : bootOkB = true) (fuel : Nat) :
    Semantics.typeStuck (Semantics.run fuel (toRuby p)) = false := by
  have hs := validateD_safe_boot h hb fuel
  cases hboot : Semantics.bootedMachine with
  | error msg => simp only [Semantics.run, hboot, Semantics.typeStuck]
  | ok m => simpa only [Semantics.run, bootMachine, hboot, evalFrom, Machine.initOn] using hs

#print axioms djudge_certified
#print axioms djudge_context
#print axioms djudge_escape_only_raise
#print axioms djudge_saved_proc
#print axioms djudge_saved_proc_dispatch
#print axioms djudge_phase
#print axioms djudge_bindings
#print axioms djudge_owners
#print axioms djudge_shadows
#print axioms djudge_proc_call
#print axioms certified_context
#print axioms validateD_safe
#print axioms validateD_safe_boot
#print axioms validateD_safe_run

end Ratchet.Denote.Typed
