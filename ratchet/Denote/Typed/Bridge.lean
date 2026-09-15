import Denote.Typed.Derivations
import Denote.Typed.InitBridge

/-!
# `Denote/Typed/Bridge.lean` — the syntactic judgment lands in the certified one

The one lemma that composes the ladder's two halves into a statement about the **checker**:

* `Ratchet/Check.lean`'s `validateD_typed` ends at `DJudge` — the syntactic inductive, which
  is what `check` returns and what the certificate is about;
* `Denote/Typed/Clink.lean`'s `dregistry_safe` starts at `DJudgeC dclinks` — the certified
  judgment, the one every registered clink closes.

Until now nothing joined them. The only bridge in the tree ran the *other* way
(`dregistry_syn : DJudgeC dclinks → DJudge`, which is `closed_source`), so "the checker
accepted it" and "it is safe" were two facts about each rung, glued per rung by hand in
`Denote/Typed/CorpusSafety.lean` and cross-checked by `semladder` at report time. §F32.

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

/-! ## §1 Six-family mutual induction, using the initializer pair's registry bridge -/

/-- **Every syntactic derivation is a certified one.** The registry covers `DJudge`, so the
judgment `check` returns lands in the judgment `dregistry_safe` consumes. -/
theorem djudge_certified {κ κ' : Ctx} {I I' : Ty} {Γ Γ' : Env} {e : Ratchet.Expr} {τ : Ty}
    (h : DJudge Γ e τ Γ' κ I κ' I') : (DJudgeC dclinks).judge Γ e τ Γ' κ I κ' I' := by
  intro F hF
  refine DJudge.rec
    (motive_1 := fun Γ e τ Γ' κ I κ' I' _ => F.judge Γ e τ Γ' κ I κ' I')
    (motive_2 := fun Γ es tys Γ' κ I κ' I' _ => F.all Γ es tys Γ' κ I κ' I')
    (motive_3 := fun Γ es τ Γ' κ I κ' I' _ => F.seq Γ es τ Γ' κ I κ' I')
    (motive_4 := fun Γ ps ks vs Γ' κ I κ' I' _ => F.pairs Γ ps ks vs Γ' κ I κ' I')
    (motive_5 := fun κ I s Γ e τ Γ' _ => F.recBody κ I s Γ e τ Γ')
    (motive_6 := fun κ I s Γ es tys Γ' _ => F.recArgs κ I s Γ es tys Γ')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals intros
  · apply hF DClink.intLit (by simp [dclinks]) <;> assumption
  · apply hF DClink.fltLit (by simp [dclinks]) <;> assumption
  · apply hF DClink.strLit (by simp [dclinks]) <;> assumption
  · apply hF DClink.symLit (by simp [dclinks]) <;> assumption
  · apply hF DClink.truLit (by simp [dclinks]) <;> assumption
  · apply hF DClink.flsLit (by simp [dclinks]) <;> assumption
  · apply hF DClink.nilLit (by simp [dclinks]) <;> assumption
  · apply hF DClink.var (by simp [dclinks]) <;> assumption
  · apply hF DClink.vasgn (by simp [dclinks]) <;> assumption
  · apply hF DClink.seq (by simp [dclinks]) <;> assumption
  · apply hF DClink.prim (by simp [dclinks]) <;> assumption
  · apply hF DClink.if' (by simp [dclinks]) <;> assumption
  · apply hF DClink.ifNoElse (by simp [dclinks]) <;> assumption
  · apply hF DClink.bareName (by simp [dclinks]) <;> assumption
  · apply hF DClink.arrayLit (by simp [dclinks]) <;> assumption
  · apply hF DClink.hashLit (by simp [dclinks]) <;> assumption
  · rename_i κd Γd Γb Id τd d ps hp hps ht hb hm hc hs hbl hco ha hi hg hf hmiss hquiet ihb
    exact hF DClink.defDecl (by simp [dclinks]) hp hps ht ihb
      hm hc hs hbl hco ha hi hg hf hmiss hquiet
  · apply hF DClink.callSig (by simp [dclinks]) <;> assumption
  · apply hF DClink.recursive (by simp [dclinks]) <;> assumption
  · exact hF DClink.ivarRead (by simp [dclinks])
  · apply hF DClink.constClass (by simp [dclinks]) <;> assumption
  · apply hF DClink.classDecl (by simp [dclinks]) <;> assumption
  · rename_i κd Γd Γb Id Ib τd c d ps hp hps hret hself hb hn hc hg ihb
    exact hF DClink.memberDef (by simp [dclinks]) hp hps hret hself ihb hn hc hg
  · rename_i κd Γd Γb Id Ib τd c d ps hn hp hps hret hout hb hc hg
    exact hF DClink.initDef (by simp [dclinks]) hn hp hps hret hout
      (initJudge_certified hb F hF) hc hg
  · rename_i κd κ₁ κ₂ Γd Γ₁ Γ₂ Γb Id I₁ I₂ Ib τd c d ps recv args
      hr ha hs hc hd hn hnew halloc hp hps hret hout hb hg ihr iha
    exact hF DClink.newInst (by simp [dclinks]) ihr iha hs hc hd hn hnew halloc hp hps
      hret hout (initJudge_certified hb F hF) hg
  · apply hF DClink.callMethodSig (by simp [dclinks]) <;> assumption
  · apply hF DClink.DJudgeAll.nil (by simp [dclinks]) <;> assumption
  · apply hF DClink.DJudgeAll.cons (by simp [dclinks]) <;> assumption
  · apply hF DClink.DJudgeSeq.last (by simp [dclinks]) <;> assumption
  · apply hF DClink.DJudgeSeq.cons (by simp [dclinks]) <;> assumption
  · apply hF DClink.DJudgePairs.nil (by simp [dclinks]) <;> assumption
  · apply hF DClink.DJudgePairs.cons (by simp [dclinks]) <;> assumption
  · apply hF DClink.DJudgeRec.embed (by simp [dclinks]) <;> assumption
  · apply hF DClink.DJudgeRec.prim (by simp [dclinks]) <;> assumption
  · apply hF DClink.DJudgeRec.if' (by simp [dclinks]) <;> assumption
  · apply hF DClink.DJudgeRec.selfCall (by simp [dclinks]) <;> assumption
  · apply hF DClink.DJudgeRecAll.nil (by simp [dclinks]) <;> assumption
  · apply hF DClink.DJudgeRecAll.cons (by simp [dclinks]) <;> assumption

/-- Fundamental lemma at arbitrary method contexts, not just the top-level specialization. -/
theorem djudge_context {κ κ' : Ctx} {I I' : Ty} {Γ Γ' : Env} {e : Ratchet.Expr} {τ : Ty}
    (h : DJudge Γ e τ Γ' κ I κ' I') : SemSafeCtxA κ Γ I e τ κ' Γ' I' :=
  dregistry_context (djudge_certified h)

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
      → DJudge [] p τ Γ'                     -- validateD_typed  (Ratchet/Check.lean)
      → (DJudgeC dclinks).judge [] p τ Γ'    -- djudge_certified (§1)
      → StuckFree m p                        -- dregistry_safe   (Denote/Typed/Clink.lean)

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
rung from and the one `Denote/Typed/CorpusSafety.lean`'s per-rung theorems are stated at.

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
#print axioms certified_context
#print axioms validateD_safe
#print axioms validateD_safe_boot
#print axioms validateD_safe_run

end Ratchet.Denote.Typed
