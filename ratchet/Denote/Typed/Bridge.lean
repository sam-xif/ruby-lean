import Denote.Typed.Derivations

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

The cases are one line each because `Denote/Typed/Derivations.lean` already has a
constructor-wise builder per rule, taking its premises at `DJudgeC dclinks`. This induction is
precisely "replace each `DJudge` constructor by its `derivD_*`".
-/

set_option autoImplicit false

namespace Ratchet.Denote.Typed

open RubyCore Ratchet Ratchet.Denote

/-! ## §1 The bridge, by mutual induction over the judgment and its list companions -/

mutual

/-- **Every syntactic derivation is a certified one.** The registry covers `DJudge`, so the
judgment `check` returns lands in the judgment `dregistry_safe` consumes. -/
theorem djudge_certified {Γ Γ' : Env} {e : Ratchet.Expr} {τ : Ty}
    (h : DJudge Γ e τ Γ') : (DJudgeC dclinks).judge Γ e τ Γ' := by
  cases h with
  | intLit => exact derivD_intLit
  | fltLit => exact derivD_fltLit
  | strLit => exact derivD_strLit
  | symLit => exact derivD_symLit
  | truLit => exact derivD_truLit
  | flsLit => exact derivD_flsLit
  | nilLit => exact derivD_nilLit
  | var hg ha => exact derivD_var hg ha
  | vasgn he hc ha => exact derivD_vasgn (djudge_certified he) hc ha
  | seq hs => exact derivD_seq (djudgeSeq_certified hs)
  | prim hr ha hp => exact derivD_prim (djudge_certified hr) (djudgeAll_certified ha) hp
  | if' hc ht he =>
      exact derivD_if (djudge_certified hc) (djudge_certified ht) (djudge_certified he)
  | ifNoElse hc ht => exact derivD_ifNoElse (djudge_certified hc) (djudge_certified ht)
  | bareName => exact derivD_bareName
  | arrayLit hs hf => exact derivD_arrayLit (djudgeAll_certified hs) hf
  | hashLit hs hk hv => exact derivD_hashLit (djudgePairs_certified hs) hk hv

/-- The argument-list companion. -/
theorem djudgeAll_certified {Γ Γ' : Env} {es : List Ratchet.Expr} {tys : List Ty}
    (h : DJudgeAll Γ es tys Γ') : (DJudgeC dclinks).all Γ es tys Γ' := by
  cases h with
  | nil => exact derivD_allNil
  | cons he ht hp => exact derivD_allCons (djudge_certified he) (djudgeAll_certified ht) hp

/-- The statement-sequence companion. -/
theorem djudgeSeq_certified {Γ Γ' : Env} {es : List Ratchet.Expr} {τ : Ty}
    (h : DJudgeSeq Γ es τ Γ') : (DJudgeC dclinks).seq Γ es τ Γ' := by
  cases h with
  | last he => exact derivD_seqLast (djudge_certified he)
  | cons he ht => exact derivD_seqCons (djudge_certified he) (djudgeSeq_certified ht)

/-- The pair-list companion follows the source's key/value evaluation order. -/
theorem djudgePairs_certified {Γ Γ' : Env} {ps : List (Ratchet.Expr × Ratchet.Expr)}
    {ks vs : List Ty} (h : DJudgePairs Γ ps ks vs Γ') :
    (DJudgeC dclinks).pairs Γ ps ks vs Γ' := by
  cases h with
  | nil => exact derivD_pairsNil
  | cons hk hv hs =>
    exact derivD_pairsCons (djudge_certified hk) (djudge_certified hv) (djudgePairs_certified hs)

end

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
  obtain ⟨_, _, hj⟩ := validateD_typed h
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
#print axioms validateD_safe
#print axioms validateD_safe_boot
#print axioms validateD_safe_run

end Ratchet.Denote.Typed
