import RubyCore.Proof.Static.Konts

/-!
# P0 static soundness, part 3 — progress and preservation in one case analysis

§3 of `Proof/StaticSoundness.lean` before the L136 split. `StepOk` bundles both
obligations so the 48-way `Kont` split and the ~40-way `Expr` split are each
walked **once**: `.next` carries preservation, `.done` is a legitimate halt, and
every remaining `StepResult` — crucially `.uncaught` — is `False`, which is
exactly progress.
-/

namespace RubyCore
namespace Proof
namespace Static

open Interp
open RubyCore.Types

set_option maxRecDepth 100000

/-! ## 3. Progress and preservation, in one case analysis

`StepOk` bundles both obligations so the 48-way `Kont` split and the ~40-way
`Expr` split are each walked **once**: `.next` carries preservation, `.done` is
a legitimate halt, and every remaining `StepResult` — crucially `.uncaught` —
is `False`, which is exactly progress.
-/

def StepOk (D : Decls) : StepResult → Prop
  | .next m' => Inv D m'
  | .done _ _ => True
  | _ => False

theorem step_ok {D : Decls} {m : Machine} (h : Inv D m) : StepOk D (stepFn m) := by
  obtain ⟨htab, hhook, Γ, Γs, hfs, hc⟩ := h
  have hf : FrameOk m := hfs.frameOk
  have hl : LocalsOk Γ m := hfs.localsOk
  unfold CtlOk at hc
  rcases hctl : m.ctl with e | v | j
  · -- ## control = eval e
    rw [hctl] at hc
    obtain ⟨τ, Γ', hinf, hk⟩ := hc
    simp only [stepFn, hctl]
    cases e <;> try (simp only [infer] at hinf; contradiction)
    case int n =>
      simp only [infer, Option.some.injEq, Prod.mk.injEq] at hinf
      obtain ⟨rfl, rfl⟩ := hinf
      exact inv_value hfs htab hhook rfl hk
    case tru =>
      simp only [infer, Option.some.injEq, Prod.mk.injEq] at hinf
      obtain ⟨rfl, rfl⟩ := hinf
      exact inv_value hfs htab hhook rfl hk
    case fls =>
      simp only [infer, Option.some.injEq, Prod.mk.injEq] at hinf
      obtain ⟨rfl, rfl⟩ := hinf
      exact inv_value hfs htab hhook rfl hk
    case nil =>
      simp only [infer, Option.some.injEq, Prod.mk.injEq] at hinf
      obtain ⟨rfl, rfl⟩ := hinf
      exact inv_value hfs htab hhook rfl hk
    case var k x =>
      cases k
      case lvar =>
        simp only [infer, Option.map_eq_some_iff] at hinf
        obtain ⟨σ, hg, heq⟩ := hinf
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact inv_value hfs htab hhook (hl x _ hg) hk
      all_goals (simp only [infer] at hinf; contradiction)
    case vasgn k x rhs =>
      cases k
      case lvar =>
        simp only [infer] at hinf
        split at hinf
        · rename_i σ Γ₁ hrhs
          simp only [Option.some.injEq, Prod.mk.injEq] at hinf
          obtain ⟨rfl, rfl⟩ := hinf
          exact inv_push hfs htab hhook hrhs (KontOk.asgn hk)
        · exact absurd hinf (by simp)
      all_goals (simp only [infer] at hinf; contradiction)
    case seq es =>
      simp only [infer] at hinf
      cases es with
      | nil =>
        simp only [inferSeq, Option.some.injEq, Prod.mk.injEq] at hinf
        obtain ⟨rfl, rfl⟩ := hinf
        exact inv_value hfs htab hhook rfl hk
      | cons e₁ rest =>
        cases rest with
        | nil =>
          simp only [inferSeq] at hinf
          exact inv_eval hfs htab hhook hinf hk
        | cons e₂ rest' =>
          simp only [inferSeq] at hinf
          split at hinf
          · rename_i σ Γ₁ h₁
            exact inv_push hfs htab hhook h₁ (KontOk.seqCons hinf hk)
          · exact absurd hinf (by simp)
    case if' c t els =>
      simp only [infer] at hinf
      split at hinf
      · rename_i σ Γ₁ hcnd
        exact inv_push hfs htab hhook hcnd (KontOk.ifK hinf hk)
      · exact absurd hinf (by simp)
    case while' c body =>
      simp only [infer] at hinf
      split at hinf
      · rename_i σ Γ₁ hcnd
        split at hinf
        · rename_i hΓ₁
          subst hΓ₁
          split at hinf
          · rename_i σb Γ₂ hbody
            split at hinf
            · rename_i hΓ₂
              subst hΓ₂
              simp only [Option.some.injEq, Prod.mk.injEq] at hinf
              obtain ⟨rfl, rfl⟩ := hinf
              exact inv_push hfs htab hhook hcnd
                (KontOk.whileCond ⟨⟨σ, hcnd⟩, ⟨σb, hbody⟩⟩ hk)
            · exact absurd hinf (by simp)
          · exact absurd hinf (by simp)
        · exact absurd hinf (by simp)
      · exact absurd hinf (by simp)
    case def' name params body =>
      obtain ⟨rfl, rfl, rfl, hfresh, hha⟩ := infer_def_inv hinf
      have hdm : m.currentFrame = curFrame m := currentFrame_eq hf.1
      have hdo : (curFrame m).defmod = Boot.objectId := by
        cases hst : m.stack with
        | nil => exact absurd hst hf.1
        | cons fid _ =>
          have : FrameConforms m.heap Γ' (m.frames.getD fid default) := by
            rw [hst] at hfs; exact hfs.2.2.1
          simpa [curFrame, curFid, hst] using this.2.1
      have hha' : ¬ ("method_added" = name) := fun hh => hha hh.symm
      have hlk : ∀ md : MethodDef,
          lookup (defineMethod m.heap Boot.objectId name md)
            (.ref Boot.objectId) "method_added" = none := by
        intro md
        rw [lookup_defineMethod _ _ name "method_added" md _ hha'
          (classOf_defineMethod _ _ _ _ _)]
        exact hhook
      -- Quantified over `md` so the `MethodDef` literal `evalExpr` builds never
      -- has to be written out, and over `m₀` so the `preludeMode` branch — which
      -- differs only in fields `Inv` does not mention — is discharged by the same
      -- argument. (There used to be a `reprSensitive` branch here too; L103
      -- retired the global `reprPure` flag for a per-class test, so `def` no longer
      -- touches it. This proof kept case-splitting on a constant that no longer
      -- exists, and `Proof/` being off the default build target is why that went
      -- unnoticed from L103 until now — L119.)
      -- Phrased over the *facts* about `m₀.heap` rather than over the
      -- `MethodDef` that produced it: `m₀` is then fixed by unifying the
      -- conclusion with the goal, and each remaining hypothesis is a concrete
      -- goal whose `md` unification is forced. Quantifying over `md` instead
      -- leaves it an unsolvable metavariable.
      -- L137 added the fourth hypothesis, `TypeAgree`: with the judgement
      -- heap-indexed, the `ValueTy` facts stored in the frames and in the
      -- continuation stack have to be *transported* into the post-`def` heap
      -- rather than reused. `defineMethod` supplies it
      -- (`typeAgree_defineMethod`), which is the whole reason `TypeAgree` is
      -- phrased over `classOf`/`className`/`classPayload?` and not over the
      -- method table.
      have hres : ∀ (m₀ : Machine),
          m₀.frames = m.frames → m₀.stack = m.stack → m₀.kont = m.kont →
          TypeAgree m.heap m₀.heap → DeclsOk D m₀.heap → NoHook m₀.heap →
          Inv D (withCtl m₀ (.value (.sym name))) := by
        intro m₀ hfr hst hko hag ht' hh'
        refine ⟨ht', hh', Γ', Γs, ?_, ?_⟩
        · show FramesOk m₀.heap m₀.frames m₀.stack (Γ' :: Γs)
          rw [hfr, hst]; exact FramesOk.heap_congr hag hfs
        · show ∃ σ, ValueTy m₀.heap (Value.sym name) σ ∧
              KontOk D m₀.heap (Γ' :: Γs) σ m₀.kont
          exact ⟨.sym, rfl, by rw [hko]; exact KontOk.heap_congr hag hk⟩
      -- `hlk` collapses the hook lookup to `none`, after which only the
      -- `preludeMode` `if` remains.
      simp only [evalExpr, hdm, hdo]
      -- `split` would dive into the `visibility` `if`s *inside* the `MethodDef`
      -- literal, which `hres` deliberately abstracts over; case on the one
      -- condition that matters instead.
      by_cases hp : m.preludeMode = true <;>
        simp only [hp, if_true, if_false, Bool.false_eq_true, hlk] <;>
        refine hres _ ?_ ?_ ?_ ?_ ?_ ?_ <;>
          first
            | rfl
            | exact typeAgree_defineMethod _ _ _ _
            | exact DeclsOk_defineMethod htab hfresh
            | exact hlk _
    case send recv mname args blk =>
      cases recv with
      | none => exact absurd hinf (by simp [infer])
      | some r =>
        cases args with
        | nil => exact absurd hinf (by simp [infer])
        | cons arg extra =>
          cases extra with
          | cons _ _ => exact absurd hinf (by simp [infer])
          | nil =>
            cases blk with
            | some b => exact absurd hinf (by simp [infer])
            | none =>
              obtain ⟨τr, Γ₁, τp, hr, hsg, ha⟩ := infer_send_inv hinf
              -- `evalExpr` picks the send site by matching on the receiver
              -- *expression*, and that match will not rewrite under `rw`, so
              -- force it to compute. Every branch but `self` is `.explicit`,
              -- and `infer` rejects `self`.
              simp only [evalExpr]
              cases r <;>
                try exact inv_push hfs htab hhook hr (KontOk.recvK hsg ha hk)
              exact absurd hr (by simp [infer])
  · -- ## control = value v
    rw [hctl] at hc
    obtain ⟨τ, hv, hk⟩ := hc
    simp only [stepFn, hctl]
    unfold applyKont
    generalize hK : m.kont = K at hk ⊢
    cases hk with
    | nil => trivial
    | @seqNil Γ Γs τ k hk' =>
      exact inv_value hfs htab hhook hv hk'
    | @seqCons Γ Γs τ e₁ es τ' Γ' k hseq hk' =>
      cases es with
      | nil =>
        simp only [inferSeq] at hseq
        exact inv_push hfs htab hhook hseq (KontOk.seqNil hk')
      | cons e₂ es' =>
        simp only [inferSeq] at hseq
        split at hseq
        · rename_i σ Γ₁ h₁
          exact inv_push hfs htab hhook h₁ (KontOk.seqCons hseq hk')
        · exact absurd hseq (by simp)
    | @asgn Γ Γs τ x k hk' =>
      -- The machine `applyKont` steps to is `{ m with kont := k }.setLocal x v`, and
      -- `hfs` is phrased over `m`. The two agree definitionally, but since L137 made
      -- `FramesOk` heap-indexed the elaborator resolves `?m` from `hfs` rather than
      -- from the goal, so the instance has to be named.
      refine ⟨htab, hhook, envSet Γ x τ, Γs, ?_, ⟨τ, hv, hk'⟩⟩
      exact FramesOk.setLocal (m := { m with kont := k }) hfs hv
    | @ifK Γ Γs τ t els τ' Γ' k hif hk' =>
      cases els with
      | some e₂ =>
        simp only [inferIf] at hif
        split at hif
        · rename_i τt Γt τe Γe ht he
          split at hif
          · rename_i hagree
            obtain ⟨rfl, rfl⟩ := hagree
            simp only [Option.some.injEq, Prod.mk.injEq] at hif
            obtain ⟨rfl, rfl⟩ := hif
            by_cases hb : v.truthy
            · simp only [hb, if_true]; exact inv_eval hfs htab hhook ht hk'
            · simp only [hb]; exact inv_eval hfs htab hhook he hk'
          · exact absurd hif (by simp)
        · exact absurd hif (by simp)
      | none =>
        simp only [inferIf] at hif
        split at hif
        · rename_i τt Γt ht
          split at hif
          · rename_i hnil
            obtain ⟨rfl, rfl⟩ := hnil
            simp only [Option.some.injEq, Prod.mk.injEq] at hif
            obtain ⟨rfl, rfl⟩ := hif
            by_cases hb : v.truthy
            · simp only [hb, if_true]; exact inv_eval hfs htab hhook ht hk'
            · simp only [hb]; exact inv_value hfs htab hhook rfl hk'
          · exact absurd hif (by simp)
        · exact absurd hif (by simp)
    | @whileCond Γ Γs τ c body k hloop hk' =>
      obtain ⟨⟨σc, hcnd⟩, ⟨σb, hbody⟩⟩ := hloop
      by_cases hb : v.truthy
      · simp only [hb, if_true]
        exact inv_push hfs htab hhook hbody (KontOk.whileBody ⟨⟨σc, hcnd⟩, ⟨σb, hbody⟩⟩ hk')
      · simp only [hb]
        exact inv_value hfs htab hhook rfl hk'
    | @whileBody Γ Γs τ c body k hloop hk' =>
      obtain ⟨⟨σc, hcnd⟩, ⟨σb, hbody⟩⟩ := hloop
      exact inv_push hfs htab hhook hcnd (KontOk.whileCond ⟨⟨σc, hcnd⟩, ⟨σb, hbody⟩⟩ hk')
    | @frameK Γ Γ' Γs τ fid k hk' =>
      -- The activation pops: `frames` is untouched, `stack` loses its head, and
      -- the caller's environment — carried all along by `FramesOk` — becomes
      -- current again. This is the case L91 could not close.
      exact ⟨htab, hhook, Γ', Γs, hfs.tail, ⟨τ, hv, hk'⟩⟩
    | @recvK Γ Γs τ mname arg τp τret Γ₂ k hsg ha hk' =>
      have hsp : ∀ e, arg ≠ .splat e := by
        rintro e rfl; exact absurd ha (by simp [infer])
      have hkw : ∀ es, arg ≠ .kwargs es := by
        rintro es rfl; exact absurd ha (by simp [infer])
      have hfw : arg ≠ .fwd := by
        rintro rfl; exact absurd ha (by simp [infer])
      dsimp only
      rw [startArgs_plain hsp hkw hfw]
      exact inv_push hfs htab hhook ha (KontOk.argsK hv hsg hk')
    | @argsK Γ Γs τ mname recv τr τret k hrv hsg hk' =>
      -- **F1a: one dispatch step for every declared method**, where P0 had a
      -- three-way `rcases` over the tabulated names and a rewrite per name. The
      -- invariant supplies the entry, `entry_dispatch` supplies the step, and the
      -- ~128 conformance lemmas of F6 become witnesses of the same clause rather
      -- than a parallel obligation (`typing-a-mutable-method-table.md` §7).
      dsimp only
      simp only [List.nil_append]
      obtain ⟨w, hw, hstep⟩ :=
        entry_dispatch (m := { m with kont := k }) (recv := recv) (args := [v])
          (htab τr mname _ (sigOf_declFor hsg)) hrv (And.intro hv trivial)
      rw [hstep]
      exact inv_value hfs htab hhook hw hk'
  · -- ## control = jump: excluded by `CtlOk`
    rw [hctl] at hc
    exact hc.elim
end Static
end Proof
end RubyCore
