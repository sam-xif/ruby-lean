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

def StepOk : StepResult → Prop
  | .next m' => Inv m'
  | .done _ _ => True
  | _ => False

theorem step_ok {m : Machine} (h : Inv m) : StepOk (stepFn m) := by
  obtain ⟨hhook, hsat, hstr, hcls, hbot, D, ctx, Γ, Γs, htab, hfs, hsc, hc⟩ := h
  have hf : FrameOk m := hfs.frameOk
  have hl : LocalsOk Γ m := hfs.localsOk
  unfold CtlOk at hc
  rcases hctl : m.ctl with e | v | j
  · -- ## control = eval e
    rw [hctl] at hc
    obtain ⟨τ, Γ', D', hinf, hk⟩ := hc
    simp only [stepFn, hctl]
    cases e <;> try (simp only [infer] at hinf; contradiction)
    case int n =>
      simp only [infer, Option.some.injEq, Prod.mk.injEq] at hinf
      obtain ⟨rfl, rfl, rfl⟩ := hinf
      exact inv_value hfs htab hsc hhook hsat hstr hcls hbot rfl hk
    case tru =>
      simp only [infer, Option.some.injEq, Prod.mk.injEq] at hinf
      obtain ⟨rfl, rfl, rfl⟩ := hinf
      exact inv_value hfs htab hsc hhook hsat hstr hcls hbot rfl hk
    case fls =>
      simp only [infer, Option.some.injEq, Prod.mk.injEq] at hinf
      obtain ⟨rfl, rfl, rfl⟩ := hinf
      exact inv_value hfs htab hsc hhook hsat hstr hcls hbot rfl hk
    case nil =>
      simp only [infer, Option.some.injEq, Prod.mk.injEq] at hinf
      obtain ⟨rfl, rfl, rfl⟩ := hinf
      exact inv_value hfs htab hsc hhook hsat hstr hcls hbot rfl hk
    -- **The producer** (L151). One allocation, no continuation, no dispatch: the
    -- whole case is `plainGrow_alloc` for the step, `valueTy_alloc_fresh` for the
    -- value, and `inv_grow_value` — proved a rung earlier — for everything else.
    -- That the case is this short is the measurement L149 was for.
    case str s =>
      simp only [infer, Option.some.injEq, Prod.mk.injEq] at hinf
      obtain ⟨rfl, rfl, rfl⟩ := hinf
      exact inv_grow_value hfs htab hsc hhook hsat hstr hcls hbot
        (plainGrow_alloc m.heap _ (by simp))
        rfl rfl rfl
        (valueTy_alloc_fresh (by simp) rfl hstr.1 hstr.2) hk
    -- **The symbol literal** (L159). Identical to the four immediate cases above,
    -- which is the point: the slice's third-largest blocker by node count cost a
    -- rule of one line and a case of three, because `Ty.sym` was already there and
    -- `evalExpr` writes no heap.
    case sym s =>
      simp only [infer, Option.some.injEq, Prod.mk.injEq] at hinf
      obtain ⟨rfl, rfl, rfl⟩ := hinf
      exact inv_value hfs htab hsc hhook hsat hstr hcls hbot rfl hk
    case var k x =>
      cases k
      case lvar =>
        simp only [infer, Option.map_eq_some_iff] at hinf
        obtain ⟨σ, hg, heq⟩ := hinf
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        exact inv_value hfs htab hsc hhook hsat hstr hcls hbot (hl x _ hg) hk
      all_goals (simp only [infer] at hinf; contradiction)
    case vasgn k x rhs =>
      cases k
      case lvar =>
        simp only [infer] at hinf
        split at hinf
        · rename_i σ Γ₁ hrhs
          simp only [Option.some.injEq, Prod.mk.injEq] at hinf
          obtain ⟨rfl, rfl, rfl⟩ := hinf
          exact inv_push hfs htab hsc hhook hsat hstr hcls hbot hrhs (KontOk.asgn hk)
        · exact absurd hinf (by simp)
      all_goals (simp only [infer] at hinf; contradiction)
    case seq es =>
      simp only [infer] at hinf
      cases es with
      | nil =>
        simp only [inferSeq, Option.some.injEq, Prod.mk.injEq] at hinf
        obtain ⟨rfl, rfl, rfl⟩ := hinf
        exact inv_value hfs htab hsc hhook hsat hstr hcls hbot rfl hk
      | cons e₁ rest =>
        cases rest with
        | nil =>
          simp only [inferSeq] at hinf
          exact inv_eval hfs htab hsc hhook hsat hstr hcls hbot hinf hk
        | cons e₂ rest' =>
          simp only [inferSeq] at hinf
          split at hinf
          · rename_i σ Γ₁ h₁
            exact inv_push hfs htab hsc hhook hsat hstr hcls hbot h₁ (KontOk.seqCons hinf hk)
          · exact absurd hinf (by simp)
    case if' c t els =>
      simp only [infer] at hinf
      split at hinf
      · rename_i σ Γ₁ hcnd
        exact inv_push hfs htab hsc hhook hsat hstr hcls hbot hcnd (KontOk.ifK hinf hk)
      · exact absurd hinf (by simp)
    case while' c body =>
      simp only [infer] at hinf
      split at hinf
      · rename_i σ Γ₁ D₁ hcnd
        split at hinf
        · rename_i hΓ₁
          obtain ⟨rfl, rfl⟩ := hΓ₁
          split at hinf
          · rename_i σb Γ₂ D₂ hbody
            split at hinf
            · rename_i hΓ₂
              obtain ⟨rfl, rfl⟩ := hΓ₂
              simp only [Option.some.injEq, Prod.mk.injEq] at hinf
              obtain ⟨rfl, rfl, rfl⟩ := hinf
              exact inv_push hfs htab hsc hhook hsat hstr hcls hbot hcnd
                (KontOk.whileCond ⟨⟨σ, hcnd⟩, ⟨σb, hbody⟩⟩ hk)
            · exact absurd hinf (by simp)
          · exact absurd hinf (by simp)
        · exact absurd hinf (by simp)
      · exact absurd hinf (by simp)
    -- **Reopening a class** (F1b.6, L156). The step writes **no heap at all** —
    -- `enterClassBody`'s reopen branch is `pushFrame` and nothing else — which is
    -- the whole reason this rung comes before the allocating one: all six heap
    -- conjuncts carry across by `rfl`, and what is left is the frame push.
    case class' name sup body =>
      obtain ⟨htop, rfl, hmem, rfl, Γb, hbody⟩ := infer_class_inv hinf
      -- `Γs.isEmpty = true` is the mode `infer` was run at; `FramesOk` turns it into
      -- a singleton frame stack and `BottomObj` names that frame's definee. This is
      -- the composite L155 exists for.
      have hΓs : Γs = [] := List.isEmpty_iff.mp htop
      subst hΓs
      obtain ⟨fid₀, hst⟩ := hfs.stack_singleton
      have hdefmod : m.currentFrame.defmod = Boot.objectId := by
        rw [currentFrame_eq hf.1]; exact BottomObj_curFrame hst hbot
      -- `ClassOk` at this name: the constant is there, it is a class, and it is not
      -- a module — the three tests `enterClassBody` applies before `pushFrame`.
      obtain ⟨k, cp, hconst, hpay, hmod, hnm, huniq⟩ :=
        hcls.2 name (List.mem_of_elem_eq_true hmem)
      simp only [evalExpr, enterClassBody, hdefmod, hconst, hpay, hmod, withKont]
      -- What is left is `pushFrame`, and it is a frame push on an untouched heap.
      have hlt : ∀ g ∈ m.stack, g < m.frames.size := hfs.mem_lt
      refine ⟨hhook, hsat, hstr, hcls,
        BottomObj_cons hf.1 (BottomObj_push hlt hbot), D, name, [], [(ctx, Γ')],
        htab, ?_, ?_, ?_⟩
      · refine ⟨by rw [Array.size_push]; exact Nat.lt_succ_self _, hlt, ?_,
          FramesOk.push hfs⟩
        rw [getD_push_lt_self]
        -- `FrameConforms` at the class-body frame: no captured chain (the literal
        -- leaves the field at its default), the definee is a class — which is
        -- exactly `ClassOk`'s second conjunct, and is what L154 generalized this
        -- clause to admit — and the empty environment types nothing.
        exact ⟨rfl, by simp [hpay], by simp [envGet?]⟩
      -- **The class-body frame's static context is the class's own name** (F1b.9),
      -- and this is where `ClassOk`'s new clause is spent: the definee is the object
      -- the constant names, and that object is named `name`. `defVis` comes out of
      -- the frame literal's default, which is what makes a `def` in this body public
      -- where a toplevel one is private.
      · refine ⟨?_, ?_, ?_, StackCtx.push hlt hsc⟩
        · rw [getD_push_lt_self]; simp [hpay]
        · rw [getD_push_lt_self]; exact hnm
        · rw [getD_push_lt_self]; exact fun _ => rfl
      -- The class body's own table `Db` is the index the *callee's* continuation
      -- carries; `frameK` carries one table, which the rule's stability condition
      -- is what pays for.
      · exact ⟨τ, Γb, D', hbody, KontOk.frameK hk⟩
    case def' name params body =>
      obtain ⟨rfl, rfl, rfl, hfresh, hha, τb, Γb, hbody, hrow⟩ := infer_def_inv hinf
      have hdm : m.currentFrame = curFrame m := currentFrame_eq hf.1
      -- L154: the definee is *a class* rather than *`Object`*, which is what makes a
      -- class-body frame expressible. Every `defineMethod` lemma below is already
      -- stated `∀ cls`, so the generalization costs nothing here — the equation was
      -- only ever used to instantiate `NoHook` at the definee, and `NoHook` is now
      -- quantified over exactly the class objects this predicate names.
      have hdo : (m.heap.classPayload? (curFrame m).defmod).isSome := by
        cases hst : m.stack with
        | nil => exact absurd hst hf.1
        | cons fid _ =>
          have : FrameConforms m.heap Γ' (m.frames.getD fid default) := by
            rw [hst] at hfs; exact hfs.2.2.1
          simpa [curFrame, curFid, hst] using this.2.1
      have hha' : ¬ ("method_added" = name) := fun hh => hha hh.symm
      -- `hlk` is the raw lookup equation, because `simp` needs it to collapse
      -- `evalExpr`'s hook `match`; `hlkNH` is the invariant's clause, which since L149
      -- also carries `Boot.objectId < objs.size` — preserved because `set!` does not
      -- resize.
      have hlkNH : ∀ md : MethodDef,
          NoHook (defineMethod m.heap (curFrame m).defmod name md) :=
        fun _ => NoHook_defineMethod hhook hha'
      -- L153/L154: one *instance* of the generalized clause, at the definee the frame
      -- names. That the definee is a class is `hdo`, and `classPayload?` is unmoved by
      -- a method-table write.
      have hlk : ∀ md : MethodDef,
          lookup (defineMethod m.heap (curFrame m).defmod name md)
            (.ref (curFrame m).defmod) "method_added" = none := fun md =>
        (hlkNH md).2 (curFrame m).defmod
          (by rw [classPayload?_isSome_defineMethod]; exact hdo)
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
          TypeAgree m.heap m₀.heap → DeclsOk D' m₀.heap → NoHook m₀.heap →
          Saturated m₀.heap → StrClsOk m₀.heap → ClassOk m₀.heap →
          Inv (withCtl m₀ (.value (.sym name))) := by
        intro m₀ hfr hst hko hag ht' hh' hsat' hstr' hcls'
        refine ⟨hh', hsat', hstr', hcls',
          show BottomObj m₀.frames m₀.stack by rw [hfr, hst]; exact hbot,
          D', ctx, Γ', Γs, ht', ?_, ?_, ?_⟩
        · show FramesOk m₀.heap m₀.frames m₀.stack (Γ' :: Γs.map Prod.snd)
          rw [hfr, hst]; exact FramesOk.heap_congr hag hfs
        · show StackCtx m₀.heap m₀.frames m₀.stack (ctx :: Γs.map Prod.fst)
          rw [hfr, hst]; exact StackCtx.heap_congr hag hsc
        · show ∃ σ, ValueTy m₀.heap (Value.sym name) σ ∧
              KontOk D' m₀.heap ((ctx, Γ') :: Γs) σ m₀.kont
          exact ⟨.sym, rfl, by rw [hko]; exact KontOk.heap_congr hag hk⟩
      -- `hlk` collapses the hook lookup to `none`, after which only the
      -- `preludeMode` `if` remains.
      simp only [evalExpr, hdm]
      -- `split` would dive into the `visibility` `if`s *inside* the `MethodDef`
      -- literal, which `hres` deliberately abstracts over; case on the one
      -- condition that matters instead.
      -- **The declaration obligation** (F1b.10), and it is the only conjunct that
      -- distinguishes the two branches of the rule. Without a row `DeclsOk` is
      -- `DeclsOk_defineMethod` exactly as before; with one it is `DeclsOk_addRow`,
      -- whose single new obligation is the row's own `EntryOk` — discharged by the
      -- **user** arm, which makes this the first commit in which that arm is
      -- inhabited (L157 built it and left it empty).
      rcases hrow with rfl | ⟨rfl, htopf, hinit, hmemctx, hdf⟩
      · by_cases hp : m.preludeMode = true <;>
          simp only [hp, if_true, if_false, Bool.false_eq_true, hlk] <;>
          refine hres _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
            first
              | rfl
              | exact typeAgree_defineMethod _ _ _ _
              | exact DeclsOk_defineMethod htab hfresh
              | exact hlkNH _
              | exact Saturated_defineMethod hsat _ _ _
              | exact StrClsOk_defineMethod hstr
              | exact ClassOk_defineMethod hcls
      -- The row branch. Three facts about the *current frame* are wanted, and all
      -- three come from `StackCtx` — which is what that predicate was added for.
      · obtain ⟨fid₀, fids₀, hst⟩ : ∃ fid fids, m.stack = fid :: fids := by
          cases hst : m.stack with
          | nil => exact absurd hst hf.1
          | cons a r => exact ⟨a, r, rfl⟩
        have hΓs : Γs ≠ [] := by
          intro hz; rw [hz] at htopf; exact absurd htopf (by simp)
        have hfidsne : fids₀ ≠ [] := by
          intro hz
          rw [hst, hz] at hfs
          cases hΓ : Γs with
          | nil => exact absurd hΓ hΓs
          | cons a r => rw [hΓ] at hfs; exact absurd hfs.2.2.2 (by simp [FramesOk])
        have hscc : StackCtx m.heap m.frames (fid₀ :: fids₀) (ctx :: Γs.map Prod.fst) := by
          rw [hst] at hsc; exact hsc
        have hctx : className m.heap (curFrame m).defmod = ctx := by
          rw [show curFrame m = m.frames.getD fid₀ default by
            simp [curFrame, curFid, hst]]
          exact hscc.2.1
        have hvis : defVisOfDef (curFrame m) = .pub := by
          rw [show curFrame m = m.frames.getD fid₀ default by
            simp [curFrame, curFid, hst]]
          exact hscc.2.2.1 hfidsne
        -- The chain from the definee starts at the definee, which is what makes the
        -- entry the step just wrote the one `lookup` finds.
        have hchain : ∀ md : MethodDef, ∃ rest,
            ancestors (defineMethod m.heap (curFrame m).defmod name md)
              (curFrame m).defmod = (curFrame m).defmod :: rest := by
          intro md
          obtain ⟨k₀, cp, _, _, _, hnm₀, huniq₀, hhead₀⟩ :=
            (ClassOk_defineMethod (name := name) (md := md)
              (cls := (curFrame m).defmod) hcls).2 ctx (List.mem_of_elem_eq_true hmemctx)
          have hdefk : (curFrame m).defmod = k₀ :=
            huniq₀ _ (by rw [classPayload?_isSome_defineMethod]; exact hdo)
              (by rw [className_defineMethod]; exact hctx)
          rw [hdefk] at hdo hhead₀ ⊢
          cases hanc : ancestors (defineMethod m.heap k₀ name md) k₀ with
          | nil => rw [hanc] at hhead₀; exact absurd hhead₀ (by simp)
          | cons a rest =>
            rw [hanc] at hhead₀
            simp only [List.head?_cons, Option.some.injEq] at hhead₀
            exact ⟨rest, by rw [hhead₀]⟩
        have hdecls : ∀ (md : MethodDef), md.owner = (curFrame m).defmod →
            md.builtin = none → md.undefined = false → md.visibility = .pub →
            md.params = [] → md.declared = [] → md.capturedFrame = none →
            md.body = body →
            DeclsOk (addRow D ctx name { params := [], ret := τb })
              (defineMethod m.heap (curFrame m).defmod name md) := by
          intro md hown hb hu hvs hpar hdec hcap hbd
          refine DeclsOk_addRow htab hfresh ?_ ?_
          · -- The row is not at a ground type, which is what `reopenableClasses`
            -- membership buys: `tyClassNames` of a ground type lists ground names,
            -- and a row on one would owe `EntryOk` over immediates.
            revert hmemctx
            simp only [reopenableClasses, groundClassNames, List.contains_cons,
              List.contains_nil, Bool.or_false, beq_iff_eq]
            rintro rfl
            decide
          obtain ⟨k₀, cp, _, _, _, hnm₀, huniq₀, _⟩ :=
            (ClassOk_defineMethod (name := name) (md := md)
              (cls := (curFrame m).defmod) hcls).2 ctx (List.mem_of_elem_eq_true hmemctx)
          have hctx' : className (defineMethod m.heap (curFrame m).defmod name md)
              (curFrame m).defmod = ctx := by rw [className_defineMethod]; exact hctx
          have hdefk : (curFrame m).defmod = k₀ :=
            huniq₀ _ (by rw [classPayload?_isSome_defineMethod]; exact hdo) hctx'
          obtain ⟨rest, hrest⟩ := hchain md
          refine Or.inr ⟨md, ctx, fun k htc => ?_, by rw [hown]; exact hctx', rfl,
            by rw [hbd]; exact hdf, ?_⟩
          · have hk : k = (curFrame m).defmod := by
              rw [hdefk]; exact huniq₀ k htc.1 htc.2
            subst hk
            refine ⟨(curFrame m).defmod, ?_, hb, hu, hvs, hpar, hdec, hcap,
              by rw [hown, classPayload?_isSome_defineMethod]; exact hdo, ?_⟩
            · show lookup.go _ name (ancestors _ _) = _
              rw [hrest]
              exact lookup_go_defineMethod_self m.heap _ name md hdo rest
            · split
              · rfl
              · rw [hrest]
                simp only [List.takeWhile, bne_self_eq_false, decide_false,
                  Bool.false_eq_true, if_false]
                rfl
          · exact ⟨Γb, by rw [hbd]; exact infer_mono (subDecls_addRow hfresh) hdf hbody⟩
        by_cases hp : m.preludeMode = true <;>
          simp only [hp, if_true, if_false, Bool.false_eq_true, hlk] <;>
          refine hres _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
            first
              | rfl
              | exact typeAgree_defineMethod _ _ _ _
              -- The literal's `visibility` is `defVisOfDef` once the name is not
              -- `initialize`, and `StackCtx` says that is `.pub` on any frame that
              -- is not the outermost — which `top = false` is exactly.
              | exact hdecls _ rfl rfl rfl
                  (by simpa [defVisOfDef, hinit] using hvis) rfl rfl rfl rfl
              | exact hlkNH _
              | exact Saturated_defineMethod hsat _ _ _
              | exact StrClsOk_defineMethod hstr
              | exact ClassOk_defineMethod hcls
    case send recv mname args blk =>
      cases recv with
      | none => exact absurd hinf (by simp [infer])
      | some r =>
        cases args with
        -- **The zero-argument send** (L152). Same `evalExpr` step as the unary one —
        -- push `recvK` and evaluate the receiver — and the whole difference lands one
        -- step later, in `applyKont`.
        | nil =>
          cases blk with
          | some b => exact absurd hinf (by simp [infer])
          | none =>
            obtain ⟨τr, hr, hsg⟩ := infer_send0_inv hinf
            simp only [evalExpr]
            cases r <;>
              try exact inv_push hfs htab hsc hhook hsat hstr hcls hbot hr (KontOk.recvK0 hsg hk)
            exact absurd hr (by simp [infer])
        | cons arg extra =>
          cases extra with
          | cons _ _ => exact absurd hinf (by simp [infer])
          | nil =>
            cases blk with
            | some b => exact absurd hinf (by simp [infer])
            | none =>
              obtain ⟨τr, Γ₁, D₁, τp, hr, ha, hsg⟩ := infer_send_inv hinf
              -- `evalExpr` picks the send site by matching on the receiver
              -- *expression*, and that match will not rewrite under `rw`, so
              -- force it to compute. Every branch but `self` is `.explicit`,
              -- and `infer` rejects `self`.
              simp only [evalExpr]
              cases r <;>
                try exact inv_push hfs htab hsc hhook hsat hstr hcls hbot hr (KontOk.recvK ha hsg hk)
              exact absurd hr (by simp [infer])
  · -- ## control = value v
    rw [hctl] at hc
    obtain ⟨τ, hv, hk⟩ := hc
    simp only [stepFn, hctl]
    unfold applyKont
    generalize hK : m.kont = K at hk ⊢
    cases hk with
    | nil => trivial
    | @seqNil _ _ _ _ _ _ k hk' =>
      exact inv_value hfs htab hsc hhook hsat hstr hcls hbot hv hk'
    | @seqCons _ _ _ _ _ _ _ e₁ es τ' Γ' k hseq hk' =>
      cases es with
      | nil =>
        simp only [inferSeq] at hseq
        exact inv_push hfs htab hsc hhook hsat hstr hcls hbot hseq (KontOk.seqNil hk')
      | cons e₂ es' =>
        simp only [inferSeq] at hseq
        split at hseq
        · rename_i σ Γ₁ h₁
          exact inv_push hfs htab hsc hhook hsat hstr hcls hbot h₁ (KontOk.seqCons hseq hk')
        · exact absurd hseq (by simp)
    | @asgn _ _ _ _ _ _ x k hk' =>
      -- The machine `applyKont` steps to is `{ m with kont := k }.setLocal x v`, and
      -- `hfs` is phrased over `m`. The two agree definitionally, but since L137 made
      -- `FramesOk` heap-indexed the elaborator resolves `?m` from `hfs` rather than
      -- from the goal, so the instance has to be named.
      refine ⟨hhook, hsat, hstr, hcls, ?_, _, ctx, envSet Γ x τ, Γs, htab, ?_, ?_, ⟨τ, hv, hk'⟩⟩
      · -- `setLocal` rewrites one frame's `locals` and nothing else, so every
        -- stacked frame's `defmod` — all `BottomObj` reads — is unmoved.
        show BottomObj (Machine.setLocal { m with kont := k } x v).frames
          (Machine.setLocal { m with kont := k } x v).stack
        have hf' : FrameOk { m with kont := k } :=
          FramesOk.frameOk (m := { m with kont := k }) hfs
        rw [setLocal_stack, setLocal_frames (m := { m with kont := k }) hf']
        refine BottomObj_congr (fun fid _ => ?_) hbot
        by_cases hfx : fid = curFid { m with kont := k }
        · subst hfx
          rw [getD_set!_self _ _ _ (by simpa using hf'.2.1)]
          rfl
        · rw [getD_set!_ne _ _ _ _ hfx]
      · exact FramesOk.setLocal (m := { m with kont := k }) hfs hv
      · -- The same argument for the context stack: `setLocal` moves neither
        -- `defmod` nor `defVis`, which is all this predicate reads.
        show StackCtx (Machine.setLocal { m with kont := k } x v).heap
          (Machine.setLocal { m with kont := k } x v).frames
          (Machine.setLocal { m with kont := k } x v).stack (ctx :: Γs.map Prod.fst)
        have hf' : FrameOk { m with kont := k } :=
          FramesOk.frameOk (m := { m with kont := k }) hfs
        rw [setLocal_stack, setLocal_frames (m := { m with kont := k }) hf']
        refine StackCtx_congr (fun fid _ => ?_) (fun fid _ => ?_) hsc <;>
          by_cases hfx : fid = curFid { m with kont := k }
        · subst hfx; rw [getD_set!_self _ _ _ (by simpa using hf'.2.1)]; rfl
        · rw [getD_set!_ne _ _ _ _ hfx]
        · subst hfx
          rw [getD_set!_self _ _ _ (by simpa using hf'.2.1)]
          rfl
        · rw [getD_set!_ne _ _ _ _ hfx]
    | @ifK _ _ _ _ _ _ _ t els τ' Γ' k hif hk' =>
      cases els with
      | some e₂ =>
        simp only [inferIf] at hif
        split at hif
        · rename_i τt Γt Dt τe Γe De ht he
          split at hif
          · rename_i hagree
            obtain ⟨rfl, rfl, rfl⟩ := hagree
            simp only [Option.some.injEq, Prod.mk.injEq] at hif
            obtain ⟨rfl, rfl, rfl⟩ := hif
            by_cases hb : v.truthy
            · simp only [hb, if_true]; exact inv_eval hfs htab hsc hhook hsat hstr hcls hbot ht hk'
            · simp only [hb]; exact inv_eval hfs htab hsc hhook hsat hstr hcls hbot he hk'
          · exact absurd hif (by simp)
        · exact absurd hif (by simp)
      | none =>
        simp only [inferIf] at hif
        split at hif
        · rename_i τt Γt ht
          split at hif
          · rename_i hnil
            obtain ⟨rfl, rfl, rfl⟩ := hnil
            simp only [Option.some.injEq, Prod.mk.injEq] at hif
            obtain ⟨rfl, rfl, rfl⟩ := hif
            by_cases hb : v.truthy
            · simp only [hb, if_true]; exact inv_eval hfs htab hsc hhook hsat hstr hcls hbot ht hk'
            · simp only [hb]; exact inv_value hfs htab hsc hhook hsat hstr hcls hbot rfl hk'
          · exact absurd hif (by simp)
        · exact absurd hif (by simp)
    | @whileCond _ _ _ _ _ _ c body k hloop hk' =>
      obtain ⟨⟨σc, hcnd⟩, ⟨σb, hbody⟩⟩ := hloop
      by_cases hb : v.truthy
      · simp only [hb, if_true]
        exact inv_push hfs htab hsc hhook hsat hstr hcls hbot hbody (KontOk.whileBody ⟨⟨σc, hcnd⟩, ⟨σb, hbody⟩⟩ hk')
      · simp only [hb]
        exact inv_value hfs htab hsc hhook hsat hstr hcls hbot rfl hk'
    | @whileBody _ _ _ _ _ _ c body k hloop hk' =>
      obtain ⟨⟨σc, hcnd⟩, ⟨σb, hbody⟩⟩ := hloop
      exact inv_push hfs htab hsc hhook hsat hstr hcls hbot hcnd (KontOk.whileCond ⟨⟨σc, hcnd⟩, ⟨σb, hbody⟩⟩ hk')
    | @frameK _ _ _ cΓ' Γs _ fid k hk' =>
      -- The activation pops: `frames` is untouched, `stack` loses its head, and
      -- the caller's environment — carried all along by `FramesOk` — becomes
      -- current again. This is the case L91 could not close.
      obtain ⟨c', Γ'⟩ := cΓ'
      refine ⟨hhook, hsat, hstr, hcls, BottomObj_tail hbot, _, c', Γ', Γs, htab,
        hfs.tail, ?_, ⟨τ, hv, hk'⟩⟩
      -- `StackCtx` pops with the environment stack, which is the whole point of
      -- pairing the two: the caller's context is the second component of the list
      -- rather than a fact `frameK` has to be handed.
      exact StackCtx.tail hsc
    | @recvK _ _ _ _ _ _ _ mname arg τp τret Γ₂ k ha hsg hk' =>
      have hsp : ∀ e, arg ≠ .splat e := by
        rintro e rfl; exact absurd ha (by simp [infer])
      have hkw : ∀ es, arg ≠ .kwargs es := by
        rintro es rfl; exact absurd ha (by simp [infer])
      have hfw : arg ≠ .fwd := by
        rintro rfl; exact absurd ha (by simp [infer])
      dsimp only
      rw [startArgs_plain hsp hkw hfw]
      exact inv_push hfs htab hsc hhook hsat hstr hcls hbot ha (KontOk.argsK hv hsg hk')
    -- **The zero-argument dispatch** (L152). `applyKont` runs `startArgs … [] []`,
    -- which is `finishSend` with no argument continuation in between — so this case
    -- ends where `argsK`'s does, one step earlier, and it is `entry_dispatch` at
    -- `args = []` rather than a second dispatch lemma. `ValuesTy _ [] []` is
    -- `trivial`, which is the whole of what the empty parameter list costs.
    | @recvK0 _ _ _ _ _ _ mname τret k hsg hk' =>
      dsimp only
      -- **The two witness kinds land different steps** (L157), which is why
      -- `EntryOk` is a disjunction and why this case is the first to case on it.
      rcases htab τ mname _ (sigOf_declFor hsg) with hbi | ⟨mdu, cu, hresu, hnmu, hconfu⟩
      · obtain ⟨w, hw, hstep⟩ :=
          entry_dispatch (m := { m with kont := k }) (recv := v) (args := [])
            hbi hv trivial
        rw [hstep]
        exact inv_value hfs htab hsc hhook hsat hstr hcls hbot hw hk'
      · -- The user branch: no value, a **frame**. `user_dispatch` supplies the step;
        -- the heap is untouched, so all five heap conjuncts pass straight through and
        -- what is left is the push and the callee's `CtlOk`.
        have hru := hresu _ (valueTy_tyClass hv)
        have hown : (m.heap.classPayload? mdu.owner).isSome := by
          obtain ⟨_, _, _, _, _, _, _, _, h9, _⟩ := hru; exact h9
        rw [user_dispatch (m := { m with kont := k }) hru hv]
        have hlt : ∀ g ∈ m.stack, g < m.frames.size := hfs.mem_lt
        obtain ⟨hdp, hdfu, Γb, hbodyu⟩ := hconfu
        refine ⟨hhook, hsat, hstr, hcls,
          BottomObj_cons hf.1 (BottomObj_push hlt hbot), _, cu, [], (ctx, Γ) :: Γs,
          htab, ?_, ?_, ?_⟩
        · refine ⟨by rw [Array.size_push]; exact Nat.lt_succ_self _, hlt, ?_,
            FramesOk.push hfs⟩
          rw [getD_push_lt_self]
          -- `FrameConforms` at the activation: `userFrame` leaves `captured` at its
          -- default, its definee **is** `md.owner`, and `ResolvesUser` carries that
          -- that id is a class — the clause the user arm has and `ResolvesAt` does
          -- not need.
          exact ⟨rfl, hown, by simp [envGet?]⟩
        · -- **The activation's static context is the owner's class name** (F1b.9),
          -- which is the clause `UserEntryOk` carries beside the body's typing: the
          -- body was checked in the class it is defined on, and `userFrame`'s definee
          -- **is** `md.owner`. `defVis` is the frame literal's default, which is what
          -- makes a `def` in a method body public — and it is `UserConforms`'s
          -- `defFree` restriction, not this, that keeps one out of the fragment.
          refine ⟨?_, ?_, ?_, StackCtx.push hlt hsc⟩
          · rw [getD_push_lt_self]; exact hown
          · rw [getD_push_lt_self]; exact hnmu
          · rw [getD_push_lt_self]; exact fun _ => rfl
        · -- The callee's body, typed at the **declared return type**: that is what
          -- makes `frameK` — which has always resumed the caller at the in-flight
          -- type — line the activation's answer up with the send's continuation.
          exact ⟨τret, Γb, _, hbodyu, KontOk.frameK hk'⟩
    | @argsK _ _ _ _ _ _ mname recv τr τret k hrv hsg hk' =>
      -- **F1a: one dispatch step for every declared method**, where P0 had a
      -- three-way `rcases` over the tabulated names and a rewrite per name. The
      -- invariant supplies the entry, `entry_dispatch` supplies the step, and the
      -- ~128 conformance lemmas of F6 become witnesses of the same clause rather
      -- than a parallel obligation (`typing-a-mutable-method-table.md` §7).
      dsimp only
      simp only [List.nil_append]
      -- **The user arm is refuted rather than handled**, and by arithmetic rather
      -- than by anything about dispatch: `UserConforms` requires `d.params = []`
      -- (a zero-parameter method is all `enterUserMethod` binds today) while this
      -- declaration's is `[τ]`. So a unary send is a builtin send, necessarily.
      have hbi : BuiltinEntryOk m.heap τr mname { params := [τ], ret := τret } := by
        rcases htab τr mname _ (sigOf_declFor hsg) with hb | ⟨_, _, _, _, hdp, _, _⟩
        · exact hb
        · exact absurd hdp (by simp)
      obtain ⟨w, hw, hstep⟩ :=
        entry_dispatch (m := { m with kont := k }) (recv := recv) (args := [v])
          hbi hrv (And.intro hv trivial)
      rw [hstep]
      exact inv_value hfs htab hsc hhook hsat hstr hcls hbot hw hk'
  · -- ## control = jump: excluded by `CtlOk`
    rw [hctl] at hc
    exact hc.elim
end Static
end Proof
end RubyCore
