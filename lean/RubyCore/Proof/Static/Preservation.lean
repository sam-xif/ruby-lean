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
  obtain ⟨htab, hhook, hsat, hstr, hcls, hbot, Γ, Γs, hfs, hc⟩ := h
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
      exact inv_value hfs htab hhook hsat hstr hcls hbot rfl hk
    case tru =>
      simp only [infer, Option.some.injEq, Prod.mk.injEq] at hinf
      obtain ⟨rfl, rfl⟩ := hinf
      exact inv_value hfs htab hhook hsat hstr hcls hbot rfl hk
    case fls =>
      simp only [infer, Option.some.injEq, Prod.mk.injEq] at hinf
      obtain ⟨rfl, rfl⟩ := hinf
      exact inv_value hfs htab hhook hsat hstr hcls hbot rfl hk
    case nil =>
      simp only [infer, Option.some.injEq, Prod.mk.injEq] at hinf
      obtain ⟨rfl, rfl⟩ := hinf
      exact inv_value hfs htab hhook hsat hstr hcls hbot rfl hk
    -- **The producer** (L151). One allocation, no continuation, no dispatch: the
    -- whole case is `plainGrow_alloc` for the step, `valueTy_alloc_fresh` for the
    -- value, and `inv_grow_value` — proved a rung earlier — for everything else.
    -- That the case is this short is the measurement L149 was for.
    case str s =>
      simp only [infer, Option.some.injEq, Prod.mk.injEq] at hinf
      obtain ⟨rfl, rfl⟩ := hinf
      exact inv_grow_value hfs htab hhook hsat hstr hcls hbot
        (plainGrow_alloc m.heap _ (by simp))
        rfl rfl rfl
        (valueTy_alloc_fresh (by simp) rfl hstr.1 hstr.2) hk
    case var k x =>
      cases k
      case lvar =>
        simp only [infer, Option.map_eq_some_iff] at hinf
        obtain ⟨σ, hg, heq⟩ := hinf
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact inv_value hfs htab hhook hsat hstr hcls hbot (hl x _ hg) hk
      all_goals (simp only [infer] at hinf; contradiction)
    case vasgn k x rhs =>
      cases k
      case lvar =>
        simp only [infer] at hinf
        split at hinf
        · rename_i σ Γ₁ hrhs
          simp only [Option.some.injEq, Prod.mk.injEq] at hinf
          obtain ⟨rfl, rfl⟩ := hinf
          exact inv_push hfs htab hhook hsat hstr hcls hbot hrhs (KontOk.asgn hk)
        · exact absurd hinf (by simp)
      all_goals (simp only [infer] at hinf; contradiction)
    case seq es =>
      simp only [infer] at hinf
      cases es with
      | nil =>
        simp only [inferSeq, Option.some.injEq, Prod.mk.injEq] at hinf
        obtain ⟨rfl, rfl⟩ := hinf
        exact inv_value hfs htab hhook hsat hstr hcls hbot rfl hk
      | cons e₁ rest =>
        cases rest with
        | nil =>
          simp only [inferSeq] at hinf
          exact inv_eval hfs htab hhook hsat hstr hcls hbot hinf hk
        | cons e₂ rest' =>
          simp only [inferSeq] at hinf
          split at hinf
          · rename_i σ Γ₁ h₁
            exact inv_push hfs htab hhook hsat hstr hcls hbot h₁ (KontOk.seqCons hinf hk)
          · exact absurd hinf (by simp)
    case if' c t els =>
      simp only [infer] at hinf
      split at hinf
      · rename_i σ Γ₁ hcnd
        exact inv_push hfs htab hhook hsat hstr hcls hbot hcnd (KontOk.ifK hinf hk)
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
              exact inv_push hfs htab hhook hsat hstr hcls hbot hcnd
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
      obtain ⟨k, cp, hconst, hpay, hmod⟩ := hcls name (List.mem_of_elem_eq_true hmem)
      simp only [evalExpr, enterClassBody, hdefmod, hconst, hpay, hmod, withKont]
      -- What is left is `pushFrame`, and it is a frame push on an untouched heap.
      have hlt : ∀ g ∈ m.stack, g < m.frames.size := hfs.mem_lt
      refine ⟨htab, hhook, hsat, hstr, hcls,
        BottomObj_cons hf.1 (BottomObj_push hlt hbot), [], [Γ'], ?_, ?_⟩
      · refine ⟨by rw [Array.size_push]; exact Nat.lt_succ_self _, hlt, ?_,
          FramesOk.push hfs⟩
        rw [getD_push_lt_self]
        -- `FrameConforms` at the class-body frame: no captured chain (the literal
        -- leaves the field at its default), the definee is a class — which is
        -- exactly `ClassOk`'s second conjunct, and is what L154 generalized this
        -- clause to admit — and the empty environment types nothing.
        exact ⟨rfl, by simp [hpay], by simp [envGet?]⟩
      · exact ⟨τ, Γb, hbody, KontOk.frameK hk⟩
    case def' name params body =>
      obtain ⟨rfl, rfl, rfl, hfresh, hha⟩ := infer_def_inv hinf
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
          TypeAgree m.heap m₀.heap → DeclsOk D m₀.heap → NoHook m₀.heap →
          Saturated m₀.heap → StrClsOk m₀.heap → ClassOk m₀.heap →
          Inv D (withCtl m₀ (.value (.sym name))) := by
        intro m₀ hfr hst hko hag ht' hh' hsat' hstr' hcls'
        refine ⟨ht', hh', hsat', hstr', hcls',
          show BottomObj m₀.frames m₀.stack by rw [hfr, hst]; exact hbot, Γ', Γs, ?_, ?_⟩
        · show FramesOk m₀.heap m₀.frames m₀.stack (Γ' :: Γs)
          rw [hfr, hst]; exact FramesOk.heap_congr hag hfs
        · show ∃ σ, ValueTy m₀.heap (Value.sym name) σ ∧
              KontOk D m₀.heap (Γ' :: Γs) σ m₀.kont
          exact ⟨.sym, rfl, by rw [hko]; exact KontOk.heap_congr hag hk⟩
      -- `hlk` collapses the hook lookup to `none`, after which only the
      -- `preludeMode` `if` remains.
      simp only [evalExpr, hdm]
      -- `split` would dive into the `visibility` `if`s *inside* the `MethodDef`
      -- literal, which `hres` deliberately abstracts over; case on the one
      -- condition that matters instead.
      by_cases hp : m.preludeMode = true <;>
        simp only [hp, if_true, if_false, Bool.false_eq_true, hlk] <;>
        refine hres _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
          first
            | rfl
            | exact typeAgree_defineMethod _ _ _ _
            | exact DeclsOk_defineMethod htab hfresh
            | exact hlkNH _
            -- L148: the third heap conjunct, and `defineMethod` preserves it for the
            -- same reason it preserves the other two — it moves no id.
            | exact Saturated_defineMethod hsat _ _ _
            -- L151: the fourth, and the same reason a fourth time.
            | exact StrClsOk_defineMethod hstr
            -- L156: the sixth, and the case that matters is a `def` inside the very
            -- class body being reopened — `constOwn` reads `consts`, `defineMethod`
            -- writes `methods`.
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
              try exact inv_push hfs htab hhook hsat hstr hcls hbot hr (KontOk.recvK0 hsg hk)
            exact absurd hr (by simp [infer])
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
                try exact inv_push hfs htab hhook hsat hstr hcls hbot hr (KontOk.recvK hsg ha hk)
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
      exact inv_value hfs htab hhook hsat hstr hcls hbot hv hk'
    | @seqCons Γ Γs τ e₁ es τ' Γ' k hseq hk' =>
      cases es with
      | nil =>
        simp only [inferSeq] at hseq
        exact inv_push hfs htab hhook hsat hstr hcls hbot hseq (KontOk.seqNil hk')
      | cons e₂ es' =>
        simp only [inferSeq] at hseq
        split at hseq
        · rename_i σ Γ₁ h₁
          exact inv_push hfs htab hhook hsat hstr hcls hbot h₁ (KontOk.seqCons hseq hk')
        · exact absurd hseq (by simp)
    | @asgn Γ Γs τ x k hk' =>
      -- The machine `applyKont` steps to is `{ m with kont := k }.setLocal x v`, and
      -- `hfs` is phrased over `m`. The two agree definitionally, but since L137 made
      -- `FramesOk` heap-indexed the elaborator resolves `?m` from `hfs` rather than
      -- from the goal, so the instance has to be named.
      refine ⟨htab, hhook, hsat, hstr, hcls, ?_, envSet Γ x τ, Γs, ?_, ⟨τ, hv, hk'⟩⟩
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
            · simp only [hb, if_true]; exact inv_eval hfs htab hhook hsat hstr hcls hbot ht hk'
            · simp only [hb]; exact inv_eval hfs htab hhook hsat hstr hcls hbot he hk'
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
            · simp only [hb, if_true]; exact inv_eval hfs htab hhook hsat hstr hcls hbot ht hk'
            · simp only [hb]; exact inv_value hfs htab hhook hsat hstr hcls hbot rfl hk'
          · exact absurd hif (by simp)
        · exact absurd hif (by simp)
    | @whileCond Γ Γs τ c body k hloop hk' =>
      obtain ⟨⟨σc, hcnd⟩, ⟨σb, hbody⟩⟩ := hloop
      by_cases hb : v.truthy
      · simp only [hb, if_true]
        exact inv_push hfs htab hhook hsat hstr hcls hbot hbody (KontOk.whileBody ⟨⟨σc, hcnd⟩, ⟨σb, hbody⟩⟩ hk')
      · simp only [hb]
        exact inv_value hfs htab hhook hsat hstr hcls hbot rfl hk'
    | @whileBody Γ Γs τ c body k hloop hk' =>
      obtain ⟨⟨σc, hcnd⟩, ⟨σb, hbody⟩⟩ := hloop
      exact inv_push hfs htab hhook hsat hstr hcls hbot hcnd (KontOk.whileCond ⟨⟨σc, hcnd⟩, ⟨σb, hbody⟩⟩ hk')
    | @frameK Γ Γ' Γs τ fid k hk' =>
      -- The activation pops: `frames` is untouched, `stack` loses its head, and
      -- the caller's environment — carried all along by `FramesOk` — becomes
      -- current again. This is the case L91 could not close.
      exact ⟨htab, hhook, hsat, hstr, hcls, BottomObj_tail hbot, Γ', Γs, hfs.tail,
        ⟨τ, hv, hk'⟩⟩
    | @recvK Γ Γs τ mname arg τp τret Γ₂ k hsg ha hk' =>
      have hsp : ∀ e, arg ≠ .splat e := by
        rintro e rfl; exact absurd ha (by simp [infer])
      have hkw : ∀ es, arg ≠ .kwargs es := by
        rintro es rfl; exact absurd ha (by simp [infer])
      have hfw : arg ≠ .fwd := by
        rintro rfl; exact absurd ha (by simp [infer])
      dsimp only
      rw [startArgs_plain hsp hkw hfw]
      exact inv_push hfs htab hhook hsat hstr hcls hbot ha (KontOk.argsK hv hsg hk')
    -- **The zero-argument dispatch** (L152). `applyKont` runs `startArgs … [] []`,
    -- which is `finishSend` with no argument continuation in between — so this case
    -- ends where `argsK`'s does, one step earlier, and it is `entry_dispatch` at
    -- `args = []` rather than a second dispatch lemma. `ValuesTy _ [] []` is
    -- `trivial`, which is the whole of what the empty parameter list costs.
    | @recvK0 Γ Γs τ mname τret k hsg hk' =>
      dsimp only
      -- **The two witness kinds land different steps** (L157), which is why
      -- `EntryOk` is a disjunction and why this case is the first to case on it.
      rcases htab τ mname _ (sigOf_declFor hsg) with hbi | ⟨mdu, hresu, hconfu⟩
      · obtain ⟨w, hw, hstep⟩ :=
          entry_dispatch (m := { m with kont := k }) (recv := v) (args := [])
            hbi hv trivial
        rw [hstep]
        exact inv_value hfs htab hhook hsat hstr hcls hbot hw hk'
      · -- The user branch: no value, a **frame**. `user_dispatch` supplies the step;
        -- the heap is untouched, so all five heap conjuncts pass straight through and
        -- what is left is the push and the callee's `CtlOk`.
        have hru := hresu _ (valueTy_tyClass hv)
        have hown : (m.heap.classPayload? mdu.owner).isSome := by
          obtain ⟨_, _, _, _, _, _, _, _, h9, _⟩ := hru; exact h9
        rw [user_dispatch (m := { m with kont := k }) hru hv]
        have hlt : ∀ g ∈ m.stack, g < m.frames.size := hfs.mem_lt
        obtain ⟨hdp, Γb, hbody⟩ := hconfu
        refine ⟨htab, hhook, hsat, hstr, hcls,
          BottomObj_cons hf.1 (BottomObj_push hlt hbot), [], Γ :: Γs, ?_, ?_⟩
        · refine ⟨by rw [Array.size_push]; exact Nat.lt_succ_self _, hlt, ?_,
            FramesOk.push hfs⟩
          rw [getD_push_lt_self]
          -- `FrameConforms` at the activation: `userFrame` leaves `captured` at its
          -- default, its definee **is** `md.owner`, and `ResolvesUser` carries that
          -- that id is a class — the clause the user arm has and `ResolvesAt` does
          -- not need.
          exact ⟨rfl, hown, by simp [envGet?]⟩
        · -- The callee's body, typed at the **declared return type**: that is what
          -- makes `frameK` — which has always resumed the caller at the in-flight
          -- type — line the activation's answer up with the send's continuation.
          exact ⟨τret, Γb, hbody, KontOk.frameK hk'⟩
    | @argsK Γ Γs τ mname recv τr τret k hrv hsg hk' =>
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
        rcases htab τr mname _ (sigOf_declFor hsg) with hb | ⟨_, _, hdp, _⟩
        · exact hb
        · exact absurd hdp (by simp)
      obtain ⟨w, hw, hstep⟩ :=
        entry_dispatch (m := { m with kont := k }) (recv := recv) (args := [v])
          hbi hrv (And.intro hv trivial)
      rw [hstep]
      exact inv_value hfs htab hhook hsat hstr hcls hbot hw hk'
  · -- ## control = jump: excluded by `CtlOk`
    rw [hctl] at hc
    exact hc.elim
end Static
end Proof
end RubyCore
