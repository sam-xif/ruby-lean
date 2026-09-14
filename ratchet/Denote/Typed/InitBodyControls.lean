import Denote.Typed.InitExpr
import Denote.Sem.Reframe

/-! The complete 061 initializer body, from its Integer parameter annotations.
This is a semantic body pilot, not class/constructor admission by the validator.
-/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private theorem int_after_write {m : Machine} {x : String} {v w : Value}
    (h : denM .int m w) : denM .int (Interp.bindIvar m x v) w := by
  simpa only [denM] using h

private theorem integer_field_write {anchor : Heap} {κ : Ctx} {Γ : Env} {I : Ty}
    {m : Machine} {x cn : String} {v : Value}
    (hm : InitState anchor κ Γ I m) (hv : denM .int m v)
    (he : ∀ y τ, envGet? Γ y = some τ → stripAlias τ = .int)
    (hi : ∀ y τ, ivarGet? I y = some τ → τ = .int)
    (hs : κ.selfTy = some (.inst cn .ivar0)) (hb : κ.blockTy = none) (hc : κ.consts = []) :
    InitState anchor κ Γ (ivarSet I x .int) (Interp.bindIvar m x v) ∧
      denM .int (Interp.bindIvar m x v) v := by
  obtain ⟨o, ho, hfresh, hlive, hfrozen⟩ := hm.fresh
  have hv' := int_after_write (x := x) (v := v) hv
  have henv : EnvOk Γ (Interp.bindIvar m x v) := env_bindIvar hm.typed.env (by
    intro y τ hy
    have hden := (hm.typed.env.1 y τ hy).1
    rw [he y τ hy] at hden ⊢
    exact int_after_write hden)
  have hspine : SelfSpineOk (ivarSet I x .int) (Interp.bindIvar m x v) :=
    selfSpine_bindIvar ho hlive hm.typed.selfSpine hv' (by
      intro y τ _ hy
      have hd := denSpineFrom_get hm.typed.selfSpine.1 (by simp) hy
      rw [hi y τ hy, ho] at hd
      rw [hi y τ hy]
      exact int_after_write hd)
  refine ⟨⟨StateOk_bindIvar hm.typed x v henv hspine ?_ ?_ ?_ ?_,
    hm.growth.bindIvar ho hfresh x v, ?_⟩, hv'⟩
  · simpa only [BlockTyOk, hb, bindIvar_currentFrame] using hm.typed.blockTy
  · simpa only [SelfTyOk, hs, denM, denSpineFrom, and_true, bindIvar_currentFrame,
      bindIvar_isExactInst] using hm.typed.selfTy
  · intro n τ hn
    rw [constGet?_empty hc n] at hn
    cases hn
  · simp [ConstPathsOk, hc, envGet?]
  · exact ⟨o, by simpa only [bindIvar_currentFrame] using ho, hfresh,
      by simpa only [bindIvar_size] using hlive,
      by simpa only [(bindIvar_ivarOnly m x v).frozen] using hfrozen⟩

def pointInitParams : Env := [("x", .int), ("y", .int)]
def pointInitBody : Ratchet.Expr :=
  .seq [.vasgn .ivar "@x" (.var .lvar "x"), .vasgn .ivar "@y" (.var .lvar "y")]
def pointInitSpine : Ty := .ivarCons "@x" .int (.ivarCons "@y" .int .ivar0)

/-- No call arguments occur in the theorem: the full body uses the annotated domain. -/
theorem point_initializer_sem {κ : Ctx} {cn : String}
    (hs : κ.selfTy = some (.inst cn .ivar0)) (hb : κ.blockTy = none) (hc : κ.consts = []) :
    SemInitA κ pointInitParams .ivar0 pointInitBody .any κ pointInitParams pointInitSpine := by
  have he (y : String) (τ : Ty) (hy : envGet? pointInitParams y = some τ) : stripAlias τ = .int := by
    obtain ⟨z, hz⟩ := envGet?_mem hy
    simp only [pointInitParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hz
    rcases hz with ⟨_, ht⟩ | ⟨_, ht⟩ <;> rw [ht] <;> rfl
  have hx : SemInitA κ pointInitParams .ivar0 (.vasgn .ivar "@x" (.var .lvar "x")) .int
      κ pointInitParams (.ivarCons "@x" .int .ivar0) :=
    SemInitA.ivarAsgn (SemInitA.var rfl rfl) (fun _ _ _ hm hv =>
      integer_field_write (x := "@x") hm hv he (by intro y τ hy; cases hy) hs hb hc)
  have hy : SemInitA κ pointInitParams (.ivarCons "@x" .int .ivar0)
      (.vasgn .ivar "@y" (.var .lvar "y")) .int κ pointInitParams pointInitSpine :=
    SemInitA.ivarAsgn (SemInitA.var rfl rfl) (fun _ _ _ hm hv =>
      integer_field_write (x := "@y") hm hv he (by
        intro y τ hy
        simp only [ivarGet?] at hy
        split at hy
        · exact (Option.some.inj hy).symm
        · cases hy) hs hb hc)
  exact (SemInitA.sequence (.cons hx (.last hy))).ignoreResult

-- Discarding the result never discards outgoing conformance or all-fuel safety.
theorem point_initializer_safe {anchor : Heap} {κ : Ctx} {cn : String} {m : Machine}
    (hs : κ.selfTy = some (.inst cn .ivar0)) (hb : κ.blockTy = none) (hc : κ.consts = [])
    (hm : InitState anchor κ pointInitParams .ivar0 m) : StuckFree m pointInitBody :=
  (point_initializer_sem hs hb hc anchor m hm).1

theorem point_initializer_self_type {anchor : Heap} {κ : Ctx} {cn : String} {m n : Machine}
    {fuel rest : Nat} {v : Value}
    (hs : κ.selfTy = some (.inst cn .ivar0)) (hb : κ.blockTy = none) (hc : κ.consts = [])
    (hm : InitState anchor κ pointInitParams .ivar0 m)
    (hr : runA fuel (evalFrom m pointInitBody) = .ans (.val v) n rest) :
    denM (.inst cn pointInitSpine) n n.currentFrame.self := by
  have hn := ((point_initializer_sem hs hb hc anchor m hm).2 fuel (.val v) n rest hr).2.2 v rfl
  have ht := hn.typed.selfTy
  simp only [SelfTyOk, hs, denM, denSpineFrom, and_true] at ht
  rw [denM]
  exact ⟨ht, hn.typed.selfSpine.1⟩

-- Updating a visible binding does not revive its shadowed, differently typed duplicate.
example {m : Machine} {o : ObjId} (hs : m.currentFrame.self = .ref o)
    (ho : o < m.heap.objs.size)
    (hi : SelfSpineOk (.ivarCons "@x" .nilT (.ivarCons "@x" .bool .ivar0)) m) :
    SelfSpineOk (.ivarCons "@x" .int (.ivarCons "@x" .bool .ivar0))
      (Interp.bindIvar m "@x" (.int 1)) :=
  selfSpine_bindIvar (x := "@x") (ρ := .int) (v := .int 1) hs ho hi (by simp [denM, isIntV]) (by
    intro y τ hy hg
    simp [ivarGet?, Ne.symm hy] at hg)

-- The scoped run contract cannot claim a wrong type, even at execution bound zero.
example (anchor : Heap) (origin m : Machine) (κ : Ctx) (Γ : Env) (I : Ty) :
    ¬ InitRunSpec anchor origin (deliverA (.val (.int 1)) m []) Γ .bool κ I := by
  intro h
  have hr := h.2 0 (.val (.int 1)) (deliverA (.val (.int 1)) m []) 0 (by
    rw [runA_ans (by rfl)])
  have hb := hr.2.1
  simp only [AnsOk, denM, isBoolV, Bool.false_eq_true] at hb

#print axioms point_initializer_sem
#print axioms point_initializer_safe
#print axioms point_initializer_self_type
end Ratchet.Denote.Typed
