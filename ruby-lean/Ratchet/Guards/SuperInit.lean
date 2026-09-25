import Ratchet.Guards.ClassGuards
import Ratchet.Guards.SuperRoute
import Ratchet.Guards.WriteTypes

/-! Checkable obligations for explicit parent initialization on the current receiver. -/
set_option autoImplicit false
namespace Ratchet

def frameIsB (κ : Ctx) (recv owner name : String) : Bool :=
  κ.frame.any fun f => f.recvClass == recv && f.defClass == owner && f.methName == name

theorem frameIsB_sound {κ : Ctx} {recv owner name : String} (h : frameIsB κ recv owner name = true) :
    κ.frame = some ⟨recv, owner, name⟩ := by
  cases hf : κ.frame with
  | none => simp [frameIsB, hf] at h
  | some f =>
    rcases f with ⟨r, o, n⟩
    simp only [frameIsB, hf, Option.any_some, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
    rfl

def superInitB (κ : Ctx) (Γ : Env) (I Ib : Ty) (c : Cls) (current : String)
    (d : Defn) (ps : List (String × Ty)) (τ : Ty) : Bool :=
  frameIsB κ c.name current d.name && reframeTypesB κ I && reframeTypesB κ Ib &&
    Γ.all (fun p => IvarStable (stripAlias p.2)) &&
    paramEqAll d.params (ps.map (fun p => Param.req p.1)) &&
    ps.all (fun p => FirstOrder p.2 && !isAliasTy p.2) && FirstOrder τ &&
    decide (κ.asms = [] ∧ κ.consts = [] ∧ κ.scope.runtimeMain = false ∧
      κ.scope.runtimeClass = some current ∧ κ.blockTy = none ∧
      κ.selfTy = some (.inst c.name .ivar0) ∧ κ.scope.closedIvars = true ∧
      d.name = "initialize" ∧ current ∈ κ.classes.map (·.name))

structure SuperInitReady (κ : Ctx) (Γ : Env) (I Ib : Ty) (c : Cls) (current : String)
    (d : Defn) (ps : List (String × Ty)) (τ : Ty) : Prop where
  frame : κ.frame = some ⟨c.name, current, d.name⟩
  input : reframeTypesB κ I = true
  output : reframeTypesB κ Ib = true
  locals : ∀ p ∈ Γ, IvarStable (stripAlias p.2) = true
  params : d.params = ps.map (fun p => Param.req p.1)
  paramsFO : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false
  ret : FirstOrder τ = true
  asms : κ.asms = []
  consts : κ.consts = []
  main : κ.scope.runtimeMain = false
  scope : κ.scope.runtimeClass = some current
  block : κ.blockTy = none
  self : κ.selfTy = some (.inst c.name .ivar0)
  closed : κ.scope.closedIvars = true
  name : d.name = "initialize"
  current : current ∈ κ.classes.map (·.name)

theorem superInitB_sound {κ : Ctx} {Γ : Env} {I Ib : Ty} {c : Cls} {current : String}
    {d : Defn} {ps : List (String × Ty)} {τ : Ty} (h : superInitB κ Γ I Ib c current d ps τ = true) :
    SuperInitReady κ Γ I Ib c current d ps τ := by
  simp only [superInitB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.not_eq_true'] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨hf, hi⟩, ho⟩, hl⟩, hp⟩, hps⟩, hr⟩,
    ha, hconst, hmain, hclass, hblock, hself, hclosed, hn, hcurrent⟩
  exact ⟨frameIsB_sound hf, hi, ho, hl, paramEqAll_sound hp, hps, hr,
    ha, hconst, hmain, hclass, hblock, hself, hclosed, hn, hcurrent⟩

end Ratchet
