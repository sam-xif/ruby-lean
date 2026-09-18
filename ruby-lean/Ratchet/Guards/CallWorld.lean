import Ratchet.Guards.ClassCtx

/-! Existing context data identifies the ordinary callers whose state we can restore. -/
set_option autoImplicit false
namespace Ratchet

inductive CallWorld (κ : Ctx) : Prop where
  | main : κ.scope.runtimeMain = true → κ.pos.mainWorld = true →
      κ.scope.runtimeClass = none → CallWorld κ
  | inst {owner recv : String} {fields : Ty} : κ.scope.runtimeMain = false →
      κ.scope.runtimeClass = some owner → κ.selfTy = some (.inst recv fields) →
      owner ∈ κ.classes.map (·.name) → recv ∈ κ.classes.map (·.name) → CallWorld κ

def callWorldB (κ : Ctx) : Bool :=
  if κ.scope.runtimeMain then κ.pos.mainWorld && κ.scope.runtimeClass.isNone else
  match κ.scope.runtimeClass, κ.selfTy with
  | some owner, some (.inst recv _) =>
    (κ.classes.map (·.name)).contains owner && (κ.classes.map (·.name)).contains recv
  | _, _ => false

theorem callWorldB_sound {κ : Ctx} (h : callWorldB κ = true) : CallWorld κ := by
  cases hm : κ.scope.runtimeMain with
  | true =>
    simp only [callWorldB, hm, ↓reduceIte, Bool.and_eq_true] at h
    exact .main hm h.1 (Option.isNone_iff_eq_none.mp h.2)
  | false =>
    cases ho : κ.scope.runtimeClass with
    | none => simp [callWorldB, hm, ho] at h
    | some owner =>
      cases hs : κ.selfTy with
      | none => simp [callWorldB, hm, ho, hs] at h
      | some ty =>
        cases ty <;> simp only [callWorldB, hm, ho, hs, Bool.false_eq_true, ↓reduceIte] at h
        all_goals first | contradiction | skip
        rename_i recv fields
        simp only [Bool.and_eq_true] at h
        exact .inst hm ho hs (by simpa using h.1) (by simpa using h.2)

end Ratchet
