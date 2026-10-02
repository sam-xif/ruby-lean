import Denote.Rules.Method.MethodDispatch
import Denote.Sem.Class.ClassScope
import Ratchet.Guards.ClassGuards

/-! Ordinary instance-method metadata at a requested class scope. This is installation,
not body admission: annotated body checking is a separate obligation. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

variable {m : Machine} {cn : String}

theorem currentDefinitionFrame_self (hs : m.stack ≠ [])
    (hd : m.currentFrame.definitionFrame = none) : m.currentDefinitionFrame = m.currentFrame := by
  cases hst : m.stack with
  | nil => exact absurd hst hs
  | cons fid rest =>
    have hc : m.currentFrame = m.frames.getD fid default := by
      simp [Machine.currentFrame, hst, Array.getD_eq_getD_getElem?]
    rw [hc] at hd ⊢
    simp only [Machine.currentDefinitionFrame, Machine.definitionFrameId, hst, List.headD_cons]
    unfold Machine.definitionFrameId.go
    rw [hd]

/-- A requested scope supplies definition metadata in every conformant state, not only
the fresh-entry witness. Body typing remains a separate premise of admission. -/
theorem scoped_defined_instanceCode {name : String} {ps : List RubyCore.Param}
    {code : RubyCore.Expr} {k : ObjId} (h : ClassScopeAt cn k m) (hs : m.stack ≠ [])
    (hn : autoPrivateNames.contains name = false) :
    InstanceMethodCode k name (definedMethod m name ps code) := by
  have hdef := currentDefinitionFrame_self hs h.defFrame
  have hvis : m.currentFrame.defVis = .pub := by
    have hv := h.visibility
    unfold defaultDefVis at hv
    split at hv
    · cases hv
    · exact hv
  have hcode : OrdinaryMethodCode k [k] (definedMethod m name ps code) := by
    unfold definedMethod Interp.normalizeDefinitionVisibility
    split <;> exact ⟨h.owner, h.cref, rfl, rfl, rfl, rfl,
      by simp [sourceMethod, h.phase, h.origin], rfl, rfl, rfl, h.owner, rfl, rfl⟩
  refine ⟨hcode, ?_⟩
  unfold definedMethod Interp.normalizeDefinitionVisibility
  rw [h.owner, h.detached]
  by_cases hi : name = "initialize"
  · subst hi; rfl
  · have hne : (name == "initialize") = false := by simpa using hi
    have hl : (["initialize", "initialize_copy", "initialize_dup", "initialize_clone"].contains name) = false := by
      simp only [autoPrivateNames, List.contains_cons, List.contains_nil, Bool.or_false,
        Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hn ⊢
      exact ⟨fun he => hi he, hn.1, hn.2.1, hn.2.2.1⟩
    simp only [hl, hne, Bool.false_and, Bool.false_eq_true, ↓reduceIte, sourceMethod, hdef, hvis]

theorem scoped_defHookQuiet {k : ObjId} (h : ClassScopeAt cn k m) : DefHookQuiet m :=
  defHookQuietB_sound (by simpa only [defHookQuietB, h.owner] using h.hook)

#print axioms currentDefinitionFrame_self
#print axioms scoped_defined_instanceCode
end Ratchet.Denote.Typed
