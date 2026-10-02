import Denote.Sem.Instance.MethodCode

/-! Class singleton methods dispatch from an eigenclass but keep the lexical class as
definee (frame defmod) and constant scope. The two owners stay distinct. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

structure SingletonMethodCode (lexical owner : ObjId) (md : MethodDef) : Prop where
  owner : md.owner = owner
  cref : md.cref = [lexical]
  superName : md.superName = none
  builtin : md.builtin = none
  captured : md.capturedFrame = none
  declared : md.declared = []
  fromPrelude : md.fromPrelude = false
  visibilityOnly : md.visibilityOnly = false
  fromBlock : md.fromBlock = false
  forTargets : md.forTargets = none
  /-- Actual def-self records the lexical class as definee. -/
  definee : md.definee.getD md.owner = lexical
  definitionFrame : md.definitionFrame = none
  visibility : md.visibility = .pub

def singletonMethodCodeB (lexical owner : ObjId) (md : MethodDef) : Bool :=
  decide (md.owner = owner ∧ md.cref = [lexical] ∧ md.superName = none ∧ md.builtin = none ∧
    md.capturedFrame = none ∧ md.declared = [] ∧ md.fromPrelude = false ∧
    md.visibilityOnly = false ∧ md.fromBlock = false ∧ md.forTargets = none ∧
    md.definee.getD md.owner = lexical ∧ md.definitionFrame = none ∧ md.visibility = .pub)

theorem singletonMethodCodeB_sound {lexical owner : ObjId} {md : MethodDef}
    (h : singletonMethodCodeB lexical owner md = true) : SingletonMethodCode lexical owner md := by
  simp only [singletonMethodCodeB, decide_eq_true_eq] at h
  obtain ⟨a, b, c, d, e, f, g, i, j, k, l, n, o⟩ := h
  exact ⟨a, b, c, d, e, f, g, i, j, k, l, n, o⟩

end Ratchet.Denote
