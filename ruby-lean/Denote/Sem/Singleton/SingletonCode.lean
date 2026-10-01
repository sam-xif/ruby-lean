import Denote.Sem.Instance.MethodCode

/-! Class singleton methods dispatch from an eigenclass but retain the lexical class's
constant scope. These two owners must remain distinct at installation and entry. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

structure SingletonMethodCode (lexical owner : ObjId) (md : MethodDef) : Prop
    extends OrdinaryMethodCode owner [lexical] md where
  visibility : md.visibility = .pub

def singletonMethodCodeB (lexical owner : ObjId) (md : MethodDef) : Bool :=
  ordinaryMethodCodeB owner [lexical] md && decide (md.visibility = .pub)

theorem singletonMethodCodeB_sound {lexical owner : ObjId} {md : MethodDef}
    (h : singletonMethodCodeB lexical owner md = true) : SingletonMethodCode lexical owner md := by
  simp only [singletonMethodCodeB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨ordinaryMethodCodeB_sound h.1, h.2⟩

end Ratchet.Denote
