import Ratchet.CheckInit
import Denote.Typed.InitWrite

/-! Initializer derivations mean the anchored fresh-receiver contract, not ordinary
Framed preservation. This fundamental lemma is generic in every class/body/annotation.
Before using InitJudge as a DJudge premise, the registry must carry both initializer families. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem initJudge_sem {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {e : Ratchet.Expr}
    (h : InitJudge κ Γ I e τ κ' Γ' I') : SemInitA κ Γ I e τ κ' Γ' I' := by
  refine InitJudge.rec
    (motive_1 := fun κ Γ I e τ κ' Γ' I' _ => SemInitA κ Γ I e τ κ' Γ' I')
    (motive_2 := fun κ Γ I es τ κ' Γ' I' _ => SemInitSeqA κ Γ I es τ κ' Γ' I')
    ?_ ?_ ?_ ?_ ?_ ?_ h
  · intros; apply SemInitA.var <;> assumption
  · intros; apply SemInitA.ivarAsgnChecked <;> assumption
  · intros; apply SemInitA.sequence; assumption
  · intros; apply SemInitA.ignoreResult; assumption
  · intros; apply SemInitSeqA.last; assumption
  · intros; apply SemInitSeqA.cons <;> assumption

theorem _root_.Ratchet.CheckedInitializer.sem {κ : Ctx} {decl : Defn} (c : CheckedInitializer κ decl) :
    SemInitA κ c.params .ivar0 decl.body c.ret κ c.out c.fields := initJudge_sem c.judged

#print axioms initJudge_sem
#print axioms CheckedInitializer.sem
end Ratchet.Denote.Typed
