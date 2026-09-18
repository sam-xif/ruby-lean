import Ratchet.Check.CheckInit
import Denote.Rules.Init.InitBridge

/-! Initializer derivations mean the anchored fresh-receiver contract, not ordinary
Framed preservation. This fundamental lemma is generic in every class/body/annotation.
Both initializer families are interpreted through the rule registry. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem initJudge_sem {κ κ' : Ctx} {Γ Γ' : Env} {I I' τ : Ty} {e : Ratchet.Expr}
    (h : InitJudge κ Γ I e τ κ' Γ' I') : SemInitA κ Γ I e τ κ' Γ' I' :=
  initJudge_certified h dsemFam (closed_target dclinks)

theorem _root_.Ratchet.CheckedInitializer.sem {κ : Ctx} {decl : Defn} (c : CheckedInitializer κ decl) :
    SemInitA κ c.params .ivar0 decl.body c.ret κ c.out c.fields := initJudge_sem c.judged

#print axioms initJudge_sem
#print axioms CheckedInitializer.sem
end Ratchet.Denote.Typed
