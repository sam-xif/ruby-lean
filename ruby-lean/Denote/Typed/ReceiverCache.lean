import Ratchet.ReceiverCache
import Denote.Typed.InitChecked
import Denote.Typed.Bridge
import Denote.Typed.InheritedConstructor
import Denote.Typed.InheritedRun
import Denote.Sem.ClassGuards

/-! Receiver-cache artifacts supply the full annotation-domain proofs to real dispatch.
These lemmas quantify over every class/owner/body; no cache signature is an axiom. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem checked_inherited_constructor_run {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {c : Cls} {args : List Value} (b : CallableInitializerAt κ c)
    (hm : StateOk κ Γ I m) (hc : c ∈ κ.classes)
    (hnew : smroGet? κ.classes c.name "new" = none) (halloc : c.name ∈ κ.pos.plainAlloc)
    (hg : mainCallB κ Γ I = true) (hkont : m.kont = [])
    (hargs : DenAll (b.body.params.map (·.2)) m args) :
    ∃ k n, classNamed? m.heap c.name = some k ∧
      Interp.finishSend m (.ref k) .explicit "new" args .none = .next n ∧
      RunSpec m n Γ (.inst c.name b.body.fields) κ I := by
  simp only [mainCallB, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨ht, hΓ⟩, hasms, hmain, hw, hcl, hco⟩ := hg
  exact declared_inherited_constructor_run hm hc b.route.member b.route.installed b.nameOk
    b.route.chain b.route.clear hnew halloc b.body.paramShape b.body.paramsFO
    (by simpa only [b.route.nameOk] using b.body.sem)
    (reframeTypesB_sound ht) hasms hmain hw hcl
    (fun x => (constGet?_empty (κ := initializerBodyCtxAt κ c.name b.route.cls.name) hco x).trans
      (constGet?_empty hco x).symm)
    (List.all_eq_true.mp hΓ) b.body.fieldsFO hkont hargs

/-- Native-prefix interception remains explicit; a cached body cannot waive it. -/
theorem checked_inherited_member_run {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {c : Cls} {name : String} {sendSite : SendSite} {recv : Value} {args : List Value}
    (b : CallableMemberAt κ c name) (hm : StateOk κ Γ I m) (hc : c ∈ κ.classes)
    (hg : instanceCallB κ Γ I = true) (hkont : m.kont = [])
    (hv : denM (.inst c.name b.fields) m recv)
    (hargs : DenAll (b.body.params.map (·.2)) m args)
    (hn : b.decl.name ≠ "initialize") (hname : DirectSendName b.decl.name)
    (hshadow : ∀ k, classNamed? m.heap b.route.cls.name = some k → Interp.crubyShadow m.heap
      ((ancestors m.heap (classOf m.heap recv)).takeWhile (· != k)) b.decl.name = none) :
    ∃ n, Interp.finishSend m recv sendSite b.decl.name args .none = .next n ∧
      RunSpec m n Γ b.body.ret κ I := by
  simp only [instanceCallB, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨ht, hΓ⟩, hw⟩, hasms, hco⟩ := hg
  exact declared_inherited_run b.body.paramShape b.body.paramsFO b.body.returnFO
    (by simpa only [b.route.nameOk] using djudge_context b.body.judged)
    hm (reframeTypesB_sound ht) hasms hc b.route.member b.route.installed b.route.chain b.route.clear
    (callWorldB_sound hw) hkont b.fieldsFO hv (by simpa using denAll_length hargs) hargs
    (fun x => (constGet?_empty (κ := instanceBodyCtx κ ⟨c.name, b.route.cls.name, b.decl.name⟩ b.fields)
      hco x).trans (constGet?_empty hco x).symm)
    (List.all_eq_true.mp hΓ) (fun _ _ => Or.inr hname) hn hshadow

#print axioms checked_inherited_constructor_run
#print axioms checked_inherited_member_run
end Ratchet.Denote.Typed
