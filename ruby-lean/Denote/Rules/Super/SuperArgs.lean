import Denote.Rules.Super.SuperRun
import Denote.Rules.Method.MethodArgs

/-! Arbitrary-length explicit super arguments, evaluated left to right in the scoped
initializer contract. Earlier values retain IvarStable types through later writes. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

inductive SemInitAllA : Ctx → Env → Ty → List Ratchet.Expr → List Ty → Ctx → Env → Ty → Prop
  | nil {κ : Ctx} {Γ : Env} {I : Ty} : SemInitAllA κ Γ I [] [] κ Γ I
  | cons {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ σ : Ty}
      {e : Ratchet.Expr} {es : List Ratchet.Expr} {tys : List Ty} :
      SemInitA κ Γ I e σ κ₁ Γ₁ I₁ → SemInitAllA κ₁ Γ₁ I₁ es tys κ₂ Γ₂ I₂ →
      plainArgB e = true → IvarStable σ = true →
      SemInitAllA κ Γ I (e :: es) (σ :: tys) κ₂ Γ₂ I₂

theorem denAll_ivarStable {m n : Machine} {ts : List Ty} {vs : List Value}
    (ht : ∀ τ ∈ ts, IvarStable τ = true) (h : IvarTypePres m n) (hd : DenAll ts m vs) :
    DenAll ts n vs := by
  induction ts generalizing vs with
  | nil => cases vs <;> simp_all [DenAll]
  | cons t ts ih => cases vs with
    | nil => cases hd
    | cons v vs => exact ⟨h t (ht t (by simp)) v hd.1,
        ih (fun t hx => ht t (by simp [hx])) hd.2⟩

theorem startSuperArgs_cons (m : Machine) (acc : List Value) (e : Ratchet.Expr)
    (es : List Ratchet.Expr) (hp : plainArgB e = true) :
    Interp.startSuperArgs m acc (toRubyList (e :: es)) none =
      .next (Interp.withKont m (.eval (toRuby e)) (.superArgK acc (toRubyList es) none)) := by
  cases e <;> cases hp <;> rfl

theorem SemInitAllA.startSuperArgs {κ κ' : Ctx} {Γ Γ' Γo : Env} {I I' Io τ : Ty}
    {es : List Ratchet.Expr} {tys : List Ty} (h : SemInitAllA κ Γ I es tys κ' Γ' I')
    {anchor : Heap} {m : Machine} (hm : InitState anchor κ Γ I m) (hk : m.kont = [])
    (seen : List Ty) (acc : List Value) (ht : ∀ σ ∈ seen, IvarStable σ = true)
    (ha : DenAll seen m acc)
    (finish : ∀ n, InitState anchor κ' Γ' I' n → n.kont = [] →
      ∀ vs, DenAll (seen ++ tys) n vs → ∃ next, Interp.doSuper n vs none = .next next ∧
        InitRunSpec anchor n next Γo τ κ' Io) :
    ∃ next, Interp.startSuperArgs m acc (toRubyList es) none = .next next ∧
      InitRunSpec anchor m next Γo τ κ' Io := by
  induction h generalizing m seen acc with
  | nil => exact finish m hm hk acc (by simpa using ha)
  | @cons κ κ₁ κ₂ Γ Γ₁ Γ₂ I I₁ I₂ σ e es tys he hs hp hσ ih =>
    refine ⟨_, startSuperArgs_cons m acc e es hp, ?_⟩
    simp only [Interp.withKont, hk]
    change InitRunSpec anchor m (pushK [.superArgK acc (toRubyList es) none] (evalFrom m e)) Γo τ κ₂ Io
    apply (he anchor m hm).bindSpec hm.typed.rootClean (by intro k h; simp at h; subst h; rfl)
    intro a n hn
    cases a with
    | val v =>
      have hf := hn.1.reCtl (.value v) []
      have hacc : DenAll (seen ++ [σ]) (deliverA (.val v) n []) (acc ++ [v]) :=
        denAll_append (denAll_ivarStable ht hf.stable ha) ⟨denM_deliverA.mpr hn.2.1, trivial⟩
      obtain ⟨next, hd, hr⟩ := ih ((hn.2.2 v rfl).reCtl _ _) rfl (seen ++ [σ]) (acc ++ [v])
        (by intro s hs; rcases List.mem_append.mp hs with hs | hs
            · exact ht s hs
            · simpa only [List.mem_singleton.mp hs] using hσ)
        hacc (by simpa only [List.append_assoc, List.singleton_append] using finish)
      apply InitRunSpec.rebase (hf := hf)
      apply InitRunSpec.step (by rfl) (show Interp.stepFn _ = .next next from ?_) hr
      exact hd
    | esc j =>
      apply InitRunSpec.step (by rfl)
        (show Interp.stepFn _ = .next (deliverA (.esc j) n []) from by cases j <;> rfl)
      exact InitRunSpec.answer ⟨hn.1, hn.2.1, fun _ hv => by cases hv⟩

#print axioms SemInitAllA.startSuperArgs
end Ratchet.Denote.Typed
