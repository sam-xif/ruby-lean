import Denote.Typed.Array

/-! Hash pairs evaluate key, value, then the next pair; duplicate keys keep their first
position and their last value. First-order framing retains evaluated keys and values. -/
set_option autoImplicit false
set_option maxRecDepth 4000
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

inductive SemPairsA : Env → List (Ratchet.Expr × Ratchet.Expr) → List Ty → List Ty → Env → Prop
  | nil {Γ : Env} : SemPairsA Γ [] [] [] Γ
  | cons {Γ Γk Γv Γ' : Env} {k v : Ratchet.Expr} {ps : List (Ratchet.Expr × Ratchet.Expr)}
      {σ τ : Ty} {ks vs : List Ty} :
      SemSafeA Γ k σ Γk → SemSafeA Γk v τ Γv → SemPairsA Γv ps ks vs Γ' →
      SemPairsA Γ ((k, v) :: ps) (σ :: ks) (τ :: vs) Γ'

private def hashNext (m : Machine) (acc : List (Value × Value))
    (ps : List (RubyCore.Expr × RubyCore.Expr)) : StepResult :=
  match ps with
  | [] =>
    let (v, m) := Builtins.allocHsh m acc.toArray
    .next (Interp.withCtl m (.value v))
  | (k, v) :: rest => .next (Interp.withKont m (.eval k) (.hshKeyK acc v rest))

private def hashPut (h : Heap) (acc : List (Value × Value)) (k v : Value) :=
  match acc.findIdx? (fun p => valueEql h p.1 k) with
  | some i => acc.set i (acc[i]!.1, v)
  | none => acc ++ [(k, v)]

private def PairsDen (m : Machine) (σ τ : Ty) (acc : List (Value × Value)) : Prop :=
  ∀ p ∈ acc, denM σ m p.1 ∧ denM τ m p.2

private theorem PairsDen.framed {m n : Machine} {σ τ : Ty} {acc : List (Value × Value)}
    (hd : PairsDen m σ τ acc) (hf : Framed m n)
    (hk : FirstOrder σ = true) (hv : FirstOrder τ = true) : PairsDen n σ τ acc := by
  intro p hp
  exact ⟨hf.firstOrder σ hk _ (hd p hp).1, hf.firstOrder τ hv _ (hd p hp).2⟩

private theorem hashPut_den {m : Machine} {σ τ : Ty} {acc : List (Value × Value)}
    {k v : Value} (ha : PairsDen m σ τ acc) (hk : denM σ m k) (hv : denM τ m v) :
    PairsDen m σ τ (hashPut m.heap acc k v) := by
  unfold hashPut
  split
  next i hi =>
    have hlt := (List.findIdx?_eq_some_iff_findIdx_eq.mp hi).1
    have hmem : acc[i]! ∈ acc := by
      simpa only [getElem!_pos acc i hlt] using List.getElem_mem hlt
    intro p hp
    rcases List.mem_or_eq_of_mem_set hp with hp | hp
    · exact ha p hp
    · subst p; exact ⟨(ha _ hmem).1, hv⟩
  next =>
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact ha p hp
    · have hp := List.mem_singleton.mp hp
      subst p; exact ⟨hk, hv⟩

private theorem hash_alloc {Γ : Env} {m : Machine} {σ τ : Ty}
    (hm : StateOk ctx0 Γ .ivar0 m) (hk : m.kont = [])
    (acc : List (Value × Value)) (hd : PairsDen m σ τ acc) :
    StepSpec m Γ (.hashOf σ τ) (hashNext m acc []) := by
  let obj : Object := { klass := Boot.hashId, payload := .hsh acc.toArray }
  let n : Machine := { m with heap := pushHeap m.heap obj }
  have he : Ext m n := ext_push obj hm.sat hm.core.basicSelf
    (fun c => by simp [obj]) rfl rfl hm.core.hashBasic
  have hn : StateOk ctx0 Γ .ivar0 n := StateOk_ext hm he
    (stringPayloadOk_push hm.stringPayload (by simp [obj, Boot.hashId, Boot.stringId]))
  have hv : denM (.hashOf σ τ) n (.ref m.heap.objs.size) := by
    rw [denM]
    refine ⟨acc.toArray, ?_, ?_⟩
    · simp [hshEntries?, n, pushHeap_get_self, obj]
    · intro p hp
      have hp := hd p (by simpa using hp)
      exact ⟨denM_ext he hp.1, denM_ext he hp.2⟩
  have h := RunSpec.answer (a := .val (.ref m.heap.objs.size))
    (show ResultOk m Γ (.hashOf σ τ) _ n from
      ⟨Framed.of_ext he, hv, fun _ hv => by cases hv; exact hn⟩)
  simpa only [StepSpec, hashNext, Builtins.allocHsh, Heap.alloc,
    n, obj, pushHeap, Interp.withCtl, deliverA, Answer.ctl, hk] using h

private theorem hash_spec {Γ Γ' : Env} {ps : List (Ratchet.Expr × Ratchet.Expr)}
    {ks vs : List Ty} (hs : SemPairsA Γ ps ks vs Γ') {σ τ : Ty}
    (hfk : FirstOrder σ = true) (hfv : FirstOrder τ = true)
    (htk : ∀ α ∈ ks, ∀ m v, denM α m v → denM σ m v)
    (htv : ∀ α ∈ vs, ∀ m v, denM α m v → denM τ m v)
    {m : Machine} (hm : StateOk ctx0 Γ .ivar0 m) (hk : m.kont = [])
    (acc : List (Value × Value)) (ha : PairsDen m σ τ acc) :
    StepSpec m Γ' (.hashOf σ τ) (hashNext m acc (toRubyPairs ps)) := by
  induction hs generalizing m acc with
  | nil => exact hash_alloc hm hk acc ha
  | @cons Γ Γk Γv Γ' k v ps α β ks vs hkey hval hs ih =>
    simp only [toRubyPairs, hashNext, StepSpec, Interp.withKont, hk]
    change RunSpec m (pushK [.hshKeyK acc (toRuby v) (toRubyPairs ps)] (evalFrom m k))
      Γ' (.hashOf σ τ)
    apply RunSpec.bind hkey hm (by
      intro k h tag; simp only [List.mem_singleton] at h; subst h; simp)
    intro ak n hn
    cases ak with
    | esc j =>
      apply RunSpec.step (by rfl)
        (show Interp.stepFn _ = .next (deliverA (.esc j) n []) from by cases j <;> rfl)
      exact RunSpec.answer ⟨hn.1, hn.2.1, fun _ hv => by cases hv⟩
    | val key =>
      have hkey : denM σ n key := htk α (by simp) n key hn.2.1
      have hacc := ha.framed hn.1 hfk hfv
      apply RunSpec.step (by rfl)
        (show Interp.stepFn _ =
          .next (pushK [.hshValK acc key (toRubyPairs ps)] (evalFrom n v)) from rfl)
      apply RunSpec.rebase ?_ hn.1
      apply RunSpec.bind hval (hn.2.2 key rfl) (by
        intro k h tag; simp only [List.mem_singleton] at h; subst h; simp)
      intro av o ho
      cases av with
      | esc j =>
        apply RunSpec.step (by rfl)
          (show Interp.stepFn _ = .next (deliverA (.esc j) o []) from by cases j <;> rfl)
        exact RunSpec.answer ⟨ho.1, ho.2.1, fun _ hv => by cases hv⟩
      | val val =>
        have hacc := hashPut_den (hacc.framed ho.1 hfk hfv)
          (ho.1.firstOrder σ hfk key hkey) (htv β (by simp) o val ho.2.1)
        have hnext := ih (m := deliverA (.val val) o []) (fun α hα => htk α (by simp [hα]))
          (fun α hα => htv α (by simp [hα])) (StateOk_deliverA (ho.2.2 val rfl)) rfl
          (hashPut o.heap acc key val) (hacc.framed (Framed_reCtl _ _ _) hfk hfv)
        have h : RunSpec (deliverA (.val val) o [])
            (deliverA (.val val) o [.hshValK acc key (toRubyPairs ps)]) Γ' (.hashOf σ τ) := by
          apply RunSpec.of_stepSpec (by rfl)
          exact hnext
        exact h.rebase (ho.1.trans (Framed_reCtl _ _ _))

theorem SemA.hashLit {Γ Γ' : Env} {ps : List (Ratchet.Expr × Ratchet.Expr)} {ks vs : List Ty}
    (hs : SemPairsA Γ ps ks vs Γ') (hk : FirstOrder (elemTy ks) = true)
    (hv : FirstOrder (elemTy vs) = true) :
    SemSafeA Γ (.hash ps) (.hashOf (elemTy ks) (elemTy vs)) Γ' := by
  apply semSafe_of_runSpec
  intro m hm
  apply RunSpec.rebase (middle := evalFrom m (.hash ps)) ?_ (Framed_reCtl _ _ [])
  apply RunSpec.of_stepSpec (by rfl)
  have h := hash_spec (m := evalFrom m (.hash ps)) hs hk hv (fun _ ht _ _ hd => denM_elemTy ht hd)
    (fun _ ht _ _ hd => denM_elemTy ht hd) (StateOk_reCtl hm _ []) rfl [] (by simp [PairsDen])
  exact h

theorem SemA.DJudgePairs.nil {Γ : Env} : SemPairsA Γ [] [] [] Γ := .nil

theorem SemA.DJudgePairs.cons {Γ Γk Γv Γ' : Env} {k v : Ratchet.Expr}
    {ps : List (Ratchet.Expr × Ratchet.Expr)} {σ τ : Ty} {ks vs : List Ty}
    (hk : SemSafeA Γ k σ Γk) (hv : SemSafeA Γk v τ Γv) (hs : SemPairsA Γv ps ks vs Γ') :
    SemPairsA Γ ((k, v) :: ps) (σ :: ks) (τ :: vs) Γ' := .cons hk hv hs

#print axioms SemA.hashLit

-- Runtime pin: duplicate keys keep the first position and the last value.
#guard match Interp.run 100 (evalFrom bootMachine
    (.hash [(.sym "a", .int 1), (.sym "b", .int 2), (.sym "a", .int 3)])) with
  | .value v m => match hshEntries? m.heap v with
    | some #[(.sym "a", .int 3), (.sym "b", .int 2)] => true
    | _ => false
  | _ => false

end Ratchet.Denote.Typed
