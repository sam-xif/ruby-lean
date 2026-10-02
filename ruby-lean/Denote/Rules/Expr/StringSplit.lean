import Denote.Rules.Expr.ArrayCompact
import Denote.Rules.Primitive.PrimitiveAlloc

/-! `String#split` at a String separator: whatever the regex engine answers, the result
is a fresh Array of fresh Strings (or an unsupported gate). -/
set_option autoImplicit false
set_option maxRecDepth 4000
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

/-- One fresh String: conformance, frame and kont are retained. -/
theorem allocStr_ok {κ : Ctx} {I : Ty} {Γ : Env} {m : Machine} (hm : StateOk κ Γ I m)
    (s : String) (bin : Bool) :
    StateOk κ Γ I (Builtins.allocStrEnc m s bin).2 ∧ Framed m (Builtins.allocStrEnc m s bin).2 ∧
      (Builtins.allocStrEnc m s bin).2.kont = m.kont ∧
      denM (.cls "String") (Builtins.allocStrEnc m s bin).2 (Builtins.allocStrEnc m s bin).1 := by
  have he := ext_push (m := m) (strObj s bin) hm.sat hm.core.basicSelf
    (fun c => by simp [strObj]) rfl rfl (by simpa [strObj] using hm.core.stringBasic)
  obtain ⟨hn, hd⟩ := strLit_alloc_ok (Γ := Γ) (m := m) (s := s) m.kont hm bin
  refine ⟨?_, ?_, rfl, ?_⟩
  · simpa only [Builtins.allocStrEnc, Heap.alloc, pushHeap, strObj, reCtl] using
      StateOk_reCtl hn m.ctl m.kont
  · simpa only [Builtins.allocStrEnc, Heap.alloc, pushHeap, strObj] using Framed.of_ext he
  · have hd' := denM_reCtl.mp hd
    simpa only [Builtins.allocStrEnc, Heap.alloc, pushHeap, strObj] using hd'

theorem allocStrs_ok {κ : Ctx} {I : Ty} {Γ : Env} (bin : Bool)
    (f : Array Value × Machine → String → Array Value × Machine)
    (hf : ∀ p s, f p s = (p.1.push (Builtins.allocStrEnc p.2 s bin).1,
      (Builtins.allocStrEnc p.2 s bin).2)) :
    ∀ (l : List String) (acc : Array Value) (m : Machine), StateOk κ Γ I m →
      (∀ v ∈ acc, denM (.cls "String") m v) →
      StateOk κ Γ I (l.foldl f (acc, m)).2 ∧ Framed m (l.foldl f (acc, m)).2 ∧
        (l.foldl f (acc, m)).2.kont = m.kont ∧
        ∀ v ∈ (l.foldl f (acc, m)).1, denM (.cls "String") (l.foldl f (acc, m)).2 v := by
  intro l
  induction l with
  | nil => intro acc m hm ha; exact ⟨hm, .refl m, rfl, ha⟩
  | cons s l ih =>
    intro acc m hm ha
    obtain ⟨hn, hfr, hk, hd⟩ := allocStr_ok hm s bin
    simp only [List.foldl_cons, hf]
    obtain ⟨h1, h2, h3, h4⟩ := ih _ _ hn (by
      intro v hv
      rcases Array.mem_push.mp hv with hv | rfl
      · exact hfr.firstOrder _ rfl v (ha v hv)
      · exact hd)
    exact ⟨h1, hfr.trans h2, h3.trans hk, h4⟩

theorem splitBy_step {κ : Ctx} {I : Ty} {Γ : Env} {m : Machine} (hm : StateOk κ Γ I m)
    (hk : m.kont = []) (s src : String) (opts : Nat) (lim : Int) (bin : Bool) :
    StepSpec m Γ (.arrayOf (.cls "String"))
      (builtinStep (Builtins.runRegex.splitBy m s src opts lim bin)) κ I := by
  unfold Builtins.runRegex.splitBy
  split
  · exact stepSpec_allocArr hm hk #[] (by simp)
  · split
    · trivial
    · simp only []
      split
      all_goals
        apply StepSpec.rebase (stepSpec_allocArr ?_ ?_ _ ?_) ?_
        · exact (allocStrs_ok bin _ (fun _ _ => rfl) _ #[] m hm (by simp)).1
        · exact (allocStrs_ok (κ := κ) (Γ := Γ) (I := I) bin _ (fun _ _ => rfl) _ #[] m hm
            (by simp)).2.2.1.trans hk
        · exact (allocStrs_ok bin _ (fun _ _ => rfl) _ #[] m hm (by simp)).2.2.2
        · exact (allocStrs_ok (κ := κ) (Γ := Γ) (I := I) bin _ (fun _ _ => rfl) _ #[] m hm
            (by simp)).2.1

theorem string_split_run {κ : Ctx} {I : Ty} {Γ : Env} {m : Machine} {o p : ObjId} {s t : String}
    (hm : StateOk κ Γ I m) (hk : m.kont = [])
    (hs : (m.heap.get o).payload = .str s) (ht : (m.heap.get p).payload = .str t) :
    StepSpec m Γ (.arrayOf (.cls "String"))
      (builtinStep (Builtins.run "String#split" (.ref o) [.ref p] m)) κ I := by
  simp only [Builtins.run]
  repeat' split
  all_goals first | trivial | skip
  all_goals
    change StepSpec m Γ _
      (builtinStep (Builtins.runRegex "String#split" (.ref o) [.ref p] m)) κ I
    rw [Builtins.runRegex.eq_def]
    simp only [Builtins.strPayload?, hs, ht, Builtins.regexpParts?, Option.isSome_none,
      Bool.false_eq_true, ↓reduceIte, Builtins.runRegex.splitOn]
    split
    · exact splitBy_step hm hk _ _ _ _ _
    · split
      · exact splitBy_step hm hk _ _ _ _ _
      · exact splitBy_step hm hk _ _ _ _ _

#print axioms allocStrs_ok
#print axioms string_split_run
end Ratchet.Denote.Typed
