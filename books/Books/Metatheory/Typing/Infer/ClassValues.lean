import Books.Metatheory.Typing.Infer.Decls
import Books.Metatheory.Heap.ClassCongr

/-!
# Value and resolution reads across a class allocation (J43 / W2c, second half)

`ClassCongr.lean` pinned the object-model walks at old ids; this file lifts that to
the judgment's vocabulary: `valueTy?`/`ValueTy` (the bounds are *internal* —
`plainRecv`/`classRecv` refuse an out-of-bounds id, so an old value's type
mentions only old ids), and the `lookup`/`lookupIn`/`crubyShadow` reads the
resolution facts run on.
-/

namespace RubyCore
namespace Proof

open Interp Static RubyCore.Types

namespace ClsGrow

variable {h h' : Heap}

theorem plainRecv_old (hg : ClsGrow h h') (hch : ChainsIn h) (hn : NamesOk h) {o : ObjId}
    (ho : o < h.objs.size) : plainRecv h' o = plainRecv h o := by
  have h1 : decide (o < h'.objs.size) = true := by
    simp [Nat.lt_of_lt_of_le ho hg.size]
  have h2 : decide (o < h.objs.size) = true := by simp [ho]
  unfold plainRecv
  rw [hg.get o ho, hg.payloadOld (hch.klass o ho), h1, h2,
    className_old hg hn (hch.klass o ho)]

theorem classRecv_old (hg : ClsGrow h h') (hch : ChainsIn h) {o : ObjId}
    (ho : o < h.objs.size) : classRecv h' o = classRecv h o := by
  have h1 : decide (o < h'.objs.size) = true := by
    simp [Nat.lt_of_lt_of_le ho hg.size]
  have h2 : decide (o < h.objs.size) = true := by simp [ho]
  unfold classRecv
  rw [hg.payloadOld ho, h1, h2]

/-- `valueTy?` is pinned wherever it *answers*: a `.ref`'s arms bound their id
    themselves. -/
theorem valueTy?_old (hg : ClsGrow h h') (hch : ChainsIn h) (hn : NamesOk h) {v : Value} {σ : Ty}
    (hv : valueTy? h v = some σ) : valueTy? h' v = some σ := by
  cases v with
  | ref o =>
    by_cases ho : o < h.objs.size
    · unfold valueTy? at hv ⊢
      dsimp only at hv ⊢
      rw [plainRecv_old hg hch hn ho, classRecv_old hg hch ho]
      by_cases hp : plainRecv h o = true
      · rw [hp] at hv ⊢
        simp only [if_true] at hv ⊢
        rw [classOf_old hg hch ho,
          className_old hg hn (classOf_lt hch ho)]
        exact hv
      · rw [Bool.not_eq_true] at hp
        rw [hp] at hv ⊢
        simp only [Bool.false_eq_true, if_false] at hv ⊢
        by_cases hc : classRecv h o = true
        · rw [hc] at hv ⊢
          simp only [if_true] at hv ⊢
          rw [className_old hg hn ho]
          exact hv
        · rw [Bool.not_eq_true] at hc
          rw [hc] at hv
          simp at hv
    · exfalso
      unfold valueTy? plainRecv classRecv at hv
      simp only [decide_eq_true_eq] at hv
      rw [if_neg (by simp [ho]), if_neg (by simp [ho])] at hv
      simp at hv
  | _ => exact hv

theorem valueTy_old (hg : ClsGrow h h') (hch : ChainsIn h) (hn : NamesOk h) {v : Value} {τ : Ty}
    (hv : ValueTy h v τ) : ValueTy h' v τ := by
  rcases hv with hany | ⟨σ, o, xs, hsub, rfl, ho, hva, hpay, helems⟩ | ⟨σ, hvt, hsub⟩
  · exact Or.inl hany
  · refine Or.inr (Or.inl ⟨σ, o, xs, hsub, rfl, Nat.lt_of_lt_of_le ho hg.size,
      valueTy?_old hg hch hn hva, by rw [hg.get o ho]; exact hpay, ?_⟩)
    intro v' hv'
    obtain ⟨σ', hv'e, hsub'⟩ := helems v' hv'
    exact ⟨σ', valueTy?_old hg hch hn hv'e, hsub'⟩
  · exact Or.inr (Or.inr ⟨σ, valueTy?_old hg hch hn hvt, hsub⟩)

/-- Bounded dispatch over old ids, including the Object fallback. -/
theorem lookup_go_old (hg : ClsGrow h h') (hch : ChainsIn h) (hsat : Saturated h)
    {mname : String} (chain : List ObjId)
    (hmem : ∀ j ∈ chain, j < h.objs.size)
    (hlen : chain.length ≤ h.objs.size + 1) :
    lookupInChain h' chain mname = lookupInChain h chain mname := by
  apply lookupInChain_grow_congr hg.size (ancestors_old hg hch hsat hch.boot.2.2.2.2)
  · have ho := ancestors_length_bound hch Boot.objectId
    omega
  · intro k hk
    apply hg.payloadOld
    rcases List.mem_append.mp hk with hk | hk
    · exact hmem k hk
    · exact ancestors_mem_lt hch hch.boot.2.2.2.2 k hk

/-- Dispatch from an old value is pinned. -/
theorem lookup_old (hg : ClsGrow h h') (hch : ChainsIn h) (hsat : Saturated h)
    {o : ObjId} (ho : o < h.objs.size) (mname : String) :
    lookup h' (.ref o) mname = lookup h (.ref o) mname := by
  unfold lookup
  rw [classOf_old hg hch ho, ancestors_old hg hch hsat (classOf_lt hch ho)]
  exact lookup_go_old hg hch hsat _ (ancestors_mem_lt hch (classOf_lt hch ho))
    (ancestors_length_bound hch _)

theorem lookupIn_old (hg : ClsGrow h h') (hch : ChainsIn h) (hsat : Saturated h)
    {k : ObjId} (hk : k < h.objs.size) (mname : String) :
    lookupIn h' k mname = lookupIn h k mname := by
  unfold lookupIn
  rw [ancestors_old hg hch hsat hk]
  exact lookup_go_old hg hch hsat _ (ancestors_mem_lt hch hk)
    (ancestors_length_bound hch _)

theorem crubyShadow_old (hg : ClsGrow h h') (hn : NamesOk h) {mname : String} :
    ∀ chain : List ObjId, (∀ j ∈ chain, j < h.objs.size) →
      crubyShadow h' chain mname = crubyShadow h chain mname := by
  have hlib (k : ObjId) (hk : k < h.objs.size) :
      libraryNamespace h' k = libraryNamespace h k := by
    simp only [libraryNamespace, hg.payloadOld hk]
  have hnativ (k : ObjId) (hk : k < h.objs.size) :
      nativeSingletonMethod h' k mname = nativeSingletonMethod h k mname ∧
      featureMethod h' k mname = featureMethod h k mname := by
    simp only [nativeSingletonMethod, featureMethod, hg.payloadOld hk, hlib k hk]
    cases hc : h.classPayload? k with
    | none => simp [featureHas, hlib k hk]
    | some cp =>
      cases ha : cp.attached with
      | none => simp [ha, featureHas, hlib k hk]
      | some target =>
        have ht := (hn.attached k cp target hc ha).1
        simp [featureHas, ha, className_old hg hn ht, hlib target ht, hlib k hk]
  intro chain
  induction chain with
  | nil => intro _; rfl
  | cons a rest ih =>
    intro hmem
    unfold crubyShadow at *
    simp only [List.firstM, className_old hg hn (hmem a (by simp)),
      (hnativ a (hmem a (by simp))).1, (hnativ a (hmem a (by simp))).2]
    split <;> first | rfl | exact ih (fun j hj => hmem j (List.mem_cons_of_mem _ hj))

theorem constOwn_old (hg : ClsGrow h h') {k : ObjId} (hk : k < h.objs.size)
    (n : String) : constOwn h' k n = constOwn h k n := by
  unfold constOwn
  rw [hg.payloadOld hk]

theorem constLookupFrom_old (hg : ClsGrow h h') (hch : ChainsIn h)
    (hsat : Saturated h) {k : ObjId} (hk : k < h.objs.size) (n : String) :
    constLookupFrom h' k n = constLookupFrom h k n := by
  unfold constLookupFrom
  rw [ancestors_old hg hch hsat hk]
  have hmem := ancestors_mem_lt hch hk
  revert hmem
  generalize ancestors h k = chain
  intro hmem
  induction chain with
  | nil => rfl
  | cons a rest ih =>
    have hpa := hg.payloadOld (hmem a (by simp))
    have ihr := ih (fun j hj => hmem j (List.mem_cons_of_mem _ hj))
    cases h1 : h'.classPayload? a with
    | none =>
      cases h2 : h.classPayload? a with
      | none => simp [List.firstM, h1, h2, ihr]
      | some c => rw [h1, h2] at hpa; exact absurd hpa (by simp)
    | some c' =>
      cases h2 : h.classPayload? a with
      | none => rw [h1, h2] at hpa; exact absurd hpa (by simp)
      | some c =>
        rw [h1, h2] at hpa
        simp only [Option.some.injEq] at hpa
        subst hpa
        simp [List.firstM, h1, h2, ihr]

end ClsGrow

end Proof
end RubyCore
