import Ratchet.NativeGuards
import Denote.Sem.ClassNative
import Denote.Sem.DispatchName

/-! Kernel-checked coverage, not trust in copied dispatch metadata. The finite projection
retains every modeled native blocker for its supported queries and explicit call names. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

private theorem query_covered : crubyMethodNames.all (fun p => nativeQueryNames.all
    (fun mn => !p.2.contains mn || nativeQueryHasB p.1 mn)) = true := by decide
private theorem singleton_covered : crubySingletonNames.all
    (fun p => p.2.all singletonSendNames.contains) = true := by decide

theorem nativeQueryFreeB_sound {cn mn : String} (h : nativeQueryFreeB cn mn = true) :
    crubyClassDefines cn mn = false := by
  simp only [nativeQueryFreeB, Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at h
  unfold crubyClassDefines
  cases hf : crubyMethodNames.find? (·.1 == cn) with
  | none => rfl
  | some p =>
    have hp : p.1 = cn := by simpa using List.find?_some hf
    have hc := List.all_eq_true.mp (List.all_eq_true.mp query_covered p
      (List.mem_of_find?_eq_some hf)) mn h.1
    simpa only [hp, h.2, Bool.or_false, Bool.not_eq_true'] using hc

theorem classNativeQuietB_sound {cn mn : String} (h : classNativeQuietB cn mn = true) :
    FreshClass.NativeQuiet cn mn := by
  simp only [classNativeQuietB, Bool.and_eq_true] at h
  exact ⟨nativeQueryFreeB_sound h.1, nativeQueryFreeB_sound h.2⟩

theorem classNativeFrameB_sound {κ : Ctx} {cn : String} (h : classNativeFrameB κ cn = true) :
    FreshClass.NativeFrame κ cn := by
  have quiet (mn : String) (hm : mn ∈ ["is_a?", "class", "raise", "===", "to_s", "nil?"])
      (hf : nameFreeN κ mn = true) : FreshClass.NativeQuiet cn mn := by
    have ht := List.all_eq_true.mp h mn hm
    exact classNativeQuietB_sound (by simpa only [hf, Bool.not_true, Bool.false_or] using ht)
  refine ⟨?_, ?_, fun hf => quiet "nil?" (by simp) hf⟩
  · intro mn bid hm hf
    have hm : mn ∈ queryBuiltins.map (·.1) := List.mem_map.mpr ⟨(mn, bid), hm, rfl⟩
    apply quiet mn _ hf
    simp only [queryBuiltins, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp
  · intro mn bid hm hf
    have hm : mn ∈ clsQueryBuiltins.map (·.1) := List.mem_map.mpr ⟨(mn, bid), hm, rfl⟩
    apply quiet mn _ hf
    simp only [clsQueryBuiltins, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp

theorem directCallNameB_sound {mn : String} (h : directCallNameB mn = true) : DirectSendName mn := by
  simp only [directCallNameB, Bool.and_eq_true, Bool.not_eq_true'] at h
  refine ⟨by simpa [interceptedSendNames, payloadSendNames] using h.1, ?_⟩
  intro cn
  unfold crubySingletonDefines
  cases hf : crubySingletonNames.find? (·.1 == cn) with
  | none => rfl
  | some p =>
    have hc := List.all_eq_true.mp singleton_covered p (List.mem_of_find?_eq_some hf)
    cases hm : p.2.contains mn with
    | false => exact hm
    | true =>
      have hn := List.all_eq_true.mp hc mn (List.contains_iff_mem.mp hm)
      rw [h.2] at hn
      cases hn

theorem classNativeFrameB_to_semB {κ : Ctx} {cn : String} (h : classNativeFrameB κ cn = true) :
    FreshClass.nativeFrameB κ cn = true := by
  have hf := classNativeFrameB_sound h
  have rows (rs : List (String × String))
      (hr : ∀ mn bid, (mn, bid) ∈ rs → nameFreeN κ mn = true → FreshClass.NativeQuiet cn mn) :
      FreshClass.nativeRowsB κ cn rs = true := by
    apply List.all_eq_true.mpr
    intro p hp
    cases he : nameFreeN κ p.1 with
    | false => simp [he]
    | true =>
      have hq := hr p.1 p.2 hp he
      simp [he, FreshClass.nativeQuietB, hq.1, hq.2]
  simp only [FreshClass.nativeFrameB, Bool.and_eq_true]
  refine ⟨⟨rows _ hf.query, rows _ hf.clsQuery⟩, rows _ ?_⟩
  intro mn bid hm hn
  have hm : mn = "nil?" ∧ bid = "" := by simpa using hm
  rcases hm with ⟨rfl, _⟩
  exact hf.nilQuery hn

#print axioms nativeQueryFreeB_sound
#print axioms classNativeFrameB_sound
#print axioms directCallNameB_sound
#print axioms classNativeFrameB_to_semB
end Ratchet.Denote
