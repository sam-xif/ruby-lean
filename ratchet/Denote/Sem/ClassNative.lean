import Denote.Sem.ClassQueries

/-! Executable native-shadow guard for a fresh class and its eigenclass. Only names whose
negative facts the context still exposes need this guard. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet

def nativeQuietB (name mn : String) : Bool :=
  !crubyClassDefines name mn && !crubyClassDefines ("#<Class:" ++ name ++ ">") mn

def nativeRowsB (κ : Ctx) (name : String) (rows : List (String × String)) : Bool :=
  rows.all fun (mn, _) => !nameFreeN κ mn || nativeQuietB name mn

theorem nativeRowsB_sound {κ : Ctx} {name mn bid : String} {rows : List (String × String)}
    (hb : nativeRowsB κ name rows = true) (hm : (mn, bid) ∈ rows)
    (hf : nameFreeN κ mn = true) : NativeQuiet name mn := by
  have ht := List.all_eq_true.mp hb (mn, bid) hm
  simpa [hf, nativeQuietB, NativeQuiet] using ht

structure NativeFrame (κ : Ctx) (name : String) : Prop where
  query : ∀ mn bid, (mn, bid) ∈ queryBuiltins → nameFreeN κ mn = true → NativeQuiet name mn
  clsQuery : ∀ mn bid, (mn, bid) ∈ clsQueryBuiltins → nameFreeN κ mn = true → NativeQuiet name mn
  nilQuery : nameFreeN κ "nil?" = true → NativeQuiet name "nil?"

def nativeFrameB (κ : Ctx) (name : String) : Bool :=
  nativeRowsB κ name queryBuiltins && nativeRowsB κ name clsQueryBuiltins &&
    nativeRowsB κ name [("nil?", "")]

theorem nativeFrameB_sound {κ : Ctx} {name : String} (hb : nativeFrameB κ name = true) :
    NativeFrame κ name := by
  simp only [nativeFrameB, Bool.and_eq_true] at hb
  obtain ⟨⟨hq, hc⟩, hn⟩ := hb
  exact ⟨fun _ _ hm hf => nativeRowsB_sound hq hm hf,
    fun _ _ hm hf => nativeRowsB_sound hc hm hf,
    fun hf => nativeRowsB_sound hn (List.mem_singleton_self _) hf⟩

#print axioms nativeFrameB_sound
end Ratchet.Denote.FreshClass
