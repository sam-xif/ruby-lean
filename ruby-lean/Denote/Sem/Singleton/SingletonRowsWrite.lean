import Denote.Sem.Instance.MethodInstall

/-! Ordinary class owners have cached metaclasses; singleton owners have none. Thus an
ordinary write preserves even a same-named singleton row, without comparing source names. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

theorem SingletonRows.methodWrite {ds : List Defn} {k cls : ObjId} {h : Heap}
    {name : String} {md : MethodDef} (hp : SingletonRows ds k h)
    (hs : (h.get k).eigen = some cls → ∀ d ∈ ds, d.name ≠ name) :
    SingletonRows ds k (defineMethod h cls name md) := by
  intro d hd
  obtain ⟨e, prev, hke, hleaf, hcode, hrest⟩ := hp d hd
  refine ⟨e, prev, (Proof.get_defineMethod_eigen ..).trans hke,
    (Proof.get_defineMethod_eigen ..).trans hleaf, ?_, hrest⟩
  by_cases he : e = cls
  · subst e
    exact (ownMethod_defineMethod_ne h cls cls name d.name md (hs hke d hd)).trans hcode
  · simpa only [ownCode, Heap.classPayload?, heap_get_defineMethod_ne he] using hcode

theorem SingletonRows.ordinaryWrite {ds : List Defn} {k cls : ObjId} {h : Heap}
    {name : String} {md : MethodDef} (hp : SingletonRows ds k h)
    (hw : (h.get cls).eigen.isSome = true) : SingletonRows ds k (defineMethod h cls name md) := by
  intro d hd
  obtain ⟨e, prev, hke, hleaf, hcode, hrest⟩ := hp d hd
  have hne : e ≠ cls := by
    intro he; subst cls; rw [hleaf] at hw; cases hw
  exact ⟨e, prev, (Proof.get_defineMethod_eigen ..).trans hke,
    (Proof.get_defineMethod_eigen ..).trans hleaf,
    by simpa only [ownCode, Heap.classPayload?, heap_get_defineMethod_ne hne] using hcode,
    hrest⟩

end Ratchet.Denote
