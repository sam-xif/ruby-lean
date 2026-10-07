import Books.TypeSoundness.Conformance.Singleton.SingletonCode
import Books.TypeSoundness.Conformance.Core.Trans
import Books.TypeSoundness.Conformance.Instance.InstanceSite

/-! Positive singleton code records. A cached owner and exact code, not an annotation,
justify a row. The owner's absent eigenclass separates it from ordinary class owners. -/
set_option autoImplicit false
namespace Checker.Soundness
open RubyCore Checker

def ownCode (h : Heap) (owner : ObjId) (name : String) : Option MethodDef :=
  (h.classPayload? owner).bind (fun cp => (cp.methods.find? (·.1 == name)).map (·.2))

def SingletonRows (ds : List Defn) (k : ObjId) (h : Heap) : Prop :=
  ∀ d ∈ ds, ∃ e md, (h.get k).eigen = some e ∧ (h.get e).eigen = none ∧
    ownCode h e d.name = some md ∧ md.params = toRubyParams d.params ∧
    md.body = toRuby d.body ∧ md.undefined = false ∧ SingletonMethodCode k e md

theorem ownCode_live {h : Heap} {e : ObjId} {name : String} {md : MethodDef}
    (hc : ownCode h e name = some md) : e < h.objs.size := by
  apply lt_size_of_classPayload
  cases hp : h.classPayload? e with
  | none => simp [ownCode, hp] at hc
  | some cp => rfl

theorem SingletonRows.transport {ds : List Defn} {k : ObjId} {h h' : Heap}
    (hp : SingletonRows ds k h) (hk : k < h.objs.size)
    (he : ∀ o, o < h.objs.size → (h'.get o).eigen = (h.get o).eigen)
    (hc : ∀ e name, ownCode h' e name = ownCode h e name) : SingletonRows ds k h' := by
  intro d hd
  obtain ⟨e, md, hke, hleaf, hcode, hrest⟩ := hp d hd
  exact ⟨e, md, (he k hk).trans hke, (he e (ownCode_live hcode)).trans hleaf,
    (hc e d.name).trans hcode, hrest⟩

end Checker.Soundness
