import Books.TypeSoundness.Conformance.Instance.InstanceSite

/-! Constructor dispatch metadata at one heap site. Range/Struct have real prelude new
methods, so this is not a universal class-object query invariant. Positive lookup is
retained: conditional metadata alone permits default new to gate without allocating. -/
set_option autoImplicit false
namespace Checker.Soundness
open RubyCore Checker

structure NewDispatch (h : Heap) (k : ObjId) : Prop where
  found : ∀ owner md, Interp.methodOn h k "new" = some (owner, md) →
    md.builtin = some "Class#new" ∧ md.undefined = false ∧ md.visibility = .pub ∧
    md.fromPrelude = false ∧
    Interp.crubyShadow h ((ancestors h k).takeWhile (· != owner)) "new" = none
  present : ∃ owner md, Interp.methodOn h k "new" = some (owner, md)

theorem NewDispatch.transport {h h' : Heap} {k k' : ObjId} (hd : NewDispatch h k)
    (hn : Interp.methodOn h' k' "new" = Interp.methodOn h k "new")
    (hs : ∀ owner, Interp.crubyShadow h' ((ancestors h' k').takeWhile (· != owner)) "new" =
      Interp.crubyShadow h ((ancestors h k).takeWhile (· != owner)) "new") : NewDispatch h' k' := by
  refine ⟨?_, ?_⟩
  · intro owner md hl
    obtain ⟨hb, hu, hv, hp, hshadow⟩ := hd.found owner md (hn.symm ▸ hl)
    exact ⟨hb, hu, hv, hp, (hs owner).trans hshadow⟩
  · simpa only [hn] using hd.present

def newDispatchB (h : Heap) (k : ObjId) : Bool :=
  match Interp.methodOn h k "new" with
  | some (owner, md) => md.builtin == some "Class#new" && !md.undefined &&
      md.visibility == .pub && !md.fromPrelude &&
      (Interp.crubyShadow h ((ancestors h k).takeWhile (· != owner)) "new").isNone
  | none => false

theorem newDispatchB_sound {h : Heap} {k : ObjId} (hb : newDispatchB h k = true) :
    NewDispatch h k := by
  refine ⟨?_, ?_⟩
  · intro owner md hl
    simpa [newDispatchB, hl, Bool.and_eq_true, and_assoc] using hb
  · cases hl : Interp.methodOn h k "new" with
    | none => simp [newDispatchB, hl] at hb
    | some hit => exact ⟨hit.1, hit.2, rfl⟩

/-- The interpreter lets a user singleton new override initializer interception. -/
theorem NewDispatch.no_userNew {h : Heap} {k : ObjId}
    (hd : NewDispatch h (classOf h (.ref k))) :
    (match (h.get k).eigen with
     | some e => match Interp.methodOn h e "new" with
       | some (_, md) => md.builtin.isNone && !md.undefined
       | none => false
     | none => false) = false := by
  cases he : (h.get k).eigen with
  | none => rfl
  | some e =>
    cases hm : Interp.methodOn h e "new" with
    | none => simp only [hm]
    | some hit =>
      obtain ⟨owner, md⟩ := hit
      have hb := (hd.found owner md (by simpa only [classOf, he] using hm)).1
      simp only [hm, hb, Option.isNone_some, Bool.false_and]

#print axioms newDispatchB_sound
end Checker.Soundness
