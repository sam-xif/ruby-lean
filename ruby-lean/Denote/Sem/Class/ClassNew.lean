import Denote.Sem.Instance.InstanceSite

/-! Constructor dispatch metadata at one heap site. Range/Struct have real prelude new
methods, so this is not a universal class-object query invariant. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore Ratchet

structure NewDispatch (h : Heap) (k : ObjId) : Prop where
  found : ∀ owner md, Interp.methodOn h k "new" = some (owner, md) →
    md.builtin = some "Class#new" ∧ md.undefined = false ∧ md.visibility = .pub ∧
    md.fromPrelude = false ∧
    Interp.crubyShadow h ((ancestors h k).takeWhile (· != owner)) "new" = none
  missing : Interp.methodOn h k "new" = none → ∀ owner md,
    Interp.methodOn h k "method_missing" = some (owner, md) → md.builtin.isSome = true

theorem NewDispatch.transport {h h' : Heap} {k k' : ObjId} (hd : NewDispatch h k)
    (hn : Interp.methodOn h' k' "new" = Interp.methodOn h k "new")
    (hm : Interp.methodOn h' k' "method_missing" = Interp.methodOn h k "method_missing")
    (hs : ∀ owner, Interp.crubyShadow h' ((ancestors h' k').takeWhile (· != owner)) "new" =
      Interp.crubyShadow h ((ancestors h k).takeWhile (· != owner)) "new") : NewDispatch h' k' := by
  refine ⟨?_, ?_⟩
  · intro owner md hl
    obtain ⟨hb, hu, hv, hp, hshadow⟩ := hd.found owner md (hn.symm ▸ hl)
    exact ⟨hb, hu, hv, hp, (hs owner).trans hshadow⟩
  · intro hl owner md hmd
    exact hd.missing (hn.symm ▸ hl) owner md (hm.symm ▸ hmd)

def newDispatchB (h : Heap) (k : ObjId) : Bool :=
  match Interp.methodOn h k "new" with
  | some (owner, md) => md.builtin == some "Class#new" && !md.undefined &&
      md.visibility == .pub && !md.fromPrelude &&
      (Interp.crubyShadow h ((ancestors h k).takeWhile (· != owner)) "new").isNone
  | none => (Interp.methodOn h k "method_missing").all (fun (_, md) => md.builtin.isSome)

theorem newDispatchB_sound {h : Heap} {k : ObjId} (hb : newDispatchB h k = true) :
    NewDispatch h k := by
  refine ⟨?_, ?_⟩
  · intro owner md hl
    simpa [newDispatchB, hl, Bool.and_eq_true, and_assoc] using hb
  · intro hl owner md hm
    simpa [newDispatchB, hl, hm] using hb

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
end Ratchet.Denote
