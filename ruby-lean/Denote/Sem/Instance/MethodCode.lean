import RubyCore.Heap

/-! Runtime metadata for ordinary annotation-checked bodies. The lexical owner/scope is
explicit; top-level methods and methods of a top-level class instantiate it differently. -/
set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

structure OrdinaryMethodCode (expectedOwner : ObjId) (cref : List ObjId) (md : MethodDef) : Prop where
  owner : md.owner = expectedOwner
  cref : md.cref = cref
  superName : md.superName = none
  builtin : md.builtin = none
  captured : md.capturedFrame = none
  declared : md.declared = []
  fromPrelude : md.fromPrelude = false
  visibilityOnly : md.visibilityOnly = false
  fromBlock : md.fromBlock = false
  forTargets : md.forTargets = none
  definee : md.definee.getD md.owner = expectedOwner
  /-- Ordinary `def` bodies use their own frame as definition context. -/
  definitionFrame : md.definitionFrame = none
  /-- Ordinary `def` bodies resolve `super` from the receiver's class. -/
  superScope : md.superScope = none

abbrev TopMethodCode (md : MethodDef) : Prop :=
  OrdinaryMethodCode Boot.objectId [] md

/-- Current ordinary-class fragment: lexical top-level class scope, public methods except
private initialize. Nested lexical scopes and visibility changes need distinct contracts. -/
structure InstanceMethodCode (owner : ObjId) (name : String) (md : MethodDef) : Prop
    extends OrdinaryMethodCode owner [owner] md where
  visibility : md.visibility = if name == "initialize" then .priv else .pub

def ordinaryMethodCodeB (owner : ObjId) (cref : List ObjId) (md : MethodDef) : Bool :=
  decide (md.owner = owner ∧ md.cref = cref ∧ md.superName = none ∧ md.builtin = none ∧
    md.capturedFrame = none ∧ md.declared = [] ∧ md.fromPrelude = false ∧ md.visibilityOnly = false ∧
    md.fromBlock = false ∧ md.forTargets = none ∧ md.definee.getD md.owner = owner ∧
    md.definitionFrame = none ∧ md.superScope = none)

theorem ordinaryMethodCodeB_sound {owner : ObjId} {cref : List ObjId} {md : MethodDef}
    (hb : ordinaryMethodCodeB owner cref md = true) : OrdinaryMethodCode owner cref md := by
  simp only [ordinaryMethodCodeB, decide_eq_true_eq] at hb
  rcases hb with ⟨ho, hc, hs, hb, hcap, hd, hp, hv, hblock, hfor, hdefinee, hdf, hss⟩
  exact ⟨ho, hc, hs, hb, hcap, hd, hp, hv, hblock, hfor, hdefinee, hdf, hss⟩

def instanceMethodCodeB (owner : ObjId) (name : String) (md : MethodDef) : Bool :=
  ordinaryMethodCodeB owner [owner] md &&
    decide (md.visibility = if name == "initialize" then .priv else .pub)

theorem instanceMethodCodeB_sound {owner : ObjId} {name : String} {md : MethodDef}
    (hb : instanceMethodCodeB owner name md = true) : InstanceMethodCode owner name md := by
  simp only [instanceMethodCodeB, Bool.and_eq_true, decide_eq_true_eq] at hb
  exact ⟨ordinaryMethodCodeB_sound hb.1, hb.2⟩

#print axioms instanceMethodCodeB_sound
end Ratchet.Denote
