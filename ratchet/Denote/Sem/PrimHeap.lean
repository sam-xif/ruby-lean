import Denote.Grow

/-! Heap facts consumed by the primitive rows. Method provenance alone does not pin
which builtin is installed, and nominal String membership alone does not imply a payload. -/

set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

def primitiveMethods : List (ObjId × String × String) :=
  [(Boot.integerId, "+", "Integer#+"), (Boot.integerId, "-", "Integer#-"),
   (Boot.integerId, "*", "Integer#*"), (Boot.integerId, "/", "Integer#/"),
   (Boot.integerId, "<", "Integer#<"), (Boot.integerId, "to_s", "Integer#to_s"),
   (Boot.integerId, "==", "Integer#=="),
   (Boot.integerId, "zero?", "Integer#zero?"),
   (Boot.integerId, "<=", "Integer#<="), (Boot.integerId, ">=", "Integer#>="),
   (Boot.nilClassId, "==", "Object#=="), (Boot.stringId, "length", "String#length"),
   (Boot.stringId, "+", "String#+"),
   (Boot.trueClassId, "!", "Object#!"), (Boot.falseClassId, "!", "Object#!")]

def primitiveDispatchB (h : Heap) (free : String → Bool) : Bool :=
  primitiveMethods.all fun (k, name, bid) =>
    !free name || match Interp.methodOn h k name with
    | none => false
    | some (owner, md) =>
      md.builtin == some bid && !md.undefined && md.visibility == .pub && !md.fromPrelude &&
        (Interp.crubyShadow h ((ancestors h k).takeWhile (fun x => x != owner)) name).isNone

def primitiveErrorsB (h : Heap) : Bool :=
  (ancestors h Boot.zeroDivisionErrorId).contains Boot.basicObjectId &&
  !(ancestors h Boot.zeroDivisionErrorId).contains Boot.noMethodErrorId &&
  !(ancestors h Boot.zeroDivisionErrorId).contains Boot.argumentErrorId &&
  !(ancestors h Boot.zeroDivisionErrorId).contains Boot.typeErrorId

/-- Only references whose dispatch class is String need a string payload. -/
def StringPayloadOk (h : Heap) : Prop :=
  ∀ o, classOf h (.ref o) = Boot.stringId → ∃ s, (h.get o).payload = .str s

theorem primitiveDispatchB_ext {m n : Machine} (he : Ext m n) (free : String → Bool) :
    primitiveDispatchB n.heap free = primitiveDispatchB m.heap free := by
  simp only [primitiveDispatchB, Interp.methodOn, Interp.crubyShadow, className,
    he.payload, he.ancestors]

theorem primitiveErrorsB_ext {m n : Machine} (he : Ext m n) :
    primitiveErrorsB n.heap = primitiveErrorsB m.heap := by
  simp only [primitiveErrorsB, he.ancestors]

def stringPayloadB (h : Heap) : Bool :=
  (List.range h.objs.size).all fun o =>
    classOf h (.ref o) != Boot.stringId ||
      match (h.get o).payload with | .str _ => true | _ => false

theorem stringPayloadB_sound {h : Heap} (hb : stringPayloadB h = true) : StringPayloadOk h := by
  intro o hc
  by_cases ho : o < h.objs.size
  · have hp := List.all_eq_true.mp hb o (List.mem_range.mpr ho)
    simp only [hc, bne_self_eq_false, Bool.false_or] at hp
    cases hs : (h.get o).payload <;> simp_all
  · have he := classOf_oob h (Nat.le_of_not_gt ho)
    rw [he] at hc
    cases hc

#print axioms stringPayloadB_sound
end Ratchet.Denote
