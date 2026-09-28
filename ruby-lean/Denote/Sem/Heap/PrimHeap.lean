import Denote.Ty.Grow

/-! Heap facts consumed by the primitive rows. Method provenance alone does not pin
which builtin is installed, and nominal String membership alone does not imply a payload. -/

set_option autoImplicit false
namespace Ratchet.Denote
open RubyCore

def primitiveMethods : List (ObjId × String × String) :=
  [(Boot.integerId, "+", "Integer#+"), (Boot.integerId, "-", "Integer#-"),
   (Boot.integerId, "*", "Integer#*"), (Boot.integerId, "/", "Integer#/"),
   (Boot.integerId, "<", "Integer#<"), (Boot.integerId, ">", "Integer#>"),
   (Boot.integerId, "to_s", "Integer#to_s"),
   (Boot.integerId, "==", "Integer#=="),
   (Boot.integerId, "zero?", "Integer#zero?"),
   (Boot.integerId, "<=", "Integer#<="), (Boot.integerId, ">=", "Integer#>="),
   (Boot.nilClassId, "==", "Object#=="), (Boot.stringId, "length", "String#length"),
   (Boot.stringId, "+", "String#+"),
   (Boot.arrayId, "[]", "Array#[]"),
   (Boot.hashId, "[]", "Hash#[]"),
   (Boot.trueClassId, "!", "Object#!"), (Boot.falseClassId, "!", "Object#!")]

/-- Native lookup facts include Proc calls, Array iterators and Symbol conversion.
Membership is not a pure-builtin signature; primitiveMethods alone supplies those rows. -/
def dispatchMethods : List (ObjId × String × String) :=
  primitiveMethods ++ [(Boot.procId, "call", "Proc#call"), (Boot.procId, "[]", "Proc#[]"),
    (Boot.arrayId, "map", "Array#map"), (Boot.arrayId, "collect", "Array#collect"),
    (Boot.symbolId, "to_proc", "Symbol#to_proc")]

def nativeDispatchB (h : Heap) (free : String → Bool) : Bool :=
  dispatchMethods.all fun (k, name, bid) =>
    !free name || match Interp.methodOn h k name with
    | none => false
    | some (owner, md) =>
      md.builtin == some bid && !md.undefined && md.visibility == .pub && !md.fromPrelude &&
        (Interp.crubyShadow h ((ancestors h k).takeWhile (fun x => x != owner)) name).isNone

/-- Native Array#each is reached only on a lookup miss. A payload alone cannot
exclude an override or an undef tombstone. Reserving each withdraws this capability. -/
def eachDispatchB (h : Heap) (free : String → Bool) : Bool :=
  !free "each" || (Interp.methodOn h Boot.arrayId "each").isNone

def primitiveDispatchB (h : Heap) (free : String → Bool) : Bool :=
  nativeDispatchB h free && eachDispatchB h free

theorem dispatch_lookup {h : Heap} {free : String → Bool}
    (hd : primitiveDispatchB h free = true) {k : ObjId} {name bid : String}
    (hr : (k, name, bid) ∈ dispatchMethods) (hf : free name = true) :
    ∃ owner md, Interp.methodOn h k name = some (owner, md) ∧
      md.builtin = some bid ∧ md.undefined = false ∧ md.visibility = .pub ∧
      md.fromPrelude = false ∧
      Interp.crubyShadow h ((ancestors h k).takeWhile (fun x => x != owner)) name = none := by
  simp only [primitiveDispatchB, Bool.and_eq_true] at hd
  have hp := List.all_eq_true.mp hd.1 (k, name, bid) hr
  simp only [hf, Bool.not_true, Bool.false_or] at hp
  cases hl : Interp.methodOn h k name with
  | none => rw [hl] at hp; cases hp
  | some p =>
    obtain ⟨owner, md⟩ := p
    refine ⟨owner, md, rfl, ?_⟩
    simpa only [hl, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
      Option.isNone_iff_eq_none, and_assoc] using hp

theorem each_lookup_miss {h : Heap} {free : String → Bool}
    (hd : primitiveDispatchB h free = true) (hf : free "each" = true) :
    Interp.methodOn h Boot.arrayId "each" = none := by
  simp only [primitiveDispatchB, Bool.and_eq_true] at hd
  simpa only [eachDispatchB, hf, Bool.not_true, Bool.false_or,
    Option.isNone_iff_eq_none] using hd.2

def primitiveErrorClasses : List ObjId := [Boot.zeroDivisionErrorId, Boot.nameErrorId, Boot.frozenErrorId]

def primitiveErrorB (h : Heap) (cls : ObjId) : Bool :=
  (ancestors h cls).contains Boot.basicObjectId &&
  !(ancestors h cls).contains Boot.noMethodErrorId &&
  !(ancestors h cls).contains Boot.argumentErrorId &&
  !(ancestors h cls).contains Boot.typeErrorId

def primitiveErrorsB (h : Heap) : Bool := primitiveErrorClasses.all (primitiveErrorB h)

/-- Only references whose dispatch class is String need a string payload. -/
def StringPayloadOk (h : Heap) : Prop :=
  ∀ o, classOf h (.ref o) = Boot.stringId → ∃ s, (h.get o).payload = .str s

/-- In the current fragment, array payloads dispatch through the boot Array class.
    Payload shape alone does not establish this, especially at an incoming environment. -/
def ArrayPayloadOk (h : Heap) : Prop :=
  ∀ o xs, (h.get o).payload = .arr xs → classOf h (.ref o) = Boot.arrayId

def arrayPayloadB (h : Heap) : Bool :=
  (List.range h.objs.size).all fun o =>
    match (h.get o).payload with
    | .arr _ => classOf h (.ref o) == Boot.arrayId
    | _ => true

theorem arrayPayloadB_sound {h : Heap} (hb : arrayPayloadB h = true) : ArrayPayloadOk h := by
  intro o xs hx
  by_cases ho : o < h.objs.size
  · have hp := List.all_eq_true.mp hb o (List.mem_range.mpr ho)
    simpa only [hx, beq_iff_eq] using hp
  · rw [get_oob h (Nat.le_of_not_gt ho)] at hx
    cases hx

/-- Both absent defaults and explicit nil defaults return nil on a miss. -/
def hashDefaultNilB : Option HashDefault → Bool
  | none | some (.val .nil) => true
  | _ => false

theorem hashDefaultNilB_cases {d : Option HashDefault} (hd : hashDefaultNilB d = true) :
    d = none ∨ d = some (.val .nil) := by
  cases d with
  | none => exact Or.inl rfl
  | some d =>
    cases d with
    | prc _ => cases hd
    | val v => cases v <;> simp_all [hashDefaultNilB]

/-- Literal-fragment hashes use Hash dispatch and have no non-nil/default-proc behavior. -/
def HashPayloadOk (h : Heap) : Prop :=
  ∀ o xs, (h.get o).payload = .hsh xs →
    classOf h (.ref o) = Boot.hashId ∧ hashDefaultNilB (h.get o).hashDflt = true

def hashPayloadB (h : Heap) : Bool :=
  (List.range h.objs.size).all fun o =>
    match (h.get o).payload with
    | .hsh _ => classOf h (.ref o) == Boot.hashId && hashDefaultNilB (h.get o).hashDflt
    | _ => true

theorem hashPayloadB_sound {h : Heap} (hb : hashPayloadB h = true) : HashPayloadOk h := by
  intro o xs hx
  by_cases ho : o < h.objs.size
  · have hp := List.all_eq_true.mp hb o (List.mem_range.mpr ho)
    simpa only [hx, Bool.and_eq_true, beq_iff_eq] using hp
  · rw [get_oob h (Nat.le_of_not_gt ho)] at hx
    cases hx

theorem primitiveDispatchB_ext {m n : Machine} (he : Ext m n) (free : String → Bool) :
    primitiveDispatchB n.heap free = primitiveDispatchB m.heap free := by
  simp only [primitiveDispatchB, nativeDispatchB, eachDispatchB, Interp.methodOn, Interp.crubyShadow, className,
    he.payload, he.ancestors]

theorem primitiveErrorsB_ext {m n : Machine} (he : Ext m n) :
    primitiveErrorsB n.heap = primitiveErrorsB m.heap := by
  unfold primitiveErrorsB
  congr 1
  funext cls
  simp only [primitiveErrorB, he.ancestors]

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
