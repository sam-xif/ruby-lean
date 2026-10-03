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
   (Boot.trueClassId, "!", "Object#!"), (Boot.falseClassId, "!", "Object#!"),
   (Boot.integerId, "<=>", "Integer#<=>"), (Boot.integerId, "nil?", "Object#nil?"),
   (Boot.symbolId, "to_s", "Symbol#to_s"), (Boot.symbolId, "==", "Symbol#=="),
   (Boot.arrayId, "length", "Array#length"), (Boot.stringId, "start_with?", "String#start_with?"),
   (Boot.hashId, "key?", "Hash#key?"), (Boot.arrayId, "compact", "Array#compact"),
   (Boot.arrayId, "uniq", "Array#uniq"), (Boot.hashId, "fetch", "Hash#fetch"),
   (Boot.stringId, "===", "String#=="),
   (Boot.stringId, "split", "String#split"), (Boot.nilClassId, "nil?", "NilClass#nil?"),
   (Boot.stringId, "match?", "String#match?"), (Boot.stringId, "nil?", "Object#nil?"),
   (Boot.integerId, "is_a?", "Object#is_a?"), (Boot.stringId, "is_a?", "Object#is_a?"),
   (Boot.floatId, "is_a?", "Object#is_a?"), (Boot.nilClassId, "is_a?", "Object#is_a?"),
   (Boot.symbolId, "is_a?", "Object#is_a?"), (Boot.objectId, "is_a?", "Object#is_a?")]

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

/-- Native Array#each has an installed builtin row. A payload alone cannot exclude
an override, visibility change, or undef tombstone. Reserving each withdraws this capability. -/
def eachDispatchB (h : Heap) (free : String → Bool) : Bool :=
  !free "each" || match Interp.methodOn h Boot.arrayId "each" with
    | none => false
    | some (owner, md) =>
      md.builtin == some "Array#each" && !md.undefined && md.visibility == .pub && !md.fromPrelude &&
        (Interp.crubyShadow h ((ancestors h Boot.arrayId).takeWhile (· != owner)) "each").isNone

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

theorem each_lookup {h : Heap} {free : String → Bool}
    (hd : primitiveDispatchB h free = true) (hf : free "each" = true) :
    ∃ owner md, Interp.methodOn h Boot.arrayId "each" = some (owner, md) ∧
      md.builtin = some "Array#each" ∧ md.undefined = false ∧ md.visibility = .pub ∧
      md.fromPrelude = false ∧
      Interp.crubyShadow h ((ancestors h Boot.arrayId).takeWhile (· != owner)) "each" = none := by
  simp only [primitiveDispatchB, Bool.and_eq_true] at hd
  have hp := hd.2
  simp only [eachDispatchB, hf, Bool.not_true, Bool.false_or] at hp
  cases hl : Interp.methodOn h Boot.arrayId "each" with
  | none => rw [hl] at hp; cases hp
  | some p =>
    obtain ⟨owner, md⟩ := p
    refine ⟨owner, md, rfl, ?_⟩
    simpa only [hl, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
      Option.isNone_iff_eq_none, and_assoc] using hp

def primitiveErrorClasses : List ObjId :=
  [Boot.zeroDivisionErrorId, Boot.nameErrorId, Boot.frozenErrorId, Boot.keyErrorId]

def primitiveErrorB (h : Heap) (cls : ObjId) : Bool :=
  (ancestors h cls).contains Boot.basicObjectId &&
  !(ancestors h cls).contains Boot.noMethodErrorId &&
  !(ancestors h cls).contains Boot.argumentErrorId &&
  !(ancestors h cls).contains Boot.typeErrorId

def primitiveErrorsB (h : Heap) : Bool := primitiveErrorClasses.all (primitiveErrorB h)

/-- ZeroDivisionError runs the native initializer before being raised. NameError
constructs its payload directly; FrozenError has a separate prelude initializer. -/
def primitiveInitClasses : List ObjId := [Boot.zeroDivisionErrorId]

/-- The protected prefix resolves initialize before any program definition on Object.
The exact prefix also makes preservation under later method installation explicit. -/
def errorInitChain : List ObjId :=
  [Boot.zeroDivisionErrorId, Boot.standardErrorId, Boot.exceptionId,
    Boot.objectId, Boot.kernelId, Boot.basicObjectId]

def errorInitOwn (h : Heap) (k : ObjId) : Option MethodDef :=
  (h.classPayload? k).bind fun cp => (cp.methods.find? (·.1 == "initialize")).map (·.2)

def primitiveInitShapeB (h : Heap) : Bool :=
  ancestors h Boot.zeroDivisionErrorId == errorInitChain &&
    (errorInitOwn h Boot.zeroDivisionErrorId).isNone &&
    (errorInitOwn h Boot.standardErrorId).isNone &&
    (errorInitOwn h Boot.exceptionId).any (fun md => !md.visibilityOnly)

def primitiveInitB (h : Heap) : Bool :=
  primitiveInitShapeB h && primitiveInitClasses.all fun k => match Interp.methodOn h k "initialize" with
    | none => false
    | some (owner, md) =>
      md.builtin == some "Exception#initialize" && !md.undefined && !md.fromPrelude &&
        (Interp.crubyShadow h ((ancestors h k).takeWhile (· != owner)) "initialize").isNone

theorem primitiveInit_lookup {h : Heap} (hi : primitiveInitB h = true) {k : ObjId}
    (hk : k ∈ primitiveInitClasses) :
    ∃ owner md, Interp.methodOn h k "initialize" = some (owner, md) ∧
      md.builtin = some "Exception#initialize" ∧ md.undefined = false ∧ md.fromPrelude = false ∧
      Interp.crubyShadow h ((ancestors h k).takeWhile (· != owner)) "initialize" = none := by
  simp only [primitiveInitB, Bool.and_eq_true] at hi
  have hp := List.all_eq_true.mp hi.2 k hk
  cases hl : Interp.methodOn h k "initialize" with
  | none => rw [hl] at hp; cases hp
  | some p =>
    obtain ⟨owner, md⟩ := p
    refine ⟨owner, md, rfl, ?_⟩
    simpa only [hl, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
      Option.isNone_iff_eq_none, and_assoc] using hp

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

/-- Frozen objects carry no fields: the fragment never freezes an object, and fresh or
    literal-frozen objects start without ivars. A field write therefore never meets a
    frozen receiver whose field is a non-nil scalar. -/
def FrozenFieldsOk (h : Heap) : Prop :=
  ∀ o, (h.get o).frozen = true → (h.get o).ivars = []

def frozenFieldsB (h : Heap) : Bool :=
  (List.range h.objs.size).all fun o => !(h.get o).frozen || (h.get o).ivars.isEmpty

theorem frozenFieldsB_sound {h : Heap} (hb : frozenFieldsB h = true) : FrozenFieldsOk h := by
  intro o hf
  by_cases ho : o < h.objs.size
  · have hp := List.all_eq_true.mp hb o (List.mem_range.mpr ho)
    simpa only [hf, Bool.not_true, Bool.false_or, List.isEmpty_iff] using hp
  · rw [get_oob h (Nat.le_of_not_gt ho)] at hf ⊢
    rfl

theorem FrozenFieldsOk.ext {m n : Machine} (h : FrozenFieldsOk m.heap) (he : Ext m n) :
    FrozenFieldsOk n.heap := by
  intro o hf
  by_cases ho : o < m.heap.objs.size
  · rw [he.get o ho] at hf ⊢; exact h o hf
  · exact he.freshIvars o (Nat.le_of_not_gt ho)

/-- Transport: each object keeps its frozen bit and fields, or is unfrozen. -/
theorem FrozenFieldsOk.of_fields {h h' : Heap} (hf : FrozenFieldsOk h)
    (hp : ∀ o, (h'.get o).frozen = false ∨
      ((h'.get o).frozen = (h.get o).frozen ∧ (h'.get o).ivars = (h.get o).ivars)) :
    FrozenFieldsOk h' := by
  intro o ho
  rcases hp o with h0 | ⟨h1, h2⟩
  · rw [h0] at ho; cases ho
  · rw [h2]; exact hf o (h1 ▸ ho)

/-- Replacing an object's payload keeps every frozen bit and field list. -/
theorem fields_setPayload (h : Heap) (o k : ObjId) (p : Payload) :
    ((h.set o { h.get o with payload := p }).get k).frozen = (h.get k).frozen ∧
      ((h.set o { h.get o with payload := p }).get k).ivars = (h.get k).ivars := by
  simp only [Heap.get, Heap.set]
  by_cases hk : k = o
  · subst k
    by_cases ho : o < h.objs.size
    · rw [Proof.objs_getD_set!_self _ _ _ ho]; exact ⟨rfl, rfl⟩
    · rw [Proof.objs_getD_set!_oob _ _ _ ho]; exact ⟨rfl, rfl⟩
  · rw [Proof.objs_getD_set!_ne _ _ _ _ hk]; exact ⟨rfl, rfl⟩

theorem fields_constSetIn (h : Heap) (cls k : ObjId) (n : String) (v : Value) :
    ((constSetIn h cls n v).get k).frozen = (h.get k).frozen ∧
      ((constSetIn h cls n v).get k).ivars = (h.get k).ivars := by
  unfold constSetIn
  split
  · exact fields_setPayload h cls k _
  · exact ⟨rfl, rfl⟩

theorem primitiveDispatchB_ext {m n : Machine} (he : Ext m n) (hn : Proof.NamesOk m.heap)
    (hc : Proof.ChainsIn m.heap) (free : String → Bool) :
    primitiveDispatchB n.heap free = primitiveDispatchB m.heap free := by
  simp only [primitiveDispatchB, nativeDispatchB, eachDispatchB, he.methodOn_eq hc,
    he.crubyShadow_eq hn, he.ancestors]

theorem primitiveInitB_ext {m n : Machine} (he : Ext m n) (hn : Proof.NamesOk m.heap)
    (hc : Proof.ChainsIn m.heap) : primitiveInitB n.heap = primitiveInitB m.heap := by
  simp only [primitiveInitB, primitiveInitShapeB, errorInitOwn, he.payload, he.methodOn_eq hc, he.crubyShadow_eq hn, he.ancestors]

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
