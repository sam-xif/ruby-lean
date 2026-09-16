/-
Vendored from Lean 4 v4.32.2 `src/lean/Lean/Data/Json/FromToJson/Basic.lean`,
under the same changes as the rest of `Json/` (see `Json/Basic.lean`), plus one
more: the declarations that reach outside `Init`/`Std` are **cut**, not ported.

Those are the `Lean.Name` / `Lean.NameMap` / `System.FilePath` instances, the
`bignum` pair and the `USize`/`UInt64` instances built on it (they want
`Lean.Syntax.decodeNatLitVal?`), and `parseTagged` / `parseCtorFields` (the
`deriving FromJson` support, which takes `Array Lean.Name`). Nothing in this
project decodes any of those types, and this project does not `deriving
FromJson` -- every `ofJson?` here is hand-written, on purpose
(`Ratchet/JsonUtil.lean`'s header says why). Each cut is marked in place.

Upstream's `FromToJson/Extra.lean` is not vendored either: it is instances for
`Std` containers that nothing here converts.

The file is present for one declaration. `Ratchet/Ty.lean` calls
`j.getObjValAs? String k`, which lives here rather than in `Basic.lean`, and its
decode-a-missing-key-as-`null` behaviour is load-bearing for `Ty.ofJson?`.

Upstream copyright header follows.
-/
/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Gabriel Ebner, Marc Huisinga
-/
module

prelude
public import Json.Printer
public import Init.Data.ToString.Macro
import Init.Data.Array.GetLit

set_option doc.verso true

public section

-- [vendoring change] upstream declares `FromJson`/`ToJson` and the `Array` /
-- `List` / `Option` / `Prod` / `Float` converters at the **root** namespace. Here
-- the whole file sits inside `namespace Json` instead, because `RubyCore/Proof/`
-- and `Denote/Clink/` do import Lean proper, and a root-level `Array.fromJson?`
-- declared twice is an import error ("environment already contains") rather than
-- a shadowing. Nothing outside this file names these, so the move costs nothing.
namespace Json


universe u

/--
Types that can be decoded from JSON.

Use `deriving FromJson`
to {manual section "deriving-instances"}[automatically generate] an instance.
See {name (scope := "Lean.Data.Json.FromToJson.Basic")}`ToJson`
for details of auto-generated instances.
-/
class FromJson (α : Type u) where
  fromJson? : Json → Except String α

export FromJson (fromJson?)

/--
Types that can be encoded as JSON.

Use `deriving ToJson`
to {manual section "deriving-instances"}[automatically generate] an instance.
The following encoding strategy is employed by auto-generated instances:
- Basic types corresponding to JSON values are encoded as these values.
  - {name}`Bool` is encoded as {lit}`true`/{lit}`false`.
  - {name}`String`s are encoded as JSON strings.
  - Numeric types are encoded as JSON numbers, with the exception of:
    - {name}`UInt64` and {name}`USize`
      which are encoded as JSON strings.
      This is because, although JSON numbers proper have unbounded range,
      in JavaScript they are parsed as [Number](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Number)s
      and these can only represent integers up to $`2^{53} - 1` safely;
      so a roundtrip through JavaScript would result in truncation on these types.
      (We use these types in the JavaScript-based Lean infoview.)
    - Special {name}`Float`s which are encoded as JSON strings:
      {lit}`"NaN"`/{lit}`"Infinity"`/{lit}`"-Infinity"`.
- {name}`Unit` is encoded as {lit}`{}` (empty JSON object).
- {name}`Array`s and {name}`List`s are encoded as JSON arrays.
- {name}`Option.none` is encoded as {lit}`null`,
  whereas {given -show}`a : α` {lean}`some a` has the same encoding as {name}`a`.
  Note that this implies {lean}`Option (Option α)` does not roundtrip,
  since {lean}`none` and {lean}`some none` both become {lit}`null`.
- General `structure`s are encoded as JSON objects in the obvious way.
  - {name}`Option` fields whose names end with `?` have special support:
    the question mark is omitted from the JSON field name,
    and such a field is omitted from the JSON object when its value is {name}`none`
    (as opposed to being encoded as {lit}`{ "someField": null }`).
- General `inductive` types are encoded on a per-constructor basis.
  - An argument-free constructor is encoded as its name (a JSON string).
  - A constructor with named arguments only is encoded as the JSON object
    {lit}`{ "ctorName": { "arg1": argVal1, ..., "argN": argValN } }`.
  - A constructor with one unnamed argument is encoded as the JSON object
    {lit}`{ "ctorName": argVal }`.
  - A constructor with more than one unnamed argument is encoded as the JSON object
    {lit}`{ "ctorName": [argVal1, ..., argValN] }`.
- Certain other types have special handling: see the instances below. -/
class ToJson (α : Type u) where
  toJson : α → Json

export ToJson (toJson)

instance : FromJson Json := ⟨Except.ok⟩
instance : ToJson Json := ⟨id⟩

instance : FromJson JsonNumber := ⟨Json.getNum?⟩
instance : ToJson JsonNumber := ⟨Json.num⟩

instance : FromJson Unit :=
  ⟨fun
    | .obj .empty => .ok ()
    | json => .error s!"expected \{} to decode Unit, got {json}"⟩
instance : ToJson Unit := ⟨fun _ => Json.obj {}⟩
instance : FromJson Empty where
  fromJson? j := throw (s!"type Empty has no constructor to match JSON value '{j}'. \
                           This occurs when deserializing a value for type Empty, \
                           e.g. at type Option Empty with code for the 'some' constructor.")

instance : ToJson Empty := ⟨nofun⟩
-- looks like id, but there are coercions happening
instance : FromJson Bool := ⟨Json.getBool?⟩
instance : ToJson Bool := ⟨fun b => b⟩
instance : FromJson Nat := ⟨Json.getNat?⟩
instance : ToJson Nat := ⟨fun n => n⟩
instance : FromJson Int := ⟨Json.getInt?⟩
instance : ToJson Int := ⟨fun n => Json.num n⟩
instance : FromJson String := ⟨Json.getStr?⟩
instance : ToJson String := ⟨fun s => s⟩
instance : FromJson String.Slice := ⟨Except.map String.toSlice ∘ Json.getStr?⟩
instance : ToJson String.Slice := ⟨fun s => s.copy⟩

-- [vendoring cut] `System.FilePath` instances -- see this file's header.

protected def Array.fromJson? [FromJson α] : Json → Except String (Array α)
  | Json.arr a => a.mapM fromJson?
  | j          => throw s!"expected JSON array, got '{j}'"

instance [FromJson α] : FromJson (Array α) where
  fromJson? := Array.fromJson?

protected def Array.toJson [ToJson α] (a : Array α) : Json :=
  Json.arr (a.map toJson)

instance [ToJson α] : ToJson (Array α) where
  toJson := Array.toJson

protected def List.fromJson? [FromJson α] (j : Json) : Except String (List α) :=
  (fromJson? j (α := Array α)).map Array.toList

instance [FromJson α] : FromJson (List α) where
  fromJson? := List.fromJson?

protected def List.toJson [ToJson α] (a : List α) : Json :=
  toJson a.toArray

instance [ToJson α] : ToJson (List α) where
  toJson := List.toJson

protected def Option.fromJson? [FromJson α] : Json → Except String (Option α)
  | Json.null => Except.ok none
  | j         => some <$> fromJson? j

instance [FromJson α] : FromJson (Option α) where
  fromJson? := Option.fromJson?

protected def Option.toJson [ToJson α] : Option α → Json
  | none   => Json.null
  | some a => toJson a

instance [ToJson α] : ToJson (Option α) where
  toJson := Option.toJson

protected def Prod.fromJson? {α : Type u} {β : Type v} [FromJson α] [FromJson β] : Json → Except String (α × β)
  | Json.arr #[ja, jb] => do
    let ⟨a⟩ : ULift.{v} α := ← (fromJson? ja).map ULift.up
    let ⟨b⟩ : ULift.{u} β := ← (fromJson? jb).map ULift.up
    return (a, b)
  | j => throw s!"expected pair, got '{j}'"

instance {α : Type u} {β : Type v} [FromJson α] [FromJson β] : FromJson (α × β) where
  fromJson? := Prod.fromJson?

protected def Prod.toJson [ToJson α] [ToJson β] : α × β → Json
  | (a, b) => Json.arr #[toJson a, toJson b]

instance [ToJson α] [ToJson β] : ToJson (α × β) where
  toJson := Prod.toJson

-- [vendoring cut] the `Lean.Name` / `Lean.NameMap` instances, the `bignum` pair, and the `USize` / `UInt64` instances built on it -- see this file's header.


protected def Float.toJson (x : Float) : Json :=
  match JsonNumber.fromFloat? x with
  | Sum.inl e => Json.str e
  | Sum.inr n => Json.num n

instance : ToJson Float where
  toJson := Float.toJson

protected def Float.fromJson? : Json → Except String Float
  | (Json.str "Infinity") => Except.ok (1.0 / 0.0)
  | (Json.str "-Infinity") => Except.ok (-1.0 / 0.0)
  | (Json.str "NaN") => Except.ok (0.0 / 0.0)
  | (Json.num jn) => Except.ok jn.toFloat
  | _ => Except.error "Expected a number or a string 'Infinity', '-Infinity', 'NaN'."

instance : FromJson Float where
  fromJson? := Float.fromJson?


protected def Structured.fromJson? : Json → Except String Structured
  | .arr a => return Structured.arr a
  | .obj o => return Structured.obj o
  | j     => throw s!"expected structured object, got '{j}'"

instance : FromJson Structured where
  fromJson? := Structured.fromJson?

protected def Structured.toJson : Structured → Json
  | .arr a => .arr a
  | .obj o => .obj o

instance : ToJson Structured where
  toJson := Structured.toJson

def toStructured? [ToJson α] (v : α) : Except String Structured :=
  fromJson? (toJson v)

def getObjValAs? (j : Json) (α : Type u) [FromJson α] (k : String) : Except String α :=
  fromJson? <| j.getObjValD k

def setObjValAs! (j : Json) {α : Type u} [ToJson α] (k : String) (v : α) : Json :=
  j.setObjVal! k <| toJson v

def opt [ToJson α] (k : String) : Option α → List (String × Json)
  | none   => []
  | some o => [⟨k, toJson o⟩]

/-- Returns the string value or single key name, if any. -/
def getTag? : Json → Option String
  | .str tag => some tag
  | .obj kvs => guard (kvs.size == 1) *> kvs.minKey?
  | _        => none

-- TODO: delete after rebootstrap
-- [vendoring cut] `parseTagged` / `parseCtorFields`, the `deriving FromJson` support -- see this file's header.

end Json
