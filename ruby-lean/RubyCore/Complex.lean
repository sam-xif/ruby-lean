import RubyCore.Rational
import RubyCore.FloatFmt

namespace RubyCore

def complexPayload? (h : Heap) : Value → Option (Value × Value)
  | .ref o => match (h.get o).payload with
    | .complex r i => some (r, i)
    | _ => none
  | _ => none

def Heap.allocComplex (h : Heap) (real imag : Value) : Value × Heap :=
  let (o, h) := h.alloc { klass := Boot.complexId, frozen := true, payload := .complex real imag }
  (.ref o, h)

def nativeReal (h : Heap) (v : Value) : Bool :=
  match v with | .int _ | .flt _ => true | _ => (rationalPayload? h v).isSome

def realZero (h : Heap) (v : Value) : Bool :=
  match v with
  | .int n => n == 0
  | .flt x => x == 0
  | _ => ((rationalPayload? h v).map (·.1 == 0)).getD false

def realExactZero (h : Heap) (v : Value) : Bool :=
  match v with | .flt _ => false | _ => nativeReal h v && realZero h v

def realFloat (h : Heap) (v : Value) : Float :=
  match v with
  | .int n => exactFractionFloat n 1
  | .flt x => x
  | _ => match rationalPayload? h v with
    | some (n, d) => fractionFloat n d
    | none => 0

def realNegative (h : Heap) (v : Value) : Bool :=
  match v with
  | .int n => n < 0
  | .flt x => !x.isNaN && x.toBits >>> 63 == 1
  | _ => ((rationalPayload? h v).map (fun p => decide (p.1 < 0))).getD false

/-- Native real component rendering; callers check overridden component methods. -/
def realText (h : Heap) (inspectMode absolute : Bool) (v : Value) : Except String String :=
  match v with
  | .int n => .ok (toString (if absolute then (n.natAbs : Int) else n))
  | .flt x => .ok (rubyFloatRepr (if absolute then x.abs else x))
  | _ => match rationalPayload? h v with
    | some (n, d) =>
      let text := s!"{if absolute then (n.natAbs : Int) else n}/{d}"
      .ok (if inspectMode then "(" ++ text ++ ")" else text)
    | none => .error "Complex component outside the native numeric tower"

def complexText (h : Heap) (inspectMode : Bool) (r i : Value) : Except String String := do
  let rs ← realText h inspectMode false r
  let is ← realText h inspectMode true i
  let star := if (is.toList.getLast?).any Char.isDigit then "" else "*"
  let body := rs ++ (if realNegative h i then "-" else "+") ++ is ++ star ++ "i"
  return if inspectMode then "(" ++ body ++ ")" else body

end RubyCore
