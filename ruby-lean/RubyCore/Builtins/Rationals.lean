import RubyCore.Builtins.Strings

/-! Rational primitives (L278). Conversion hooks and operators still pass through
    ordinary dispatch. Strings/custom constructor conversions are explicitly gated. -/
namespace RubyCore.Builtins

def allocRat (m : Machine) (n : Int) (d : Nat) : Value × Machine :=
  let (v, h) := m.heap.allocRational n d
  (v, { m with heap := h })

def ratResult (m : Machine) (n d : Int) : BRes :=
  if d == 0 then .err Boot.zeroDivisionErrorId "divided by 0" m else
  let (v, m) := allocRat m (if d < 0 then -n else n) d.natAbs
  .ok v m

def constructorFraction? (h : Heap) : Value → Option (Int × Nat)
  | .flt x => floatFraction? x
  | v => exactFraction? h v

def rationalConstructor (m : Machine) (args : List Value) : BRes :=
  if args.any (fun v => match v with
    | .ref o => match (m.heap.get o).payload with | .hsh _ => true | _ => false
    | _ => false) then .unsupported "Rational constructor keyword/hash arguments" else
  match args with
  | [v] | [v, .int 1] =>
    if (rationalPayload? m.heap v).isSome then .ok v m
    else match constructorFraction? m.heap v with
      | some (n, d) => ratResult m n d
      | none => .unsupported "Rational constructor: string/custom/non-finite conversion"
  | [v, w] =>
    match constructorFraction? m.heap v, constructorFraction? m.heap w with
    | some (n, d), some (a, b) => ratResult m (n * (b : Int)) ((d : Int) * a)
    | _, _ => .unsupported "Rational constructor: string/custom/non-finite conversion"
  | _ => .err Boot.argumentErrorId
      s!"wrong number of arguments (given {args.length}, expected 1..2)" m

def rationalBinary (bid : String) (recv other : Value) (m : Machine)
    (n : Int) (d : Nat) : BRes :=
  match exactFraction? m.heap other with
  | some (a, b) =>
    match bid with
    | "Rational#+" => ratResult m (n * (b : Int) + a * (d : Int)) (d * b)
    | "Rational#-" => ratResult m (n * (b : Int) - a * (d : Int)) (d * b)
    | "Rational#*" => ratResult m (n * a) (d * b)
    | "Rational#/" | "Rational#quo" => ratResult m (n * (b : Int)) ((d : Int) * a)
    | "Rational#<=>" =>
      let x := n * (b : Int); let y := a * (d : Int)
      .ok (.int (if x < y then -1 else if x == y then 0 else 1)) m
    | _ => .unsupported bid
  | none =>
    match other with
    | .flt y =>
      let x := fractionFloat n d
      match bid with
      | "Rational#+" => .ok (.flt (x + y)) m
      | "Rational#-" => .ok (.flt (x - y)) m
      | "Rational#*" => .ok (.flt (x * y)) m
      | "Rational#/" | "Rational#quo" => .ok (.flt (x / y)) m
      | "Rational#<=>" =>
        if x.isNaN || y.isNaN then .ok .nil m
        else .ok (.int (if x < y then -1 else if x == y then 0 else 1)) m
      | _ => .unsupported bid
    | _ =>
      if bid == "Rational#<=>" then .ok .nil m
      else coerceFailed (className m.heap (realClassOf m.heap recv)) m other

def runRationals (bid : String) (recv : Value) (args : List Value) (m : Machine) : BRes :=
  match bid with
  | "Object#Rational" => rationalConstructor m args
  | "Integer#to_r" | "Float#to_r" => rationalConstructor m [recv]
  | "Rational#numerator" | "Rational#denominator" | "Rational#to_s" | "Rational#inspect"
  | "Rational#to_i" | "Rational#to_f" | "Rational#to_r" | "Rational#-@" | "Rational#+@"
  | "Rational#abs" | "Rational#magnitude" | "Rational#positive?" | "Rational#negative?"
  | "Rational#dup" | "Rational#clone" | "Rational#eql?" | "Rational#==" | "Rational#coerce"
  | "Rational#+" | "Rational#-" | "Rational#*" | "Rational#/" | "Rational#quo"
  | "Rational#<=>" | "Rational#**" | "Rational#floor" | "Rational#ceil" | "Rational#truncate" =>
    match rationalPayload? m.heap recv with
    | none => .unsupported "Rational method on a non-Rational payload"
    | some (n, d) =>
      match bid with
      | "Rational#numerator" => .ok (.int n) m
      | "Rational#denominator" => .ok (.int d) m
      | "Rational#to_s" => match toSP m recv with
        | .ok s => okStr m s | .error e => .unsupported e
      | "Rational#inspect" => match inspectP m recv with
        | .ok s => okStr m s | .error e => .unsupported e
      | "Rational#to_r" | "Rational#+@" | "Rational#dup" => .ok recv m
      | "Rational#clone" =>
        if args.isEmpty then .ok recv m else .unsupported "Rational#clone with arguments"
      | "Rational#to_i" => .ok (.int (n.tdiv (d : Int))) m
      | "Rational#to_f" => .ok (.flt (fractionFloat n d)) m
      | "Rational#-@" => ratResult m (-n) d
      | "Rational#abs" | "Rational#magnitude" =>
        if n < 0 then ratResult m (-n) d else .ok recv m
      | "Rational#positive?" => .ok (.bool (n > 0)) m
      | "Rational#negative?" => .ok (.bool (n < 0)) m
      | "Rational#eql?" => binArg m args fun b => .ok (.bool (valueEql m.heap recv b)) m
      | "Rational#==" => binArg m args fun b => .ok (.bool (valueEq m.heap recv b)) m
      | "Rational#floor" | "Rational#ceil" | "Rational#truncate" =>
        if !args.isEmpty then .unsupported "Rational rounding with digit precision" else
        .ok (.int (if bid == "Rational#floor" then n.fdiv d
          else if bid == "Rational#ceil" then -((-n).fdiv d) else n.tdiv (d : Int))) m
      | "Rational#**" => binArg m args fun b =>
        match b with
        | .int e =>
          if e ≥ 0 then ratResult m (n ^ e.toNat) ((d : Int) ^ e.toNat)
          else ratResult m ((d : Int) ^ (-e).toNat) (n ^ (-e).toNat)
        | _ => .unsupported "Rational exponent other than Integer"
      | "Rational#coerce" => binArg m args fun b =>
        match b with
        | .int a =>
          let (v, m) := allocRat m a 1
          let (pair, m) := allocArr m #[v, recv]
          .ok pair m
        | .flt _ =>
          let (pair, m) := allocArr m #[b, .flt (fractionFloat n d)]
          .ok pair m
        | _ =>
          if (rationalPayload? m.heap b).isSome then
            let (pair, m) := allocArr m #[b, recv]
            .ok pair m
          else .err Boot.typeErrorId
            s!"{className m.heap (realClassOf m.heap b)} can't be coerced into Rational" m
      | _ => binArg m args fun b => rationalBinary bid recv b m n d
  | _ => runStrings bid recv args m

end RubyCore.Builtins
