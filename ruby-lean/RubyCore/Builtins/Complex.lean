import RubyCore.Builtins.Rationals

/-! Native Complex rules, checked against CRuby 4.0.5. Scalar shortcuts,
    quotient evaluation order and constructor normalization are observable;
    complex.c supplies the algorithm, executable differential probes its oracle.
    Unsupported component hooks must gate rather than silently bypass dispatch. -/

namespace RubyCore.Builtins

abbrev ComplexM := StateT Machine (Except BRes)

def finishComplex (m : Machine) (action : ComplexM Value) : BRes :=
  match action.run m with | .ok (v, m) => .ok v m | .error r => r

def complexAlloc (r i : Value) : ComplexM Value := do
  let m ← get
  let (v, h) := m.heap.allocComplex r i
  set { m with heap := h }
  return v

def complexRat (n d : Int) : ComplexM Value := do
  let m ← get
  match ratResult m n d with
  | .ok v m => set m; return v
  | r => throw r

def complexNegate (v : Value) : ComplexM Value := do
  let m ← get
  match v with
  | .int n => return .int (-n)
  | .flt x => return .flt (-x)
  | _ => match rationalPayload? m.heap v with
    | some (n, d) => complexRat (-n) d
    | none => throw (.unsupported "Complex negation of a custom component")

/-- Native scalar operations used by complex.c. Default-method shortcuts also
    preserve component identity. An overridden component operation must dispatch,
    so that path currently gates instead of silently running the primitive. -/
def complexScalar (op : String) (a b : Value) : ComplexM Value := do
  let m ← get
  let h := m.heap
  unless nativeReal h a && nativeReal h b do
    throw (.unsupported "Complex arithmetic with custom numeric components")
  let owner := className h (realClassOf h a)
  if op != "quo" then
    unless (lookup h a op).any (fun (_, md) => !md.undefined && md.builtin == some (owner ++ "#" ++ op)) do
      throw (.unsupported "Complex arithmetic through an overridden component operator")
  else if programOverridden h ["quo", "/", "to_r"] (classOf h a) then
    throw (.unsupported "Complex quotient through overridden numeric conversion")
  if op == "+" then
    if a.identEq (.int 0) then return b
    if b.identEq (.int 0) then return a
  if op == "-" && b.identEq (.int 0) then return a
  if op == "*" then
    if b.identEq (.int 1) then return a
    match a with
    | .int n =>
      if b.identEq (.int 0) then return .int 0
      if n == 1 then return b
    | _ => pure ()
  if (rationalPayload? h b).isSome && (num? a).isSome &&
      programOverridden h ["coerce"] Boot.rationalId then
    throw (.unsupported "Complex component arithmetic through Rational#coerce override")
  match a, b with
  | .int x, .int y =>
    match op with
    | "+" => return .int (x + y)
    | "-" => return .int (x - y)
    | "*" => return .int (x * y)
    | _ => complexRat x y
  | _, _ =>
    match exactFraction? h a, exactFraction? h b with
    | some (n, d), some (x, y) =>
      match op with
      | "+" => complexRat (n * (y : Int) + x * (d : Int)) (d * y)
      | "-" => complexRat (n * (y : Int) - x * (d : Int)) (d * y)
      | "*" => complexRat (n * x) (d * y)
      | _ => complexRat (n * (y : Int)) ((d : Int) * x)
    | _, _ =>
      let x := realFloat h a; let y := realFloat h b
      if x.isNaN || x.isInf || y.isNaN || y.isInf then
        throw (.unsupported "Complex arithmetic with non-finite components")
      return .flt (if op == "+" then x + y else if op == "-" then x - y
        else if op == "*" then x * y else x / y)

def canonicalComponent (h : Heap) (v : Value) : Value :=
  match rationalPayload? h v with | some (n, 1) => .int n | _ => v

def complexResult (r i : Value) (canonical := false) : ComplexM Value := do
  let m ← get
  complexAlloc (if canonical then canonicalComponent m.heap r else r)
    (if canonical then canonicalComponent m.heap i else i)

def complexAbsGreater (h : Heap) (a b : Value) : Bool :=
  match exactFraction? h a, exactFraction? h b with
  | some (n, d), some (x, y) => n.natAbs * y > x.natAbs * d
  | _, _ => (realFloat h a).abs > (realFloat h b).abs

def complexBinary (op : String) (r i : Value) (other : Value) : ComplexM Value := do
  let m ← get
  match complexPayload? m.heap other with
  | some (a, b) =>
    if op == "+" || op == "-" then
      let x ← complexScalar op r a
      let y ← complexScalar op i b
      complexResult x y
    else if op == "*" then
      let ra ← complexScalar "*" r a
      let ib ← complexScalar "*" i b
      let rb ← complexScalar "*" r b
      let ia ← complexScalar "*" i a
      let x ← complexScalar "-" ra ib
      let y ← complexScalar "+" rb ia
      complexResult x y
    else
      -- CRuby's ratio-based division avoids squaring the larger divisor part.
      let (big, small, swap) := if complexAbsGreater m.heap a b then (a, b, false) else (b, a, true)
      let ratio ← complexScalar "quo" small big
      let square ← complexScalar "*" ratio ratio
      let scale ← complexScalar "+" (.int 1) square
      let denom ← complexScalar "*" big scale
      let rr ← complexScalar "*" r ratio
      let ir ← complexScalar "*" i ratio
      let nx ← if swap then complexScalar "+" rr i else complexScalar "+" r ir
      let ny ← if swap then complexScalar "-" ir r else complexScalar "-" i rr
      let x ← complexScalar "quo" nx denom
      let y ← complexScalar "quo" ny denom
      let flo := [r, i, a, b].any fun v => match v with | .flt _ => true | _ => false
      complexResult x y (!flo)
  | none =>
    unless nativeReal m.heap other do throw (coerceFailed "Complex" m other)
    if op == "+" || op == "-" then
      let x ← complexScalar op r other
      complexResult x i
    else
      let x ← complexScalar (if op == "*" then "*" else "quo") r other
      let y ← complexScalar (if op == "*" then "*" else "quo") i other
      complexResult x y (op != "*")

def complexConstructor (args : List Value) : ComplexM Value := do
  let m ← get
  if args.any (fun v => (hshPayload? m.heap v).isSome) then
    throw (.unsupported "Complex keyword options")
  let unbox := fun v => match complexPayload? m.heap v with
    | some (r, i) => if realExactZero m.heap i then r else v
    | none => v
  match args with
  | [a] =>
    if (complexPayload? m.heap a).isSome then return a
    if nativeReal m.heap a then complexAlloc a (.int 0)
    else throw (.unsupported "Complex string/custom conversion")
  | [a, b] =>
    let a := unbox a
    let b := unbox b
    let aa := complexPayload? m.heap a
    let bb := complexPayload? m.heap b
    let bzero := realExactZero m.heap b || bb.any (fun (r, i) => realZero m.heap r && realZero m.heap i)
    if aa.isSome && bzero then return a
    if !(nativeReal m.heap a || aa.isSome) || !(nativeReal m.heap b || bb.isSome) then
      throw (.unsupported "Complex string/custom/keyword conversion")
    let areal := nativeReal m.heap a || aa.any (fun (_, i) => realZero m.heap i)
    let breal := nativeReal m.heap b || bb.any (fun (_, i) => realZero m.heap i)
    if areal && breal then complexAlloc (aa.map Prod.fst |>.getD a) (bb.map Prod.fst |>.getD b) else
      if programOverridden m.heap ["+", "*", "coerce"] Boot.complexId then
        throw (.unsupported "Complex constructor through overridden Complex operators")
      let unit ← complexAlloc (.int 0) (.int 1)
      let (br, bi) := bb.getD (b, .int 0)
      let product ← complexBinary "*" br bi unit
      let (ar, ai) := aa.getD (a, .int 0)
      complexBinary "+" ar ai product
  | _ => throw (.err Boot.argumentErrorId
      s!"wrong number of arguments (given {args.length}, expected 1..2)" m)

def runComplex (bid : String) (recv : Value) (args : List Value) (m : Machine) : BRes :=
  match bid with
  | "Object#Complex" => finishComplex m (complexConstructor args)
  | "Object#__complex_rect" =>
    match args with
    | [r, i] =>
      if nativeReal m.heap r && nativeReal m.heap i then finishComplex m (complexAlloc r i)
      else .unsupported "Complex.rect non-real native operands"
    | _ => .unsupported "Complex.rect arity"
  | "Integer#i" | "Float#i" | "Rational#i" => finishComplex m (complexAlloc (.int 0) recv)
  | "Integer#to_c" | "Float#to_c" | "Rational#to_c" => finishComplex m (complexAlloc recv (.int 0))
  | "Complex#real" | "Complex#imag" | "Complex#imaginary" | "Complex#rect" | "Complex#rectangular"
  | "Complex#to_s" | "Complex#inspect" | "Complex#real?" | "Complex#to_c" | "Complex#dup"
  | "Complex#clone" | "Complex#coerce" | "Complex#==" | "Complex#eql?" | "Complex#-@"
  | "Complex#+@" | "Complex#conj" | "Complex#conjugate" | "Complex#+" | "Complex#-"
  | "Complex#*" | "Complex#/" | "Complex#quo" | "Complex#finite?" | "Complex#infinite?" =>
    match complexPayload? m.heap recv with
    | none => .unsupported "Complex method without native payload"
    | some (r, i) =>
      match bid with
      | "Complex#real" => .ok r m
      | "Complex#imag" | "Complex#imaginary" => .ok i m
      | "Complex#rect" | "Complex#rectangular" => let (v, m) := allocArr m #[r, i]; .ok v m
      | "Complex#real?" => .ok (.bool false) m
      | "Complex#to_c" | "Complex#dup" | "Complex#+@" => .ok recv m
      | "Complex#clone" => if args.isEmpty then .ok recv m else .unsupported "Complex#clone options"
      | "Complex#to_s" => match toSP m recv with | .ok s => okStr m s | .error e => .unsupported e
      | "Complex#inspect" => match inspectP m recv with | .ok s => okStr m s | .error e => .unsupported e
      | "Complex#finite?" => .ok (.bool ([r, i].all fun v => match v with
          | .flt x => !x.isNaN && !x.isInf | _ => true)) m
      | "Complex#infinite?" => .ok (if [r, i].any (fun v => match v with
          | .flt x => x.isInf | _ => false) then .int 1 else .nil) m
      | "Complex#-@" => finishComplex m do
        let x ← complexNegate r; let y ← complexNegate i; complexAlloc x y
      | "Complex#conj" | "Complex#conjugate" => finishComplex m do
        let y ← complexNegate i; complexAlloc r y
      | "Complex#==" | "Complex#eql?" => binArg m args fun b =>
        if [r, i].any (hasUserEq m.heap) then .unsupported "Complex equality through component overrides"
        else .ok (.bool (if bid == "Complex#==" then valueEq m.heap recv b else valueEql m.heap recv b)) m
      | "Complex#coerce" => binArg m args fun b =>
        if (complexPayload? m.heap b).isSome then let (v, m) := allocArr m #[b, recv]; .ok v m
        else if nativeReal m.heap b then finishComplex m do
          let x ← complexAlloc b (.int 0)
          let m ← get; let (v, m) := allocArr m #[x, recv]; set m; return v
        else .err Boot.typeErrorId s!"{className m.heap (realClassOf m.heap b)} can't be coerced into Complex" m
      | _ => binArg m args fun b => finishComplex m
          (complexBinary (if bid == "Complex#+" then "+" else if bid == "Complex#-" then "-"
            else if bid == "Complex#*" then "*" else "/") r i b)
  | _ => runRationals bid recv args m

end RubyCore.Builtins
