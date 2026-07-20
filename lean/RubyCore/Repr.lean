/-
Pure representation functions: Ruby-faithful `inspect` / `to_s` over values,
and pure `==` / `eql?`. These implement the *default* builtin behaviors
(artifact 01 §6: equality is a method; these are only the builtin leaves).

They are pure heap functions and are only sound while no user `def` has
overridden a repr-sensitive method (to_s/inspect/==/eql?/message/to_str) —
the machine tracks that with a `reprPure` flag and callers must gate on it
(returning Unsupported, never a wrong answer).

Errors (`Except String`) are Unsupported reasons, e.g. float formatting
(Ruby requires shortest-roundtrip which Lean's Float.toString is not).
-/
import RubyCore.Heap
import RubyCore.FloatFmt

namespace RubyCore

/-- Escape one char per Ruby String#inspect conventions. `next?` is the
    following character (for `#{`/`#$`/`#@` escaping). -/
private def escapeChar (c : Char) (next? : Option Char) : String :=
  match c with
  | '\\' => "\\\\"
  | '"' => "\\\""
  | '\n' => "\\n"
  | '\t' => "\\t"
  | '\r' => "\\r"
  | '\x0c' => "\\f"
  | '\x0b' => "\\v"
  | '\x08' => "\\b"
  | '\x07' => "\\a"
  | '\x1b' => "\\e"
  | '#' =>
    match next? with
    | some '{' | some '$' | some '@' => "\\#"
    | _ => "#"
  | _ =>
    if c.val < 0x20 || c.val == 0x7f then
      let hex := String.ofList (Nat.toDigits 16 c.val.toNat) |>.toUpper
      let hex := String.ofList (List.replicate (4 - hex.length) '0') ++ hex
      s!"\\u{hex}"
    else
      String.singleton c

def escapeString (s : String) : String := Id.run do
  let cs := s.toList
  let mut out := "\""
  for i in [0:cs.length] do
    out := out ++ escapeChar cs[i]! cs[i+1]?
  return out ++ "\""

/-- Identifier-like symbol (`:foo`, `:foo?`) — eligible for the bare
    `foo: v` hash-inspect shorthand [V] (operator symbols are NOT:
    `{:+ => 1}.inspect == "{\"+\": 1}"`). -/
def symbolIdentLike (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: rest =>
    (c.isAlpha || c == '_') &&
    (let core := if rest != [] && ['?', '!', '='].contains (rest.getLast!)
                 then rest.dropLast else rest
     core.all (fun c => c.isAlphanum || c == '_'))

/-- Printable without quotes in `Symbol#inspect` (identifiers AND operators). -/
def simpleSymbol (s : String) : Bool :=
  symbolIdentLike s || operators.contains s
where
  operators : List String :=
    ["+", "-", "*", "/", "%", "**", "==", "!=", "<", ">", "<=", ">=", "<=>",
     "===", "[]", "[]=", "<<", ">>", "!", "~", "+@", "-@", "&", "|", "^", "=~"]

def symInspect (s : String) : String :=
  if simpleSymbol s then ":" ++ s else ":" ++ escapeString s

/-- Strict `eql?` (type-strict: 1 ≠ 1.0). Used for hash-key matching.
    Fuel-bounded for (unconstructible-at-L0 but total-function-required)
    cyclic structures. -/
partial def valueEql (h : Heap) (a b : Value) : Bool :=
  match a, b with
  | .ref x, .ref y =>
    if x == y then true
    else
      match (h.get x).payload, (h.get y).payload with
      | .str s, .str t => s == t
      | .arr xs, .arr ys =>
        xs.size == ys.size && (xs.zip ys).all (fun (p, q) => valueEql h p q)
      | .hsh xs, .hsh ys => hashEq xs ys
      | _, _ => false
  | _, _ => a.identEq b
where
  hashEq (xs ys : Array (Value × Value)) : Bool :=
    xs.size == ys.size &&
    xs.all (fun (k, v) =>
      match ys.find? (fun (k', _) => valueEql h k k') with
      | some (_, v') => valueEql h v v'
      | none => false)

/-- Loose `==` (numeric: 1 == 1.0). The builtin default; user overrides are
    gated by `reprPure`. -/
partial def valueEq (h : Heap) (a b : Value) : Bool :=
  match a, b with
  | .int x, .flt y => Float.ofInt x == y
  | .flt x, .int y => x == Float.ofInt y
  | .flt x, .flt y => x == y
  | .ref x, .ref y =>
    if x == y then true
    else
      match (h.get x).payload, (h.get y).payload with
      | .str s, .str t => s == t
      | .arr xs, .arr ys =>
        xs.size == ys.size && (xs.zip ys).all (fun (p, q) => valueEq h p q)
      | .hsh xs, .hsh ys =>
        xs.size == ys.size &&
        xs.all (fun (k, v) =>
          match ys.find? (fun (k', _) => valueEql h k k') with
          | some (_, v') => valueEq h v v'
          | none => false)
      | _, _ => false
  | _, _ => a.identEq b

/-- Fake but deterministic "address" for default Object#inspect — the
    difftest observation normalizes `0x…` on both sides by occurrence
    order, so only distinctness + ordering matter. -/
def fakeAddr (o : ObjId) : String :=
  let hex := String.ofList (Nat.toDigits 16 o)
  "0x" ++ String.ofList (List.replicate (16 - hex.length) '0') ++ hex

mutual

/-- Ruby `inspect` (default builtin). Errors are Unsupported reasons. -/
partial def inspect (h : Heap) (v : Value) : Except String String := do
  match v with
  | .int n => return toString n
  | .flt x => return rubyFloatRepr x
  | .sym s => return symInspect s
  | .bool b => return toString b
  | .nil => return "nil"
  | .ref o =>
    -- toplevel self defines inspect/to_s to return "main" (everywhere,
    -- including nested: `p [self]` prints `[main]`) [V]
    if o == Boot.mainId then return "main"
    else
    match (h.get o).payload with
    | .str s => return escapeString s
    | .arr xs =>
      let parts ← xs.toList.mapM (inspect h)
      return "[" ++ String.intercalate ", " parts ++ "]"
    | .hsh xs =>
      if xs.isEmpty then return "{}"
      let parts ← xs.toList.mapM fun (k, val) => do
        let vs ← inspect h val
        match k with
        | .sym s =>
          if symbolIdentLike s then return s!"{s}: {vs}"
          else return s!"{escapeString s}: {vs}"
        | _ => return s!"{← inspect h k} => {vs}"
      return "{" ++ String.intercalate ", " parts ++ "}"
    | .cls c => return c.name
    | .exc msg =>
      let cname := className h (h.get o).klass
      if msg.isEmpty then return cname else return s!"#<{cname}: {msg}>"
    | .proc _ => throw "Proc#inspect (address non-deterministic)"
    | .rng _ => throw "Random#inspect (state/address non-deterministic)"
    | .range lo hi excl =>
      return (← inspect h lo) ++ (if excl then "..." else "..") ++ (← inspect h hi)
    | .none =>
      let cname := className h (h.get o).klass
      let ivars := (h.get o).ivars.reverse
      if ivars.isEmpty then
        return s!"#<{cname}:{fakeAddr o}>"
      else
        let parts ← ivars.mapM fun (n, iv) => do return s!"{n}={← inspect h iv}"
        return s!"#<{cname}:{fakeAddr o} " ++ String.intercalate ", " parts ++ ">"

/-- Ruby `to_s` (default builtin). -/
partial def toS (h : Heap) (v : Value) : Except String String := do
  match v with
  | .int n => return toString n
  | .flt x => return rubyFloatRepr x
  | .sym s => return s
  | .bool b => return toString b
  | .nil => return ""
  | .ref o =>
    if o == Boot.mainId then return "main"
    else
    match (h.get o).payload with
    | .str s => return s
    | .arr _ | .hsh _ => inspect h v
    | .cls c => return c.name
    | .exc msg => return msg
    | .proc _ => throw "Proc#to_s (address non-deterministic)"
    | .rng _ => throw "Random#to_s (state/address non-deterministic)"
    | .range lo hi excl =>
      return (← toS h lo) ++ (if excl then "..." else "..") ++ (← toS h hi)
    | .none =>
      let cname := className h (h.get o).klass
      return s!"#<{cname}:{fakeAddr o}>"

end

end RubyCore
