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

/-- Does `s` hold a character at or above 0x80? For a **binary** String (L118)
    that means a byte no Lean `String` consumer can carry as a byte, which is
    what `toS` and the raw-stdout paths have to refuse on. -/
def hasHighByte (s : String) : Bool := s.toList.any (fun c => c.val ≥ 0x80)

/-- Escape one char per Ruby String#inspect conventions. `next?` is the
    following character (for `#{`/`#$`/`#@` escaping). `binary` selects the
    ASCII-8BIT rendering, where a non-printable is a **byte** (`\xNN`, upper
    case) rather than a code point (`\uNNNN`) [V] — `(1.chr + 0xC3.chr).inspect`
    is `"\x01\xC3"` where `"\x01".inspect` (UTF-8) is `"\u0001"` (L118). -/
private def escapeChar (binary : Bool) (c : Char) (next? : Option Char) : String :=
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
    let hexOf (width : Nat) : String :=
      let hex := String.ofList (Nat.toDigits 16 c.val.toNat) |>.toUpper
      String.ofList (List.replicate (width - hex.length) '0') ++ hex
    if binary then
      if c.val < 0x20 || c.val ≥ 0x7f then s!"\\x{hexOf 2}" else String.singleton c
    else if c.val < 0x20 || c.val == 0x7f then s!"\\u{hexOf 4}"
    else String.singleton c

def escapeStringEnc (binary : Bool) (s : String) : String := Id.run do
  let cs := s.toList
  let mut out := "\""
  for i in [0:cs.length] do
    out := out ++ escapeChar binary cs[i]! cs[i+1]?
  return out ++ "\""

def escapeString (s : String) : String := escapeStringEnc false s

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

/-- Printable without quotes in `Symbol#inspect` (identifiers, the variable
    sigils `@x`/`@@x`/`$x` — `p [:@a]` prints `[:@a]`, not `[:"@a"]` [V] — and
    operators). -/
def simpleSymbol (s : String) : Bool :=
  symbolIdentLike (stripSigil s) || operators.contains s
where
  /-- Drop a leading `@@` / `@` / `$`; the remainder must be identifier-like.
      (An ivar/cvar/gvar-named symbol cannot end in `?`/`!`/`=`, but
      `symbolIdentLike` accepting those is harmless here.) -/
  stripSigil (s : String) : String :=
    if s.startsWith "@@" then (s.drop 2).toString
    else if s.startsWith "@" || s.startsWith "$" then (s.drop 1).toString
    else s
  operators : List String :=
    ["+", "-", "*", "/", "%", "**", "==", "!=", "<", ">", "<=", ">=", "<=>",
     "===", "[]", "[]=", "<<", ">>", "!", "~", "+@", "-@", "&", "|", "^", "=~"]

def symInspect (s : String) : String :=
  if simpleSymbol s then ":" ++ s else ":" ++ escapeString s

/-- String equality including the encoding tag (L118). CRuby compares bytes
    *and*, when either operand holds a non-ASCII byte, encodings: `"a".b == "a"`
    is true but `0xC8.chr == "È"` is **false** — same single byte 0xC8 in our
    payload, different encodings. Ignoring the tag here would be a silent wrong
    answer, which is why it is checked at the leaf both `==` and `eql?` share. -/
def strEqEnc (h : Heap) (x y : ObjId) (s t : String) : Bool :=
  s == t && ((h.get x).binary == (h.get y).binary || !hasHighByte s)

/-- Strict `eql?` (type-strict: 1 ≠ 1.0). Used for hash-key matching.
    Fuel-bounded for (unconstructible-at-L0 but total-function-required)
    cyclic structures. -/
partial def valueEql (h : Heap) (a b : Value) : Bool :=
  match a, b with
  | .ref x, .ref y =>
    if x == y then true
    else
      match (h.get x).payload, (h.get y).payload with
      | .str s, .str t => strEqEnc h x y s t
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
      | .str s, .str t => strEqEnc h x y s t
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

/-- `Regexp#inspect` renders `/src/flags`, escaping only `/` in the source, and
    orders the flag letters `m i x n` [V] (`/a/imx.inspect` is `"/a/mix"`). -/
def regexpInspect (src : String) (opts : Nat) : String :=
  let esc := src.foldl (fun acc c => if c == '/' then acc ++ "\\/" else acc.push c) ""
  let f := (if opts / 4 % 2 == 1 then "m" else "") ++
           (if opts % 2 == 1 then "i" else "") ++
           (if opts / 2 % 2 == 1 then "x" else "") ++
           (if opts / 32 % 2 == 1 then "n" else "")
  "/" ++ esc ++ "/" ++ f

/-- `Regexp#to_s` renders the equivalent inline-flag group, listing the flags
    that are on, then `-`, then those that are off [V] (`/a/i.to_s` is
    `"(?i-mx:a)"`). `n` never appears. -/
def regexpToS (src : String) (opts : Nat) : String :=
  let on := (if opts / 4 % 2 == 1 then "m" else "") ++
            (if opts % 2 == 1 then "i" else "") ++
            (if opts / 2 % 2 == 1 then "x" else "")
  let off := (if opts / 4 % 2 == 1 then "" else "m") ++
             (if opts % 2 == 1 then "" else "i") ++
             (if opts / 2 % 2 == 1 then "" else "x")
  "(?" ++ on ++ (if off.isEmpty then "" else "-" ++ off) ++ ":" ++ src ++ ")"

/-- The substring a capture span denotes, in *characters*. -/
def spanText (subject : String) : Option (Nat × Nat) → Option String
  | some (a, b) => some (String.mk ((subject.toList.drop a).take (b - a)))
  | none => none

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
    | .str s => return escapeStringEnc (h.get o).binary s
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
    | .cls c =>
      -- an anonymous class/module (`Class.new`) has no name; CRuby renders it by
      -- address (L72)
      if c.name.isEmpty then return s!"#<{if c.isModule then "Module" else "Class"}:{fakeAddr o}>"
      else return c.name
    | .exc msg =>
      let cname := className h (h.get o).klass
      if msg.isEmpty then return cname else return s!"#<{cname}: {msg}>"
    | .proc _ => throw "Proc#inspect (address non-deterministic)"
    | .rng _ => throw "Random#inspect (state/address non-deterministic)"
    | .range lo hi excl =>
      -- A **nil endpoint prints as nothing** — `(1..nil).inspect` is `"1.."` and
      -- `(nil..2)` is `"..2"` — *except* when both are nil, which prints
      -- `"nil..nil"` [V]. `to_s` needs no such case: `nil.to_s` is already `""`,
      -- so it falls out, and `(nil..nil).to_s` really is `".."`. Found while
      -- validating endpoints (L122): endless ranges were the one shape whose
      -- `inspect` the model got wrong rather than gated.
      let dots := if excl then "..." else ".."
      match lo, hi with
      | .nil, .nil => return "nil" ++ dots ++ "nil"
      | .nil, _ => return dots ++ (← inspect h hi)
      | _, .nil => return (← inspect h lo) ++ dots
      | _, _ => return (← inspect h lo) ++ dots ++ (← inspect h hi)
    | .regexp src opts => return regexpInspect src opts
    | .mdata subject caps names =>
      -- `#<MatchData "1.22" 1:"1" commit:nil>` — named groups print their name
      -- instead of their index, and an unset group prints `nil` [V].
      let whole := (spanText subject (caps[0]?.getD none)).getD ""
      -- the tag on a MatchData object records its *subject*'s encoding (L118),
      -- and every span rendered here is a slice of that subject
      let esc := escapeStringEnc (h.get o).binary
      let byIdx : Nat → String := fun i =>
        match names.find? (fun p => p.2 == i) with
        | some (n, _) => n
        | none => toString i
      let parts := (caps.toList.drop 1).zipIdx.map fun (sp, j) =>
        s!"{byIdx (j + 1)}:" ++
          (match spanText subject sp with
           | some t => esc t
           | none => "nil")
      return "#<MatchData " ++ esc whole ++
        (if parts.isEmpty then "" else " " ++ String.intercalate " " parts) ++ ">"
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
    | .str s =>
      -- `to_s` hands back the **bytes**, and every consumer of this `String`
      -- (interpolation, `print`, `join`, `%`, an exception message) drops the
      -- encoding tag on the way. For a binary String that is only observable
      -- when a byte is ≥ 0x80 — where a Lean `String` would silently re-read
      -- the byte as a code point — so that case refuses rather than answering
      -- (L118). ASCII bytes are the same either way.
      if (h.get o).binary && hasHighByte s then
        throw "to_s of a byte string holding a byte ≥ 0x80 (L118)"
      else return s
    | .arr _ | .hsh _ => inspect h v
    | .cls c =>
      -- an anonymous class/module (`Class.new`) has no name; CRuby renders it by
      -- address (L72)
      if c.name.isEmpty then return s!"#<{if c.isModule then "Module" else "Class"}:{fakeAddr o}>"
      else return c.name
    | .exc msg => return msg
    | .proc _ => throw "Proc#to_s (address non-deterministic)"
    | .rng _ => throw "Random#to_s (state/address non-deterministic)"
    | .range lo hi excl =>
      return (← toS h lo) ++ (if excl then "..." else "..") ++ (← toS h hi)
    | .regexp src opts => return regexpToS src opts
    | .mdata subject caps _ =>
      let whole := (spanText subject (caps[0]?.getD none)).getD ""
      if (h.get o).binary && hasHighByte whole then
        throw "MatchData#to_s over a byte-string subject with a byte ≥ 0x80 (L118)"
      else return whole
    | .none =>
      let cname := className h (h.get o).klass
      return s!"#<{cname}:{fakeAddr o}>"

end

end RubyCore
