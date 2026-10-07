/-
The default `inspect`, `to_s`, `==` and `eql?` (Semantics 01 §6).

These are the builtin behaviors, as pure functions of the heap, exact to the
character: `inspect` and `to_s` produce the strings CRuby prints. Equality is a
method in Ruby, so these are what runs when no user definition overrides it;
the interpreter decides when that is the case and dispatches otherwise.

The recursive functions take fuel so that they are total and the kernel can
evaluate them. Running out of fuel answers as CRuby's recursion guard does for
a structure that contains itself.

An `Except String` error is a reason the model declines, never a guess.
-/
import RubyCore.Numeric.Complex
import RubyCore.Numeric.FloatFmt
import RubyCore.Generated.Unicode

namespace RubyCore

/-- Does `s` hold a character at or above 0x80? For a **binary** String
    that means a byte no Lean `String` consumer can carry as a byte, which is
    what `toS` and the raw-stdout paths have to refuse on. -/
def hasHighByte (s : String) : Bool := s.toList.any (fun c => c.val ≥ 0x80)

/-- Escape one char per Ruby String#inspect conventions. `next?` is the
    following character (for `#{`/`#$`/`#@` escaping). `binary` selects the
    ASCII-8BIT rendering, where a non-printable is a **byte** (`\xNN`, upper
    case) rather than a code point (`\uNNNN`) [V] — `(1.chr + 0xC3.chr).inspect`
    is `"\x01\xC3"` where `"\x01".inspect` (UTF-8) is `"\u0001"`. -/
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
    else if !unicodePrintable c then
      if c.toNat ≤ 0xffff then s!"\\u{hexOf 4}" else "\\u{" ++ hexOf 0 ++ "}"
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

/-- String equality including the encoding tag. CRuby compares bytes
    *and*, when either operand holds a non-ASCII byte, encodings: `"a".b == "a"`
    is true but `0xC8.chr == "È"` is **false** — same single byte 0xC8 in our
    payload, different encodings. Ignoring the tag here would be a silent wrong
    answer, which is why it is checked at the leaf both `==` and `eql?` share. -/
def strEqEnc (h : Heap) (x y : ObjId) (s t : String) : Bool :=
  s == t && ((h.get x).binary == (h.get y).binary || !hasHighByte s)

/-- How deep the pure representation functions follow nested values. They used
    to be `partial`, which made `==`, `eql?`, `inspect` and `to_s` opaque to every
    proof: not even `1 == 1` could be shown. They now recurse on this fuel, so they
    are ordinary total functions that unfold. No non-cyclic value a program can
    build in practice is this deep. -/
def reprFuel : Nat := 10000

/-- Strict `eql?` (type-strict: 1 ≠ 1.0). Used for hash-key matching.
    Out of fuel answers `true`, which is what CRuby's recursion guard answers
    when a comparison re-enters itself (`recursive_eql`). -/
def valueEqlFuel : Nat → Heap → Value → Value → Bool
  | 0, _, _, _ => true
  | fuel + 1, h, a, b =>
    match a, b with
    | .ref x, .ref y =>
      if x == y then true
      else
        match (h.get x).payload, (h.get y).payload with
        | .str s, .str t => strEqEnc h x y s t
        | .rational n d, .rational a b => n == a && d == b
        | .complex r i, .complex a b => valueEqlFuel fuel h r a && valueEqlFuel fuel h i b
        | .arr xs, .arr ys =>
          xs.size == ys.size && (xs.zip ys).all (fun (p, q) => valueEqlFuel fuel h p q)
        | .hsh xs, .hsh ys =>
          xs.size == ys.size &&
          xs.all (fun (k, v) =>
            match ys.find? (fun (k', _) => valueEqlFuel fuel h k k') with
            | some (_, v') => valueEqlFuel fuel h v v'
            | none => false)
        | _, _ => false
    | _, _ => a.identEq b

def valueEql (h : Heap) (a b : Value) : Bool := valueEqlFuel reprFuel h a b

/-- Loose `==` (numeric: 1 == 1.0). The builtin default; user overrides are
    gated by `reprPure`. Out of fuel answers `true`, as `valueEqlFuel` does. -/
def valueEqFuel : Nat → Heap → Value → Value → Bool
  | 0, _, _, _ => true
  | fuel + 1, h, a, b =>
    if let some (r, i) := complexPayload? h a then
      match complexPayload? h b with
      | some (x, y) => valueEqFuel fuel h r x && valueEqFuel fuel h i y
      | none => nativeReal h b && valueEqFuel fuel h r b && realZero h i
    else if let some (r, i) := complexPayload? h b then
      nativeReal h a && valueEqFuel fuel h r a && realZero h i
    else if let some (n, d) := rationalPayload? h a then rationalEq h n d b
    else if let some (n, d) := rationalPayload? h b then rationalEq h n d a
    else
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
          xs.size == ys.size && (xs.zip ys).all (fun (p, q) => valueEqFuel fuel h p q)
        | .hsh xs, .hsh ys =>
          xs.size == ys.size &&
          xs.all (fun (k, v) =>
            match ys.find? (fun (k', _) => valueEqlFuel fuel h k k') with
            | some (_, v') => valueEqFuel fuel h v v'
            | none => false)
        | _, _ => false
    | _, _ => a.identEq b

def valueEq (h : Heap) (a b : Value) : Bool := valueEqFuel reprFuel h a b

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
def inspectFuel : Nat → Heap → Value → Except String String
  | 0, _, _ => throw "inspect: value nested deeper than the model follows"
  | fuel + 1, h, v => do
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
        let parts ← xs.toList.mapM (inspectFuel fuel h)
        return "[" ++ String.intercalate ", " parts ++ "]"
      | .hsh xs =>
        if xs.isEmpty then return "{}"
        let parts ← xs.toList.mapM fun (k, val) => do
          let vs ← inspectFuel fuel h val
          match k with
          | .sym s =>
            if symbolIdentLike s then return s!"{s}: {vs}"
            else return s!"{escapeString s}: {vs}"
          | _ => return s!"{← inspectFuel fuel h k} => {vs}"
        return "{" ++ String.intercalate ", " parts ++ "}"
      | .cls _ =>
        -- an anonymous class/module (`Class.new`) has no name; CRuby renders it by
        -- address, which is `className`'s own fallback since L124 — one rule,
        -- not a copy per repr function
        return className h o
      | .exc msg =>
        let cname := className h (h.get o).klass
        let text ← if msg.identEq .nil then pure cname else toSFuel fuel h msg
        if text.isEmpty then return cname else return s!"#<{cname}: {text}>"
      | .proc _ => throw "Proc#inspect (address non-deterministic)"
      | .range lo hi excl =>
        -- A **nil endpoint prints as nothing** — `(1..nil).inspect` is `"1.."` and
        -- `(nil..2)` is `"..2"` — *except* when both are nil, which prints
        -- `"nil..nil"` [V]. `to_s` needs no such case: `nil.to_s` is already `""`,
        -- so it falls out, and `(nil..nil).to_s` really is `".."`. Found while
        -- validating endpoints: endless ranges were the one shape whose
        -- `inspect` the model got wrong rather than gated.
        let dots := if excl then "..." else ".."
        match lo, hi with
        | .nil, .nil => return "nil" ++ dots ++ "nil"
        | .nil, _ => return dots ++ (← inspectFuel fuel h hi)
        | _, .nil => return (← inspectFuel fuel h lo) ++ dots
        | _, _ => return (← inspectFuel fuel h lo) ++ dots ++ (← inspectFuel fuel h hi)
      | .rational n d => return s!"({n}/{d})"
      | .complex r i => complexText h true r i
      | .enumerator none => return s!"#<{className h (h.get o).klass}: uninitialized>"
      | .chain _ => throw "Chain inspection requires method dispatch"
      | .enumerator (some data) =>
        let receiver ← inspectFuel fuel h data.recv
        let (args, keywords) := if !data.kw.isEmpty then (data.args, data.kw) else
          match data.args.getLast? with
          | some (.ref a) => match (h.get a).payload with
            | .hsh pairs =>
              if !pairs.isEmpty && pairs.all (fun (k, _) => match k with | .sym _ => true | _ => false)
              then (data.args.dropLast, pairs.toList) else (data.args, [])
            | _ => (data.args, [])
          | _ => (data.args, [])
        let args ← args.mapM (inspectFuel fuel h)
        let kwParts ← keywords.mapM fun (key, value) => do
          match key with
          | .sym s =>
            let name := if symbolIdentLike s then s else escapeString s
            return s!"{name}: {← inspectFuel fuel h value}"
          | _ => throw "Enumerator inspect with non-Symbol keyword keys"
        let args := args ++ kwParts
        return "#<" ++ className h (h.get o).klass ++ ": " ++ receiver ++ ":" ++ data.method ++
          (if args.isEmpty then "" else "(" ++ String.intercalate ", " args ++ ")") ++ ">"
      | .regexp src opts => return regexpInspect src opts
      | .mdata subject caps names =>
        -- `#<MatchData "1.22" 1:"1" commit:nil>` — named groups print their name
        -- instead of their index, and an unset group prints `nil` [V].
        let whole := (spanText subject (caps[0]?.getD none)).getD ""
        -- the tag on a MatchData object records its *subject*'s encoding,
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
      | .none | .rng _ | .generator _ | .yielder .. =>
        let cname := className h (h.get o).klass
        let ivars := (h.get o).ivars.reverse
        if ivars.isEmpty then
          return s!"#<{cname}:{fakeAddr o}>"
        else
          let parts ← ivars.mapM fun (n, iv) => do return s!"{n}={← inspectFuel fuel h iv}"
          return s!"#<{cname}:{fakeAddr o} " ++ String.intercalate ", " parts ++ ">"

/-- Ruby `to_s` (default builtin). -/
def toSFuel : Nat → Heap → Value → Except String String
  | 0, _, _ => throw "toS: value nested deeper than the model follows"
  | fuel + 1, h, v => do
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
        --. ASCII bytes are the same either way.
        if (h.get o).binary && hasHighByte s then
          throw "to_s of a byte string holding a byte ≥ 0x80"
        else return s
      | .arr _ | .hsh _ => inspectFuel fuel h v
      | .cls _ => return className h o   -- as in `inspect` above
      | .exc msg => if msg.identEq .nil then return className h (h.get o).klass else toSFuel fuel h msg
      | .proc _ => throw "Proc#to_s (address non-deterministic)"
      | .range lo hi excl =>
        return (← toSFuel fuel h lo) ++ (if excl then "..." else "..") ++ (← toSFuel fuel h hi)
      | .rational n d => return s!"{n}/{d}"
      | .complex r i => complexText h false r i
      | .enumerator _ | .chain _ | .generator _ | .yielder .. => return s!"#<{className h (h.get o).klass}:{fakeAddr o}>"
      | .regexp src opts => return regexpToS src opts
      | .mdata subject caps _ =>
        let whole := (spanText subject (caps[0]?.getD none)).getD ""
        if (h.get o).binary && hasHighByte whole then
          throw "MatchData#to_s over a byte-string subject with a byte ≥ 0x80"
        else return whole
      | .none | .rng _ =>
        let cname := className h (h.get o).klass
        return s!"#<{cname}:{fakeAddr o}>"

end

/-- Ruby `inspect` (default builtin). Errors are Unsupported reasons. -/
def inspect (h : Heap) (v : Value) : Except String String := inspectFuel reprFuel h v

/-- Ruby `to_s` (default builtin). -/
def toS (h : Heap) (v : Value) : Except String String := toSFuel reprFuel h v

end RubyCore
