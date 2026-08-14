import RubyCore.Builtins.Collections

/-!
String, Symbol and Proc rules.

Split out of the single `Builtins.run` match (L98), one class group per file, no
behaviour change: each rule file matches its own bids and hands anything it does
not recognise to the next file in the chain.
-/

namespace RubyCore

namespace Builtins

/-- `String#to_f`'s lenient prefix parse: whitespace, sign, digits with `_`
    separators, an optional fraction, an optional exponent; stop at the first
    character that does not fit, and answer `0.0` on no match at all [V]. -/
def parseFloatPrefix (str : String) : Float :=
  let cs := str.toList.dropWhile fun c =>
    c == ' ' || c == '\t' || c == '\n' || c == '\r'
  let (neg, cs) := match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  -- digits, allowing `_` strictly between digits
  let rec digits : List Char → List Char → List Char × List Char
    | acc, d :: r =>
      if d.isDigit then digits (d :: acc) r
      else if d == '_' && !acc.isEmpty then
        match r with
        | e :: r' => if e.isDigit then digits (e :: acc) r' else (acc.reverse, d :: r)
        | [] => (acc.reverse, d :: r)
      else (acc.reverse, d :: r)
    | acc, [] => (acc.reverse, [])
  let (intPart, rest) := digits [] cs
  if intPart.isEmpty then 0.0 else
  let toNatOf : List Char → Nat := fun ds =>
    ds.foldl (fun a c => a * 10 + (c.toNat - '0'.toNat)) 0
  let whole := Float.ofNat (toNatOf intPart)
  let (frac, rest) := match rest with
    | '.' :: r =>
      let (fs, r') := digits [] r
      if fs.isEmpty then (0.0, '.' :: r)
      else (Float.ofNat (toNatOf fs) / Float.ofNat (10 ^ fs.length), r')
    | r => (0.0, r)
  let mant := whole + frac
  let expo : Int := match rest with
    | e :: r =>
      if e == 'e' || e == 'E' then
        let (esign, r) := match r with
          | '-' :: r' => (true, r')
          | '+' :: r' => (false, r')
          | r' => (false, r')
        let (es, _) := digits [] r
        if es.isEmpty then 0 else (if esign then -(toNatOf es : Int) else (toNatOf es : Int))
      else 0
    | [] => 0
  let scaled :=
    if expo == 0 then mant
    else if expo > 0 then mant * Float.ofNat (10 ^ expo.toNat)
    else mant / Float.ofNat (10 ^ (-expo).toNat)
  if neg then -scaled else scaled

/-- String, Symbol and Proc rules. -/
def runStrings (bid : String) (recv : Value) (args : List Value) (m : Machine) : BRes :=
  let h := m.heap
  match bid with
  /- ─── String ─── -/
  | "String#+" =>
    binArg m args fun b =>
      match strPayload? h recv, strPayload? h b with
      | some s, some t =>
        match concatEnc h recv s b t with
        | .ok bin => okStrEnc m bin (s ++ t)
        | .error e => .unsupported e
      | some _, none => .err Boot.typeErrorId
          s!"no implicit conversion of {coerceName h b} into String" m
      | _, _ => .unsupported "String#+"
  | "String#*" =>
    binArg m args fun b =>
      match strPayload? h recv, b with
      | some s, .int n =>
        if n < 0 then .err Boot.argumentErrorId "negative argument" m
        else okStrFrom m recv (String.join (List.replicate n.toNat s))
      | _, _ => .unsupported "String#*"
  | "String#==" | "String#eql?" =>
    -- `valueEql`, not a bare payload compare: equality consults the encoding tag
    -- when a non-ASCII byte is in play (L118), and both `==` and `eql?` do.
    binArg m args fun b =>
      match strPayload? h recv, strPayload? h b with
      | some _, some _ => .ok (.bool (valueEql h recv b)) m
      | _, _ => .ok (.bool false) m
  | "String#!=" =>
    binArg m args fun b => .ok (.bool (!(valueEq h recv b))) m
  | "String#<" | "String#>" | "String#<=" | "String#>=" =>
    binArg m args fun b =>
      match strPayload? h recv, strPayload? h b with
      | some s, some t =>
        let o := strCompare s t
        let r := match bid with
          | "String#<" => o == .lt
          | "String#>" => o == .gt
          | "String#<=" => o != .gt
          | _ => o != .lt
        .ok (.bool r) m
      | some _, none =>
        -- Comparable message follows the coerceDesc rule [V]: special
        -- constants by inspect ("with 1", "with :k"), else class name
        -- ("with Array")
        .err Boot.argumentErrorId
          s!"comparison of String with {coerceDesc h b} failed" m
      | _, _ => .unsupported "String comparison"
  | "String#<=>" =>
    binArg m args fun b =>
      match strPayload? h recv, strPayload? h b with
      | some s, some t => .ok (ordValue (strCompare s t)) m
      | _, _ => .ok .nil m
  | "String#length" | "String#size" =>
    match strPayload? h recv with
    | some s => .ok (.int s.length) m  -- character count (UTF-8-aware) [D]
    | none => .unsupported "length"
  | "String#to_s" | "String#to_str" => .ok recv m
  | "String#to_f" =>
    -- As lenient as `to_i`: leading whitespace, optional sign, digits with `_`
    -- separators, an optional fraction and an optional exponent, and stop at the
    -- first character that does not fit. No match at all is `0.0` [V].
    match strPayload? h recv with
    | none => .unsupported "String#to_f on a non-String"
    | some str => .ok (.flt (parseFloatPrefix str)) m
  | "String#__binary?" =>
    .ok (.bool (isBinaryStr h recv)) m
  | "String#__bytes" =>
    -- The UTF-8 bytes of the receiver — already one per character when it is
    -- binary, encoded when it is not.
    match strPayload? h recv with
    | none => .unsupported "String#bytes on a non-String"
    | some str =>
      let bs : List Nat :=
        if isBinaryStr h recv then str.toList.map (·.toNat)
        else str.toUTF8.toList.map (·.toNat)
      let (v, m) := allocArr m (bs.map (fun b => Value.int (Int.ofNat b))).toArray
      .ok v m
  | "String#__as_binary" =>
    -- Reinterpret as bytes: one character per UTF-8 byte (L117).
    match strPayload? h recv with
    | none => .unsupported "String#b on a non-String"
    | some str =>
      if isBinaryStr h recv then .ok recv m
      else
        let bytes := str.toUTF8.toList.map (fun b => Char.ofNat b.toNat)
        let (v, m) := allocStrEnc m (String.mk bytes) true
        .ok v m
  | "String#__as_utf8" =>
    -- Re-decode the byte characters as UTF-8. An **invalid** sequence cannot be
    -- represented — a Lean `String` holds Unicode scalars, not bytes — so it
    -- gates rather than producing a different string (L117).
    match strPayload? h recv with
    | none => .unsupported "String#force_encoding on a non-String"
    | some str =>
      if !isBinaryStr h recv then .ok recv m
      else
        let bytes := ByteArray.mk (str.toList.map (fun c => UInt8.ofNat c.toNat)).toArray
        match String.fromUTF8? bytes with
        | some decoded => let (v, m) := allocStr m decoded; .ok v m
        | none =>
          .unsupported "force_encoding to UTF-8 of an invalid byte sequence (L117)"
  | "String#__force_binary" | "String#__force_utf8" =>
    -- `force_encoding` **mutates and returns the receiver** [V], so it cannot be
    -- `__as_binary`/`__as_utf8` (which copy, as `b` needs). Retagging also
    -- rewrites the payload — going to binary splits each scalar into its UTF-8
    -- bytes and coming back reassembles them — so both fields move together, on
    -- the same object (L118).
    match recv, strPayload? h recv with
    | .ref o, some str =>
      if (h.get o).frozen then
        match inspectP m recv with
        | .ok r => .err Boot.frozenErrorId s!"can't modify frozen String: {r}" m
        | .error e => .unsupported e
      else
        let toBinary := bid == "String#__force_binary"
        if (h.get o).binary == toBinary then .ok recv m
        else if toBinary then
          let bytes := str.toUTF8.toList.map (fun b => Char.ofNat b.toNat)
          let o' := { h.get o with payload := Payload.str (String.mk bytes), binary := true }
          .ok recv { m with heap := h.set o o' }
        else
          let bytes := ByteArray.mk (str.toList.map (fun c => UInt8.ofNat c.toNat)).toArray
          match String.fromUTF8? bytes with
          | some decoded =>
            let o' := { h.get o with payload := Payload.str decoded, binary := false }
            .ok recv { m with heap := h.set o o' }
          | none =>
            .unsupported "force_encoding to UTF-8 of an invalid byte sequence (L117)"
    | _, _ => .unsupported "String#force_encoding on a non-String"
  | "String#ord" =>
    match strPayload? h recv with
    | some str =>
      match str.toList with
      | c :: _ => .ok (.int c.toNat) m
      | [] => .err Boot.argumentErrorId "empty string" m
    | none => .unsupported "String#ord on a non-String"
  | "String#chars" =>
    match strPayload? h recv with
    | some str =>
      let bin := isBinaryStr h recv
      let (vs, m) := str.toList.foldl (fun (acc, m) c =>
        let (v, m) := allocStrEnc m (String.singleton c) bin; (acc.push v, m)) (#[], m)
      let (v, m) := allocArr m vs
      .ok v m
    | none => .unsupported "String#chars on a non-String"
  | "String#to_i" =>
    -- CRuby's `to_i` is lenient by design: skip leading whitespace, take an
    -- optional sign, then digits (with `_` allowed *between* digits), and stop
    -- at the first character that does not fit. No match at all is `0`, not an
    -- error — which is why `"nope".to_i` is `0` and not a `TypeError` [V].
    match strPayload? h recv with
    | none => .unsupported "String#to_i on a non-String"
    | some str =>
      let cs := str.toList.dropWhile (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r')
      let (neg, cs) := match cs with
        | '-' :: r => (true, r)
        | '+' :: r => (false, r)
        | r => (false, r)
      -- `_` is a separator only *between* digits: `"1_0"` is 10, but `"_5"` is
      -- 0 and `"1__0"` is 1 [V]. So this is a small scan, not a filter.
      let rec grab : List Char → List Char → List Char
        | acc, d :: r => if d.isDigit then grab (d :: acc) r
                         else if d == '_' then
                           match r with
                           | e :: r' => if e.isDigit && !acc.isEmpty then grab (e :: acc) r' else acc.reverse
                           | [] => acc.reverse
                         else acc.reverse
        | acc, [] => acc.reverse
      let digits := grab [] cs
      let n : Int := digits.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) (0 : Int)
      .ok (.int (if neg then -n else n)) m
  | "String#inspect" =>
    -- the *result* is UTF-8 whatever the receiver was [V] — escaping makes it
    -- pure ASCII — but the escaping itself is tag-sensitive (L118)
    match strPayload? h recv with
    | some s => okStr m (escapeStringEnc (isBinaryStr h recv) s)
    | none => .unsupported "inspect"
  | "String#<<" | "String#concat" =>
    binArg m args fun b =>
      match recv, strPayload? h recv, strPayload? h b with
      | .ref o, some s, some t =>
        if (h.get o).frozen then
          match inspectP m recv with
          | .ok r => .err Boot.frozenErrorId s!"can't modify frozen String: {r}" m
          | .error e => .unsupported e
        else
          -- appending *widens* the receiver in place: `(+"x") << "café".b` is
          -- ASCII-8BIT afterwards [V], by the same compatibility rule as `+`
          match concatEnc h recv s b t with
          | .error e => .unsupported e
          | .ok bin =>
            let o' := { h.get o with payload := Payload.str (s ++ t), binary := bin }
            .ok recv { m with heap := h.set o o' }
      | _, some _, none => .unsupported "String#<< non-string (codepoint append)"
      | _, _, _ => .unsupported "<<"
  | "String#empty?" =>
    match strPayload? h recv with
    | some s => .ok (.bool s.isEmpty) m
    | none => .unsupported "empty?"
  | "String#include?" =>
    binArg m args fun b =>
      match strPayload? h recv, strPayload? h b with
      | some s, some t => .ok (.bool (t.isEmpty || (s.splitOn t).length > 1)) m
      | some _, none => .err Boot.typeErrorId
          s!"no implicit conversion of {coerceName h b} into String" m
      | _, _ => .unsupported "include?"
  | "String#reverse" =>
    match strPayload? h recv with
    | some s => okStrFrom m recv (String.ofList s.toList.reverse)
    | none => .unsupported "reverse"
  | "String#upcase" =>
    match strPayload? h recv with
    | some s => okStrFrom m recv s.toUpper
    | none => .unsupported "upcase"
  | "String#downcase" =>
    match strPayload? h recv with
    | some s => okStrFrom m recv s.toLower
    | none => .unsupported "downcase"
  | "String#strip" =>
    match strPayload? h recv with
    | some s => okStrFrom m recv s.trimAscii.toString
    | none => .unsupported "strip"
  | "String#chomp" =>
    match strPayload? h recv, args with
    | some s, [] =>
      let s := if s.endsWith "\r\n" then (s.dropEnd 2).toString
               else if s.endsWith "\n" || s.endsWith "\r" then (s.dropEnd 1).toString
               else s
      okStrFrom m recv s
    | some s, [a] =>
      match strPayload? h a with
      | none => .unsupported "chomp with a non-String argument"
      | some suf =>
        -- `chomp("")` strips **all** trailing newlines, not one [V]; any other
        -- suffix is removed once if present.
        if suf.isEmpty then
          let rec strip : Nat → String → String
            | 0, t => t
            | n + 1, t =>
              if t.endsWith "\r\n" then strip n (t.dropEnd 2).toString
              else if t.endsWith "\n" || t.endsWith "\r" then strip n (t.dropEnd 1).toString
              else t
          okStrFrom m recv (strip (s.length + 1) s)
        else if s.endsWith suf then okStrFrom m recv (s.dropEnd suf.length).toString
        else okStrFrom m recv s
    | _, _ => .unsupported "chomp arity"
  | "String#start_with?" =>
    binArg m args fun b =>
      match strPayload? h recv, strPayload? h b with
      | some s, some t => .ok (.bool (s.startsWith t)) m
      | _, _ => .unsupported "start_with?"
  | "String#end_with?" =>
    binArg m args fun b =>
      match strPayload? h recv, strPayload? h b with
      | some s, some t => .ok (.bool (s.endsWith t)) m
      | _, _ => .unsupported "end_with?"
  | "String#frozen?" =>
    match recv with
    | .ref o => .ok (.bool (h.get o).frozen) m
    | _ => .unsupported "frozen?"
  | "String#+@" =>
    -- `+str`: an unfrozen String. CRuby 4.0.5 returns a *fresh* object even when
    -- the receiver is already unfrozen (`(+a).equal?(a)` is false [V], unlike what
    -- the 3.x docs describe), so always copy.
    match recv with
    | .ref o => let (v, m) := dupObj m o false; .ok v m
    | _ => .unsupported "+@ on a non-String"
  | "String#-@" =>
    -- `-str`: a frozen (deduplicated) string; sharing is unobservable here [V]
    match recv with
    | .ref o =>
      if (h.get o).frozen then .ok recv m
      else
        let (v, m) := dupObj m o false
        match v with
        | .ref o2 =>
          .ok v { m with heap := m.heap.set o2 { m.heap.get o2 with frozen := true } }
        | _ => .unsupported "-@"
    | _ => .unsupported "-@ on a non-String"
  | "String#to_sym" =>
    match strPayload? h recv with
    -- a Symbol in the model carries no encoding, so a byte string only interns
    -- while its bytes are ASCII (L118)
    | some s =>
      if isBinaryStr h recv && hasHighByte s then
        .unsupported "String#to_sym of a byte string holding a byte ≥ 0x80 (L118)"
      else .ok (.sym s) m
    | none => .unsupported "to_sym"
  | "String#[]" =>
    match strPayload? h recv, args with
    | some s, [.int i] =>
      let cs := s.toList
      let idx := if i < 0 then i + cs.length else i
      if idx < 0 || idx ≥ cs.length then .ok .nil m
      else okStrFrom m recv (String.singleton cs[idx.toNat]!)
    | some str, [.int start, .int len] =>
      let cs := str.toList
      match sliceRange cs.length start len with
      | none => .ok .nil m
      | some (off, count) => okStrFrom m recv (String.ofList ((cs.drop off).take count))
    | some str, [.ref ro] =>
      match (h.get ro).payload with
      | .range lo hi excl =>
        let cs := str.toList
        let n : Int := cs.length
        let st? : Option Int := match lo with
          | .nil => some 0
          | .int i => some (if i < 0 then i + n else i)
          | _ => none
        let last? : Option Int := match hi with
          | .nil => some (n - 1)
          | .int i => let e := if i < 0 then i + n else i; some (if excl then e - 1 else e)
          | _ => none
        match st?, last? with
        | some st, some lastRaw =>
          if st < 0 || st > n then .ok .nil m
          else
            let lastI := min lastRaw (n - 1)
            let count := if lastI < st then 0 else (lastI - st + 1).toNat
            okStrFrom m recv (String.ofList ((cs.drop st.toNat).take count))
        | _, _ => .unsupported "String#[] non-Integer range endpoint"
      -- `s["sub"]` → the substring if present, else nil [V]
      | .str sub =>
        if sub.isEmpty || (str.splitOn sub).length > 1 then okStrFrom m recv sub else .ok .nil m
      -- `s[/re/]` → the whole match, or nil [V]. Sets `$~` like any match.
      | .regexp src opts =>
        match runSearch src opts str with
        | .gate why => .unsupported why
        | .miss => .ok .nil (setMatchGlobals m none)
        | .hit a b caps names =>
          let (md, m) := allocMData m str caps names (isBinaryStr h recv)
          okStrFrom (setMatchGlobals m (some md)) recv (charSlice str a b)
      | _ => .unsupported "String#[] non-index argument"
    -- `s[/re/, n]` / `s[/re/, "name"]` → that capture, or nil [V].
    | some str, [.ref ro, sel] =>
      match (h.get ro).payload with
      | .regexp src opts =>
        match runSearch src opts str with
        | .gate why => .unsupported why
        | .miss => .ok .nil (setMatchGlobals m none)
        | .hit _ _ caps names =>
          let (md, m) := allocMData m str caps names (isBinaryStr h recv)
          let m := setMatchGlobals m (some md)
          match runRegex "MatchData#[]" md [sel] m with
          | .ok v m => .ok v m
          | other => other
      | _ => .unsupported "String#[] index form"
    | some _, _ => .unsupported "String#[] index form"
    | _, _ => .unsupported "[]"
  /- ─── Symbol ─── -/
  | "Symbol#to_s" =>
    match recv with | .sym s => okStr m s | _ => .unsupported "to_s"
  | "Symbol#inspect" =>
    match recv with | .sym s => okStr m (symInspect s) | _ => .unsupported "inspect"
  | "Symbol#==" =>
    binArg m args fun b => .ok (.bool (recv.identEq b)) m
  | "Symbol#to_sym" => .ok recv m
  | "Symbol#to_proc" =>
    match recv with
    | .sym s =>
      -- `:m.to_proc` ≈ `->(x, *a){ x.m(*a) }` — lambda-like (no auto-splat).
      let cl : Closure :=
        { params := [.req "__recv", .rest (some "__rest")], locals := [],
          body := .send (some (.var .lvar "__recv")) s
                    [.splat (some (.var .lvar "__rest"))] none,
          captured := 0, home := 0, lam := true }
      let (o, h) := m.heap.alloc { klass := Boot.procId, payload := .proc cl }
      .ok (.ref o) { m with heap := h }
    | _ => .unsupported "to_proc"
  /- ─── Proc ─── -/
  | "Proc#lambda?" =>
    match recv with
    | .ref o => match (h.get o).payload with
      | .proc c => .ok (.bool c.lam) m
      | _ => .unsupported "lambda?"
    | _ => .unsupported "lambda?"
  | "Proc#to_proc" => .ok recv m
  | _ => runCollections bid recv args m

end Builtins

end RubyCore
