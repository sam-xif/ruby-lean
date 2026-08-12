import RubyCore.Builtins.Collections

/-!
String, Symbol and Proc rules.

Split out of the single `Builtins.run` match (L98), one class group per file, no
behaviour change: each rule file matches its own bids and hands anything it does
not recognise to the next file in the chain.
-/

namespace RubyCore

namespace Builtins

/-- String, Symbol and Proc rules. -/
def runStrings (bid : String) (recv : Value) (args : List Value) (m : Machine) : BRes :=
  let h := m.heap
  match bid with
  /- ─── String ─── -/
  | "String#+" =>
    binArg m args fun b =>
      match strPayload? h recv, strPayload? h b with
      | some s, some t => okStr m (s ++ t)
      | some _, none => .err Boot.typeErrorId
          s!"no implicit conversion of {coerceName h b} into String" m
      | _, _ => .unsupported "String#+"
  | "String#*" =>
    binArg m args fun b =>
      match strPayload? h recv, b with
      | some s, .int n =>
        if n < 0 then .err Boot.argumentErrorId "negative argument" m
        else okStr m (String.join (List.replicate n.toNat s))
      | _, _ => .unsupported "String#*"
  | "String#==" | "String#eql?" =>
    binArg m args fun b =>
      match strPayload? h recv, strPayload? h b with
      | some s, some t => .ok (.bool (s == t)) m
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
      let (vs, m) := str.toList.foldl (fun (acc, m) c =>
        let (v, m) := allocStr m (String.singleton c); (acc.push v, m)) (#[], m)
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
    match strPayload? h recv with
    | some s => okStr m (escapeString s)
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
          .ok recv { m with heap := h.set o { h.get o with payload := .str (s ++ t) } }
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
    | some s => okStr m (String.ofList s.toList.reverse)
    | none => .unsupported "reverse"
  | "String#upcase" =>
    match strPayload? h recv with
    | some s => okStr m s.toUpper
    | none => .unsupported "upcase"
  | "String#downcase" =>
    match strPayload? h recv with
    | some s => okStr m s.toLower
    | none => .unsupported "downcase"
  | "String#strip" =>
    match strPayload? h recv with
    | some s => okStr m s.trimAscii.toString
    | none => .unsupported "strip"
  | "String#chomp" =>
    match strPayload? h recv, args with
    | some s, [] =>
      let s := if s.endsWith "\r\n" then (s.dropEnd 2).toString
               else if s.endsWith "\n" || s.endsWith "\r" then (s.dropEnd 1).toString
               else s
      okStr m s
    | _, _ => .unsupported "chomp with arg"
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
    | some s => .ok (.sym s) m
    | none => .unsupported "to_sym"
  | "String#[]" =>
    match strPayload? h recv, args with
    | some s, [.int i] =>
      let cs := s.toList
      let idx := if i < 0 then i + cs.length else i
      if idx < 0 || idx ≥ cs.length then .ok .nil m
      else okStr m (String.singleton cs[idx.toNat]!)
    | some str, [.int start, .int len] =>
      let cs := str.toList
      match sliceRange cs.length start len with
      | none => .ok .nil m
      | some (off, count) => okStr m (String.ofList ((cs.drop off).take count))
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
            okStr m (String.ofList ((cs.drop st.toNat).take count))
        | _, _ => .unsupported "String#[] non-Integer range endpoint"
      -- `s["sub"]` → the substring if present, else nil [V]
      | .str sub =>
        if sub.isEmpty || (str.splitOn sub).length > 1 then okStr m sub else .ok .nil m
      | _ => .unsupported "String#[] non-index argument"
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
