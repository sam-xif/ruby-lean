import RubyCore.Regex.Syntax

/-!
Ruby regex source → `Rx.Regex`. Total: every input either yields a `Regex` or a
`String` describing what it could not handle, which the caller turns into the
SUT contract's clean `Unsupported` gate — never a guessed pattern.

Recursive descent over `Array Char` with an explicit cursor, structurally
recursive on a fuel `Nat` seeded from the input length (D1: no `partial def`,
nothing on the path the kernel cannot reduce — cf. L73/L94). The grammar is the
usual three levels: alternation over concatenation over repetition-of-atom.

Flag handling is resolved here, not at match time (see `Syntax.lean`): `i` is
pushed onto the leaves it reaches, `x` drops whitespace and `#` comments, `m`
lands on `any`. `(?i:…)`, `(?x:…)` and `(?im-x:…)` therefore need no runtime
support at all — the flags only change how the enclosed source is parsed.
-/

namespace RubyCore

namespace Rx

/-- The three flags the parser tracks while descending. -/
structure Flags where
  ic : Bool := false
  ext : Bool := false
  dotAll : Bool := false
deriving Repr, Inhabited

/-- Parser state: the source, the cursor, and the next capture-group index. -/
structure PState where
  src : Array Char
  pos : Nat
  nextIdx : Nat
deriving Repr, Inhabited

abbrev PRes (α : Type) := Except String (α × PState)

namespace Parse

def peek (s : PState) : Option Char := s.src[s.pos]?

def peek2 (s : PState) : Option Char := s.src[s.pos + 1]?

def adv (s : PState) : PState := { s with pos := s.pos + 1 }

/-- Remaining input — the fuel every bounded helper is seeded with. -/
def rest (s : PState) : Nat := s.src.size + 1 - s.pos

def isSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' ||
  c == Char.ofNat 11 || c == Char.ofNat 12

/-- Drop to just past the next newline (an `x`-mode `#` comment). -/
def dropLine : Nat → PState → PState
  | 0, s => s
  | n + 1, s =>
    match peek s with
    | some c => if c == '\n' then adv s else dropLine n (adv s)
    | none => s

/-- Skip what the `x` flag makes insignificant. Only outside a bracket
    expression, which is Ruby's rule, so `clsBody` never calls this. -/
def skipX (f : Flags) : Nat → PState → PState
  | 0, s => s
  | n + 1, s =>
    if !f.ext then s
    else match peek s with
      | some c =>
        if isSpace c then skipX f n (adv s)
        else if c == '#' then skipX f n (dropLine (rest s) s)
        else s
      | none => s

/-- `\d`-family escapes, usable both inside and outside a bracket expression.
    Returns the family letter and whether it is the negated (upper-case) form. -/
def escClass? (c : Char) : Option (Char × Bool) :=
  if c == 'd' then some ('d', false)
  else if c == 'D' then some ('d', true)
  else if c == 'w' then some ('w', false)
  else if c == 'W' then some ('w', true)
  else if c == 's' then some ('s', false)
  else if c == 'S' then some ('s', true)
  else if c == 'h' then some ('h', false)
  else if c == 'H' then some ('h', true)
  else none

/-- The single-character escapes. Anything not listed escapes to itself, which
    is what `\.` `\/` `\+` … need. -/
def escChar (c : Char) : Char :=
  if c == 'n' then '\n'
  else if c == 't' then '\t'
  else if c == 'r' then '\r'
  else if c == 'f' then Char.ofNat 12
  else if c == 'v' then Char.ofNat 11
  else if c == 'a' then Char.ofNat 7
  else if c == 'e' then Char.ofNat 27
  else if c == '0' then Char.ofNat 0
  else c

/-- A hex digit's value. -/
def hexVal? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- `\u{XXXX}` (J54): the braced unicode escape, positioned just past the `u`.
    Returns the character and the state past the closing `}`; `none` if
    malformed (the caller reports the unsupported-escape error as before). The
    bare 4-digit `\uXXXX` form is also read. -/
def readUnicode (fuel : Nat) (s : PState) : Option (Char × PState) :=
  match peek s with
  | some '{' => go fuel (adv s) 0 false
  | _ =>
    -- bare `\uXXXX`: exactly four hex digits
    match peek s with
    | some c1 =>
      match hexVal? c1 with
      | none => none
      | some d1 =>
        match peek (adv s) with
        | none => none
        | some c2 =>
          match hexVal? c2 with
          | none => none
          | some d2 =>
            match peek (adv (adv s)) with
            | none => none
            | some c3 =>
              match hexVal? c3 with
              | none => none
              | some d3 =>
                match peek (adv (adv (adv s))) with
                | none => none
                | some c4 =>
                  match hexVal? c4 with
                  | none => none
                  | some d4 =>
                    let v := ((d1 * 16 + d2) * 16 + d3) * 16 + d4
                    if v.isValidChar then
                      some (Char.ofNat v, adv (adv (adv (adv s))))
                    else none
    | none => none
where
  go : Nat → PState → Nat → Bool → Option (Char × PState)
    | 0, _, _, _ => none
    | f + 1, s, acc, seen =>
      match peek s with
      | some '}' =>
        if seen then
          if acc.isValidChar then some (Char.ofNat acc, adv s) else none
        else none
      | some c =>
        match hexVal? c with
        | some d => go f (adv s) (acc * 16 + d) true
        | none => none
      | none => none

/-- Escapes we refuse rather than approximate. None occur in the slice. -/
def unsupportedEsc? (c : Char) : Option String :=
  if c == 'b' || c == 'B' then some "\\b / \\B word boundary"
  else if c == 'p' || c == 'P' then some "\\p{…} unicode property"
  else if c == 'x' then some "\\x hex escape"
  else if c == 'G' then some "\\G"
  else if c == 'k' then some "\\k<…> named backreference"
  else if c == 'c' || c == 'C' || c == 'M' then some "control/meta escape"
  else none

/-- Collect a run of decimal digits; `none` if there are none. -/
def readNat : Nat → PState → Nat → Bool → Option Nat × PState
  | 0, s, acc, seen => (if seen then some acc else none, s)
  | n + 1, s, acc, seen =>
    match peek s with
    | some c =>
      if c.isDigit then readNat n (adv s) (acc * 10 + (c.toNat - '0'.toNat)) true
      else (if seen then some acc else none, s)
    | none => (if seen then some acc else none, s)

/-- Turn off flags after a `-` in `(?im-x:…)`. -/
def flagsOff (f : Flags) : Nat → PState → Flags × PState
  | 0, s => (f, s)
  | n + 1, s =>
    match peek s with
    | some 'i' => flagsOff { f with ic := false } n (adv s)
    | some 'm' => flagsOff { f with dotAll := false } n (adv s)
    | some 'x' => flagsOff { f with ext := false } n (adv s)
    | _ => (f, s)

/-- `(?imx-imx…` flag letters. -/
def readFlagLetters (f : Flags) : Nat → PState → Flags × PState
  | 0, s => (f, s)
  | n + 1, s =>
    match peek s with
    | some 'i' => readFlagLetters { f with ic := true } n (adv s)
    | some 'm' => readFlagLetters { f with dotAll := true } n (adv s)
    | some 'x' => readFlagLetters { f with ext := true } n (adv s)
    | some '-' => flagsOff f n (adv s)
    | _ => (f, s)

/-- A `(?<name>` group name, cursor just past the `<`. -/
def readName : Nat → PState → List Char → Except String (String × PState)
  | 0, _, _ => .error "regex: unterminated group name"
  | n + 1, s, acc =>
    match peek s with
    | some '>' => .ok (String.mk acc.reverse, adv s)
    | some c => readName n (adv s) (c :: acc)
    | none => .error "regex: unterminated group name"

/-- The body of `[ … ]`, cursor just past `[` (and past `^`/leading `]`). -/
def clsBody : Nat → PState → List ClsItem → PRes CharClass
  | 0, _, _ => .error "regex: bracket expression too long"
  | n + 1, s, acc =>
    match peek s with
    | none => .error "regex: unterminated ["
    | some ']' => .ok ({ neg := false, items := acc.reverse }, adv s)
    | some '[' =>
      if peek2 s == some ':' then .error "regex: POSIX bracket class [[:…:]]"
      else clsBody n (adv s) (.ch '[' :: acc)
    | some '\\' =>
      match peek2 s with
      | none => .error "regex: trailing backslash in bracket expression"
      | some e =>
        match unsupportedEsc? e with
        | some why => .error s!"regex: {why}"
        | none =>
          let s := adv (adv s)
          match escClass? e with
          | some (k, ng) => clsBody n s (.esc k ng :: acc)
          | none => clsRange n s (escChar e) acc
    | some c => clsRange n (adv s) c acc
where
  /-- Having read a low character, decide between `a-z` and a bare `a`. A `-`
      that is last before `]`, or is followed by an escape, is a literal `-`. -/
  clsRange (n : Nat) (s : PState) (c : Char) (acc : List ClsItem) : PRes CharClass :=
    if peek s == some '-' then
      match peek2 s with
      | some ']' | none => clsBody n s (.ch c :: acc)
      | some '\\' => clsBody n s (.ch c :: acc)
      | some hi => clsBody n (adv (adv s)) (.range c hi :: acc)
    else clsBody n s (.ch c :: acc)

/-- Parse `[ … ]`; the cursor is *on* the `[`. -/
def parseClass (s : PState) : PRes CharClass :=
  let s := adv s
  let (neg, s) := if peek s == some '^' then (true, adv s) else (false, s)
  -- a `]` immediately after `[` or `[^` is a literal `]`
  let (lead, s) := if peek s == some ']' then ([ClsItem.ch ']'], adv s) else ([], s)
  match clsBody (rest s) s [] with
  | .error e => .error e
  | .ok (cc, s) => .ok ({ neg := neg, items := lead ++ cc.items }, s)

/-- Attach a quantifier to an atom, then look for the lazy `?` / possessive `+`
    suffix. Possessive is refused rather than silently treated as greedy. -/
def quant (a : Regex) (s : PState) (lo : Nat) (hi : Option Nat) : PRes Regex :=
  match peek s with
  | some '?' => .ok (.rep a lo hi false, adv s)
  | some '+' => .error "regex: possessive quantifier"
  | _ => .ok (.rep a lo hi true, s)

def expectClose (s : PState) : Except String PState :=
  if peek s == some ')' then .ok (adv s) else .error "regex: unbalanced ("

mutual

/-- `alt := cat ('|' cat)*` -/
def pAlt (f : Flags) : Nat → PState → PRes Regex
  | 0, _ => .error "regex: nesting too deep"
  | n + 1, s =>
    match pCat f n s with
    | .error e => .error e
    | .ok (r, s) =>
      let s := skipX f (rest s) s
      if peek s == some '|' then
        match pAlt f n (adv s) with
        | .error e => .error e
        | .ok (r₂, s) => .ok (.alt r r₂, s)
      else .ok (r, s)

/-- `cat := rep*`, stopping at `|`, `)`, or end of input. -/
def pCat (f : Flags) : Nat → PState → PRes Regex
  | 0, _ => .error "regex: nesting too deep"
  | n + 1, s =>
    let s := skipX f (rest s) s
    match peek s with
    | none => .ok (.empty, s)
    | some '|' => .ok (.empty, s)
    | some ')' => .ok (.empty, s)
    | _ =>
      match pRep f n s with
      | .error e => .error e
      | .ok (r, s₁) =>
        match pCat f n s₁ with
        | .error e => .error e
        | .ok (r₂, s₂) => .ok (match r₂ with | .empty => r | _ => .cat r r₂, s₂)

/-- `rep := atom quantifier?` -/
def pRep (f : Flags) : Nat → PState → PRes Regex
  | 0, _ => .error "regex: nesting too deep"
  | n + 1, s =>
    match pAtom f n s with
    | .error e => .error e
    | .ok (a, s) =>
      let s := skipX f (rest s) s
      match peek s with
      | some '*' => quant a (adv s) 0 none
      | some '+' => quant a (adv s) 1 none
      | some '?' => quant a (adv s) 0 (some 1)
      | some '{' =>
        -- `{n}` / `{n,}` / `{n,m}` / `{,m}`; anything else leaves `{` literal
        let s₁ := adv s
        let (lo?, s₂) := readNat (rest s₁) s₁ 0 false
        match peek s₂ with
        | some '}' =>
          match lo? with
          | some k => quant a (adv s₂) k (some k)
          | none => .ok (a, s)
        | some ',' =>
          let s₃ := adv s₂
          let (hi?, s₄) := readNat (rest s₃) s₃ 0 false
          match peek s₄ with
          | some '}' => quant a (adv s₄) (lo?.getD 0) hi?
          | _ => .ok (a, s)
        | _ => .ok (a, s)
      | _ => .ok (a, s)

/-- A single atom: a group, a bracket expression, `.`, an anchor, an escape, or
    a literal character. -/
def pAtom (f : Flags) : Nat → PState → PRes Regex
  | 0, _ => .error "regex: nesting too deep"
  | n + 1, s =>
    let s := skipX f (rest s) s
    match peek s with
    | none => .ok (.empty, s)
    | some '(' => pGroup f n s
    | some '[' =>
      match parseClass s with
      | .error e => .error e
      | .ok (cc, s) => .ok (.cls cc f.ic, s)
    | some '.' => .ok (.any f.dotAll, adv s)
    | some '^' => .ok (.anchor .lineStart, adv s)
    | some '$' => .ok (.anchor .lineEnd, adv s)
    | some '*' => .error "regex: quantifier with nothing to repeat"
    | some '+' => .error "regex: quantifier with nothing to repeat"
    | some '?' => .error "regex: quantifier with nothing to repeat"
    | some '\\' =>
      match peek2 s with
      | none => .error "regex: trailing backslash"
      | some e =>
        let s' := adv (adv s)
        if e == 'A' then .ok (.anchor .bos, s')
        else if e == 'z' then .ok (.anchor .eos, s')
        else if e == 'Z' then .ok (.anchor .eosNl, s')
        else match unsupportedEsc? e with
          | some why => .error s!"regex: {why}"
          | none =>
            match escClass? e with
            | some (k, ng) => .ok (.cls { neg := false, items := [.esc k ng] } f.ic, s')
            | none =>
              if e.isDigit && e != '0' then .ok (.backref (e.toNat - '0'.toNat), s')
              else .ok (.lit (escChar e) f.ic, s')
    | some c => .ok (.lit c f.ic, adv s)

/-- `(` … `)` in every form the slice uses. -/
def pGroup (f : Flags) : Nat → PState → PRes Regex
  | 0, _ => .error "regex: nesting too deep"
  | n + 1, s₀ =>
    let s := adv s₀
    if peek s == some '?' then
      let s := adv s
      match peek s with
      | some ':' => wrapGroup (pAlt f n (adv s)) (fun r => .group none none r)
      | some '=' => wrapGroup (pAlt f n (adv s)) (fun r => .look false r)
      | some '!' => wrapGroup (pAlt f n (adv s)) (fun r => .look true r)
      | some '>' => .error "regex: atomic group (?>…)"
      | some '#' => .error "regex: (?#…) comment group"
      | some '\'' => .error "regex: (?'name'…) group"
      | some '<' =>
        match peek2 s with
        | some '=' => .error "regex: lookbehind (?<=…)"
        | some '!' => .error "regex: negative lookbehind (?<!…)"
        | _ =>
          match readName (rest s) (adv s) [] with
          | .error e => .error e
          | .ok (nm, s) =>
            let idx := s.nextIdx
            wrapGroup (pAlt f n { s with nextIdx := idx + 1 })
              (fun r => .group (some idx) (some nm) r)
      | _ =>
        let (f', s) := readFlagLetters f (rest s) s
        match peek s with
        | some ':' => wrapGroup (pAlt f' n (adv s)) (fun r => .group none none r)
        | some ')' =>
          -- a bare `(?i)` switches flags for the rest of the enclosing group
          pAlt f' n (adv s)
        | _ => .error "regex: malformed (?…) group"
    else
      let idx := s.nextIdx
      wrapGroup (pAlt f n { s with nextIdx := idx + 1 })
        (fun r => .group (some idx) none r)
where
  wrapGroup (res : PRes Regex) (mk : Regex → Regex) : PRes Regex :=
    match res with
    | .error e => .error e
    | .ok (r, s) =>
      match expectClose s with
      | .error e => .error e
      | .ok s => .ok (mk r, s)

end

/-- Parse a Ruby regex source under an option word (`Regexp::IGNORECASE` 1,
    `EXTENDED` 2, `MULTILINE` 4, `NOENCODING` 32 — the last does not affect the
    matcher and is accepted and ignored). -/
def parse (src : String) (opts : Nat) : Except String Regex :=
  let f : Flags :=
    { ic := opts % 2 == 1, ext := (opts / 2) % 2 == 1, dotAll := (opts / 4) % 2 == 1 }
  let arr := src.toList.toArray
  let s : PState := { src := arr, pos := 0, nextIdx := 1 }
  match pAlt f (arr.size * 3 + 16) s with
  | .error e => .error e
  | .ok (r, s') =>
    if s'.pos ≥ arr.size then .ok r
    else if peek s' == some ')' then .error "regex: unbalanced )"
    else .error s!"regex: unconsumed input at {s'.pos}"

end Parse

export Parse (parse)

end Rx

end RubyCore
