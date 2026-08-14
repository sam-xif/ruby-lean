import RubyCore.Builtins.Support
import RubyCore.Regex.Parse
import RubyCore.Regex.Match

/-!
The Ruby-visible regex surface: `Regexp`, `MatchData`, and the `String` methods
that take a pattern (W2a `Api.lean`).

Everything here funnels through one helper, `runSearch`, so there is exactly one
place where a pattern is parsed and matched and exactly one place where the
engine's three outcomes are mapped onto Ruby's two:

* parse failure → `Unsupported` with the parser's reason (never a guessed
  pattern, never a `RegexpError` we invented);
* `oof` → `Unsupported "regex bound exhausted"` (never "no match");
* `no` / `yes` → `nil` / a `MatchData`.

A `Regexp` object stores its *source and options*, not a compiled `Rx.Regex`, so
each use re-parses. That keeps `Payload` a plain data type and costs a linear
pass over a pattern that is, in this corpus, tens of characters long.
-/

namespace RubyCore

namespace Builtins

open RubyCore.Rx

/-- The pattern behind a value, if it is a `Regexp`. -/
def regexpParts? (h : Heap) : Value → Option (String × Nat)
  | .ref o => match (h.get o).payload with
    | .regexp src opts => some (src, opts)
    | _ => none
  | _ => none

/-- The `MatchData` behind a value. -/
def mdataParts? (h : Heap) :
    Value → Option (String × Array (Option (Nat × Nat)) × List (String × Nat))
  | .ref o => match (h.get o).payload with
    | .mdata s c n => some (s, c, n)
    | _ => none
  | _ => none

def allocRegexp (m : Machine) (src : String) (opts : Nat) : Value × Machine :=
  let (o, h) := m.heap.alloc { klass := Boot.regexpId, payload := .regexp src opts }
  (.ref o, { m with heap := h })

/-- `binary` records the **subject**'s encoding: every String a MatchData hands
    back is a slice of the subject and carries its tag, so the flag lives on the
    MatchData object and `okStrFrom md` reads it (L118). -/
def allocMData (m : Machine) (subject : String) (caps : Array (Option (Nat × Nat)))
    (names : List (String × Nat)) (binary : Bool := false) : Value × Machine :=
  let (o, h) := m.heap.alloc
    { klass := Boot.matchDataId, payload := .mdata subject caps names, binary }
  (.ref o, { m with heap := h })

/-- Outcome of applying a pattern to a subject: the engine's answer, already
    translated into what the Ruby layer needs. -/
inductive Found where
  | miss
  | hit (mstart mend : Nat) (caps : Array (Option (Nat × Nat))) (names : List (String × Nat))
  | gate (reason : String)

/-- Parse `src`/`opts` and search `subject` from character offset `start`. The
    single choke point named in this file's header. -/
def runSearch (src : String) (opts : Nat) (subject : String) (start : Nat := 0) : Found :=
  match Rx.parse src opts with
  | .error e => .gate e
  | .ok r =>
    let inp := subject.toList.toArray
    let res := if r.hasBackref then Rx.matchBR r inp (Rx.bound r inp.size * 4 + 64) start
               else Rx.search r inp start
    match res with
    | .no => .miss
    | .oof => .gate "regex: bound exhausted"
    | .yes a b caps => .hit a b caps r.names

/-- `Regexp.escape`: backslash every character that is special in a pattern,
    and render the control whitespace as its escape [V]. -/
def escapeSource (s : String) : String :=
  s.foldl (fun acc c =>
    if c == '\n' then acc ++ "\\n"
    else if c == '\t' then acc ++ "\\t"
    else if c == '\r' then acc ++ "\\r"
    else if c == Char.ofNat 12 then acc ++ "\\f"
    else if c == Char.ofNat 11 then acc ++ "\\v"
    else if c == ' ' then acc ++ "\\ "
    else if "[]{}()|-*.\\?+^$#".any (· == c) then (acc.push '\\').push c
    else acc.push c) ""

/-- Ruby's awk-mode separator: runs of whitespace (`split` with `" "` or no
    argument), with leading whitespace already trimmed by the caller. -/
def awkSep : String := "[ " ++ "\\t\\n\\r\\f\\v" ++ "]+"

/-- Characters `a` (inclusive) to `b` (exclusive) of `s`. -/
def charSlice (s : String) (a b : Nat) : String :=
  String.mk ((s.toList.drop a).take (b - a))

/-- Set `$~` and the numbered globals, the way a successful (or failed) match
    does [V]: on a miss they all become nil. -/
def setMatchGlobals (m : Machine) (md : Option Value) : Machine :=
  { m with globals := m.globals.filter (fun p => p.1 != "$~") ++ [("$~", md.getD .nil)] }

/-- Leave `$~` at the **last** of a scan's matches, or at nil when there were
    none. Every multi-match builtin owes this: CRuby's `scan`/`sub`/`gsub` all
    leave the backref globals set, so `"a1b2".scan(/\d/); $~[0]` is `"2"` and
    `"abc".gsub(/z/, "-"); $~` is nil [V]. Missing it was a wrong answer rather
    than a gate, because `$~` simply kept an older match (N39). -/
def setLastMatch (m : Machine) (s : String) (src : String) (opts : Nat)
    (hits : List (Nat × Nat × Array (Option (Nat × Nat)))) (bin : Bool) : Machine :=
  match hits.getLast? with
  | none => setMatchGlobals m none
  | some (_, _, caps) =>
    -- group names are a property of the pattern, not of the match, so they are
    -- re-derived here rather than threaded through `allMatches` — without them
    -- `$~.names` after a `gsub` over a named pattern would come back empty
    let names := match Rx.parse src opts with | .ok r => r.names | .error _ => []
    let (md, m) := allocMData m s caps names bin
    setMatchGlobals m (some md)

/-- `Regexp` and `MatchData` rules, plus the pattern-taking `String` methods. -/
def runRegex (bid : String) (recv : Value) (args : List Value) (m : Machine) : BRes :=
  let h := m.heap
  match bid with
  /- ─── Regexp ─── -/
  | "Regexp#source" =>
    match regexpParts? h recv with
    | some (src, _) => okStr m src
    | none => .unsupported "Regexp#source on a non-Regexp"
  | "Regexp#options" =>
    match regexpParts? h recv with
    | some (_, opts) => .ok (.int opts) m
    | none => .unsupported "Regexp#options on a non-Regexp"
  | "Regexp#inspect" =>
    match regexpParts? h recv with
    | some (src, opts) => okStr m (regexpInspect src opts)
    | none => .unsupported "Regexp#inspect on a non-Regexp"
  | "Regexp#to_s" =>
    match regexpParts? h recv with
    | some (src, opts) => okStr m (regexpToS src opts)
    | none => .unsupported "Regexp#to_s on a non-Regexp"
  | "Regexp#hash" =>
    -- Equal patterns must hash equally; the value itself is unobservable in
    -- any program we admit, so the source length + options is enough and is
    -- deterministic (contrast `Object#hash`, which is address-based).
    match regexpParts? h recv with
    | some (src, opts) => .ok (.int (src.length * 64 + opts)) m
    | none => .unsupported "Regexp#hash on a non-Regexp"
  | "MatchData#inspect" =>
    match inspectP m recv with
    | .ok str => okStr m str
    | .error e => .unsupported e
  | "Regexp#names" =>
    match regexpParts? h recv with
    | some (src, opts) =>
      match Rx.parse src opts with
      | .error e => .unsupported e
      | .ok r =>
        let (vs, m) := r.names.foldl (fun (acc, m) (n, _) =>
          let (v, m) := allocStr m n; (acc.push v, m)) (#[], m)
        let (v, m) := allocArr m vs
        .ok v m
    | none => .unsupported "Regexp#names on a non-Regexp"
  | "Regexp#==" | "Regexp#eql?" =>
    binArg m args fun b =>
      match regexpParts? h recv, regexpParts? h b with
      | some (s₁, o₁), some (s₂, o₂) => .ok (.bool (s₁ == s₂ && o₁ == o₂)) m
      | _, _ => .ok (.bool false) m
  | "Regexp#match" | "Regexp#match?" | "Regexp#=~" | "Regexp#===" =>
    binArg m args fun subj => regexApply bid m recv subj
  | "Regexp#escape" | "Regexp#quote" =>
    binArg m args fun a =>
      match strPayload? h a, a with
      | some str, _ => okStr m (escapeSource str)
      | none, .sym sy => okStr m (escapeSource sy)
      | _, _ => .unsupported "Regexp.escape of a non-String"
  | "Regexp#union" =>
    -- `Regexp.union(a, b)` and `Regexp.union([a, b])` are the same call [V].
    -- A String member is escaped (it is a literal); a Regexp member contributes
    -- its `to_s`, which carries its own flags as an inline group — which is why
    -- `Regexp#to_s` renders `(?-mix:…)` rather than the bare source.
    let items := match args with
      | [one] => match arrPayload? h one with
        | some xs => xs.toList
        | none => args
      | _ => args
    if items.isEmpty then
      let (v, m) := allocRegexp m "(?!)" 0
      .ok v m
    else
      let parts := items.map fun it =>
        match regexpParts? h it with
        | some (src, opts) => some (regexpToS src opts)
        | none => match strPayload? h it with
          | some str => some (escapeSource str)
          | none => match it with
            | .sym sy => some (escapeSource sy)
            | _ => none
      if parts.any (·.isNone) then .unsupported "Regexp.union member is not a String or Regexp"
      else
        let src := String.intercalate "|" (parts.filterMap id)
        let (v, m) := allocRegexp m src 0
        .ok v m
  /- ─── MatchData ─── -/
  | "MatchData#to_s" =>
    match mdataParts? h recv with
    | some (s, caps, _) =>
      match caps[0]? with
      | some (some (a, b)) => okStrFrom m recv (charSlice s a b)
      | _ => .unsupported "MatchData#to_s"
    | none => .unsupported "MatchData#to_s on a non-MatchData"
  | "MatchData#size" | "MatchData#length" =>
    match mdataParts? h recv with
    | some (_, caps, _) => .ok (.int caps.size) m
    | none => .unsupported "MatchData#size on a non-MatchData"
  | "MatchData#pre_match" =>
    match mdataParts? h recv with
    | some (s, caps, _) =>
      match caps[0]? with
      | some (some (a, _)) => okStrFrom m recv (charSlice s 0 a)
      | _ => .unsupported "MatchData#pre_match"
    | none => .unsupported "MatchData#pre_match on a non-MatchData"
  | "MatchData#post_match" =>
    match mdataParts? h recv with
    | some (s, caps, _) =>
      match caps[0]? with
      | some (some (_, b)) => okStrFrom m recv (charSlice s b s.length)
      | _ => .unsupported "MatchData#post_match"
    | none => .unsupported "MatchData#post_match on a non-MatchData"
  | "MatchData#begin" | "MatchData#end" =>
    binArg m args fun i =>
      match mdataParts? h recv, i with
      | some (_, caps, _), .int k =>
        if k < 0 then .err Boot.indexErrorId s!"index {k} out of matches" m
        else match caps[k.toNat]? with
          | some (some (a, b)) => .ok (.int (if bid == "MatchData#begin" then a else b)) m
          | some none => .ok .nil m
          | none => .err Boot.indexErrorId s!"index {k} out of matches" m
      | _, _ => .unsupported "MatchData#begin/end"
  | "MatchData#captures" | "MatchData#to_a" =>
    match mdataParts? h recv with
    | some (s, caps, _) =>
      let items := if bid == "MatchData#to_a" then caps.toList else caps.toList.drop 1
      let bin := isBinaryStr h recv
      let (vs, m) := items.foldl (fun (acc, m) sp =>
        match sp with
        | some (a, b) => let (v, m) := allocStrEnc m (charSlice s a b) bin; (acc.push v, m)
        | none => (acc.push Value.nil, m)) (#[], m)
      let (v, m) := allocArr m vs
      .ok v m
    | none => .unsupported "MatchData#captures on a non-MatchData"
  | "MatchData#names" =>
    match mdataParts? h recv with
    | some (_, _, names) =>
      let (vs, m) := names.foldl (fun (acc, m) (n, _) =>
        let (v, m) := allocStr m n; (acc.push v, m)) (#[], m)
      let (v, m) := allocArr m vs
      .ok v m
    | none => .unsupported "MatchData#names on a non-MatchData"
  | "MatchData#named_captures" =>
    match mdataParts? h recv with
    | some (s, caps, names) =>
      let bin := isBinaryStr h recv
      let (ps, m) := names.foldl (fun (acc, m) (n, i) =>
        let (k, m) := allocStr m n
        match caps[i]? with
        | some (some (a, b)) =>
          let (v, m) := allocStrEnc m (charSlice s a b) bin; (acc.push (k, v), m)
        | _ => (acc.push (k, Value.nil), m)) (#[], m)
      let (v, m) := allocHsh m ps
      .ok v m
    | none => .unsupported "MatchData#named_captures on a non-MatchData"
  | "MatchData#[]" =>
    binArg m args fun key =>
      match mdataParts? h recv with
      | none => .unsupported "MatchData#[] on a non-MatchData"
      | some (s, caps, names) =>
        let byName (n : String) : BRes :=
          match names.find? (fun p => p.1 == n) with
          | none => .err Boot.indexErrorId s!"undefined group name reference: {n}" m
          | some (_, i) =>
            match caps[i]? with
            | some (some (a, b)) => okStrFrom m recv (charSlice s a b)
            | _ => .ok .nil m
        match key with
        | .int k =>
          if k < 0 then .ok .nil m
          else match caps[k.toNat]? with
            | some (some (a, b)) => okStrFrom m recv (charSlice s a b)
            | _ => .ok .nil m
        | .sym n => byName n
        | .ref o => match (h.get o).payload with
          | .str n => byName n
          | _ => .unsupported "MatchData#[] key"
        | _ => .unsupported "MatchData#[] key"
  /- ─── String methods that take a pattern ─── -/
  | "String#=~" | "String#match" | "String#match?" =>
    binArg m args fun pat =>
      match regexpParts? h pat with
      | none => .unsupported "String pattern method with a non-Regexp pattern"
      | some (src, opts) =>
        -- `s.match(re)` is `re.match(s)` with the arguments swapped, and the
        -- same is true of `=~` and `match?` [V], so there is one code path.
        let bid' := "Regexp#" ++ (bid.drop 7)
        regexApply bid' m pat recv
  | "String#__search_at" =>
    -- Search **the whole receiver** from character offset `pos`, setting `$~` the
    -- way `Regexp#match` does. The primitive the prelude's block-form `sub`/`gsub`
    -- is written on (N39): a loop over a *shrinking* subject re-anchors at every
    -- step, so `"12".gsub(/\A\d/) { "X" }` answered `"XX"` where CRuby answers
    -- `"X2"` — a wrong answer, not a gate. Anchors here are absolute (`.bos` is
    -- `pos == 0`), which is exactly what makes offset-based iteration faithful.
    match args, strPayload? h recv with
    | [pat, .int pos], some s =>
      match regexpParts? h pat with
      | none => .unsupported "String#__search_at with a non-Regexp pattern"
      | some (src, opts) =>
        let start := if pos < 0 then 0 else pos.toNat
        if start > s.length then .ok .nil (setMatchGlobals m none)
        else match runSearch src opts s start with
          | .gate why => .unsupported why
          | .miss => .ok .nil (setMatchGlobals m none)
          | .hit _ _ caps names =>
            let (md, m) := allocMData m s caps names (isBinaryStr h recv)
            .ok md (setMatchGlobals m (some md))
    | _, _ => .unsupported "String#__search_at arity"
  | "String#scan" =>
    binArg m args fun pat =>
      match strPayload? h recv, regexpParts? h pat with
      | some s, some (src, opts) => scanAll m s src opts (isBinaryStr h recv)
      | _, _ => .unsupported "String#scan"
  | "String#split" =>
    -- `split` with a **Regexp** separator *clears* `$~`, even when the pattern
    -- matched; with a String separator it leaves the previous match alone [V].
    -- (`scan` by contrast leaves its last match — see `setLastMatch`.) N39.
    let clearIfRe : Machine → Value → Machine := fun m pat =>
      if (regexpParts? h pat).isSome then setMatchGlobals m none else m
    match args, strPayload? h recv with
    | [], some s => splitBy m s.trimLeft awkSep 0 0 (isBinaryStr h recv)
    | [pat], some s => splitOn (clearIfRe m pat) h s pat 0 (isBinaryStr h recv)
    | [pat, .int lim], some s => splitOn (clearIfRe m pat) h s pat lim (isBinaryStr h recv)
    | _, _ => .unsupported "String#split arity"
  | "String#__split_never" =>
    match args, strPayload? h recv with
    | [pat], some s =>
      let bin := isBinaryStr h recv
      match regexpParts? h pat with
      | some (src, opts) => splitBy (setMatchGlobals m none) s src opts 0 bin
      | none =>
        match strPayload? h pat with
        -- A String separator is a *literal*, not a pattern, so it is escaped
        -- rather than compiled — otherwise `"a.b".split(".")` would split on
        -- every character [V]. `" "` is Ruby's awk-mode separator (runs of
        -- whitespace, leading whitespace ignored) and is its own rule.
        | some sep =>
          if sep == " " then splitBy m s.trimLeft awkSep 0 0 bin
          else if sep.isEmpty then splitBy m s "(?!\\A)" 0 0 bin
          else splitBy m s (escapeSource sep) 0 0 bin
        | none => .unsupported "String#split with a non-String, non-Regexp pattern"
    | _, _ => .unsupported "String#split arity"
  | "String#__sub_rep" | "String#__gsub_rep" =>
    match args, strPayload? h recv with
    | [pat, rep], some s =>
      match strPayload? h rep with
      | none => .unsupported "String#sub/gsub with a non-String replacement"
      | some r =>
        match regexpParts? h pat with
        | some (src, opts) =>
          subst m s src opts r (bid == "String#__gsub_rep") recv rep
        -- A String pattern is a literal, escaped rather than compiled — the
        -- same rule as `split` [V].
        | none => match strPayload? h pat with
          | some lit =>
            subst m s (escapeSource lit) 0 r (bid == "String#__gsub_rep") recv rep
          | none => .unsupported "String#sub/gsub with a non-String, non-Regexp pattern"
    | _, _ => .unsupported "String#sub/gsub arity"
  | _ => .unsupported s!"builtin {bid}"
where
  /-- `Regexp#match` / `#match?` / `#=~` / `#===` share one path: they differ
      only in what they build from the same search. -/
  regexApply (bid : String) (m : Machine) (re : Value) (subj : Value) : BRes :=
    match regexpParts? m.heap re with
    | none => .unsupported "Regexp match on a non-Regexp"
    | some (src, opts) =>
      let bin := isBinaryStr m.heap subj
      match strPayload? m.heap subj, subj with
      | none, .sym s => applyTo bid m src opts s bin
      | none, _ =>
        -- `=~`/`match` against nil is nil; `===` against a non-string is false
        -- [V]; anything else would need `to_str` and is gated.
        match subj with
        | .nil => .ok (if bid == "Regexp#match?" || bid == "Regexp#===" then .bool false else .nil) m
        | _ =>
          if bid == "Regexp#===" then .ok (.bool false) m
          else .unsupported "Regexp match against a non-String"
      | some s, _ => applyTo bid m src opts s bin
  /-- Every match of `src` in `s`, left to right, as (start, stop, caps). A
      zero-width match advances by one character, which is what stops
      `"abc".scan(//)` from looping [V]. Bounded by the string length. -/
  allMatches (src : String) (opts : Nat) (s : String) :
      Nat → Nat → List (Nat × Nat × Array (Option (Nat × Nat))) →
      Except String (List (Nat × Nat × Array (Option (Nat × Nat))))
    | 0, _, acc => .ok acc.reverse
    | n + 1, from_, acc =>
      if from_ > s.length then .ok acc.reverse
      else match runSearch src opts s from_ with
        | .gate why => .error why
        | .miss => .ok acc.reverse
        | .hit a b caps _ =>
          allMatches src opts s n (if b == a then b + 1 else b) ((a, b, caps) :: acc)
  scanAll (m : Machine) (s : String) (src : String) (opts : Nat) (bin : Bool) : BRes :=
    match allMatches src opts s (s.length + 2) 0 [] with
    | .error why => .unsupported why
    | .ok hits =>
      -- `scan` leaves `$~` at its **last** match, and at `nil` when there were
      -- none [V] — `"a1b2".scan(/\d/); $~[0]` is `"2"` (N39).
      let m := setLastMatch m s src opts hits bin
      -- With no groups `scan` yields strings; with groups it yields arrays of
      -- the captures [V].
      let (vs, m) := hits.foldl (fun (acc, m) (a, b, caps) =>
        if caps.size ≤ 1 then
          let (v, m) := allocStrEnc m (charSlice s a b) bin; (acc.push v, m)
        else
          let (inner, m) := (caps.toList.drop 1).foldl (fun (ia, m) sp =>
            match sp with
            | some (x, y) => let (v, m) := allocStrEnc m (charSlice s x y) bin; (ia.push v, m)
            | none => (ia.push Value.nil, m)) (#[], m)
          let (v, m) := allocArr m inner; (acc.push v, m)) (#[], m)
      let (v, m) := allocArr m vs
      .ok v m
  /-- `split` with any pattern shape and any limit. A String separator is a
      *literal* (escaped), `" "` is awk mode, `""` splits into characters. -/
  splitOn (m : Machine) (h : Heap) (s : String) (pat : Value) (lim : Int)
      (bin : Bool) : BRes :=
    match regexpParts? h pat with
    | some (src, opts) => splitBy m s src opts lim bin
    | none =>
      match strPayload? h pat, pat with
      | _, .nil => splitBy m s.trimLeft awkSep 0 lim bin
      | some sep, _ =>
        if sep == " " then splitBy m s.trimLeft awkSep 0 lim bin
        else if sep.isEmpty then splitBy m s "(?!\\A)" 0 lim bin
        else splitBy m s (escapeSource sep) 0 lim bin
      | none, _ => .unsupported "String#split with a non-String, non-Regexp pattern"
  splitBy (m : Machine) (s : String) (src : String) (opts : Nat) (lim : Int)
      (bin : Bool) : BRes :=
    -- An **empty** subject splits to `[]` whatever the pattern and the limit —
    -- including `-1`, which otherwise keeps every trailing empty field [V].
    if s.isEmpty then let (v, m) := allocArr m #[]; .ok v m else
    match allMatches src opts s (s.length + 2) 0 [] with
    | .error why => .unsupported why
    | .ok allHits =>
      -- A separator match ends the current field at `a` and starts the next at
      -- `b`; for a zero-width separator those coincide, which is what makes
      -- `"abc".split("")` give three pieces rather than one [V].
      --
      -- A **capturing** separator also contributes its groups:
      -- `"a1b".split(/(\d)/)` is `["a", "1", "b"]` [V]. An **unmatched** group
      -- contributes *nothing* — not a `nil` element that trailing-trim later
      -- removes, but never pushed at all, even when more fields follow:
      -- `"a1b".split(/(\d)(x)?/)` and `"a1b".split(/(x)?(\d)/)` are both
      -- `["a", "1", "b"]` [V]. So `split` never returns a `nil` (N39).
      --
      -- The fold carries the field start `cur` *and* the number of separators
      -- taken, because both of the remaining rules need them (N39):
      let step := fun (acc : List String × Nat × Nat)
          (h : Nat × Nat × Array (Option (Nat × Nat))) =>
        let (pieces, cur, nsep) := acc
        let (a, b, caps) := h
        -- (1) A zero-width match **at the current field start** is not a
        -- separator: it would contribute an empty field where CRuby contributes
        -- none. This is why `"aab".split(/a*/)` is `["", "b"]` and not
        -- `["", "", "b"]` [V] — the empty match at offset 2, where the previous
        -- match ended, is skipped. Testing `a == 0` instead (the old rule) only
        -- caught the special case at the front of the string.
        if b == a && a == cur then acc
        -- (2) A positive limit caps the number of *fields*, so stop after
        -- `lim - 1` separators — counted **here** rather than by pre-truncating
        -- the hit list, because a match skipped by (1) must not consume one of
        -- them: `"abc".split(//, 2)` is `["a", "bc"]`, and pre-truncation spent
        -- the budget on the skipped zero-width match at 0 and answered
        -- `["abc"]` [V].
        else if lim > 0 && Int.ofNat nsep ≥ lim - 1 then acc
        else
          let groups := (caps.toList.drop 1).filterMap fun sp =>
            sp.map fun (x, y) => charSlice s x y
          (pieces ++ [charSlice s cur a] ++ groups, b, nsep + 1)
      let (pieces, last, _) := allHits.foldl step ([], 0, 0)
      let pieces := pieces ++ [charSlice s last s.length]
      -- `split` drops *trailing* empty fields — unless a limit was given, where
      -- a positive one keeps them and a negative one keeps them all [V].
      let trimmed :=
        if lim == 0 then (pieces.reverse.dropWhile (· == "")).reverse else pieces
      let (vs, m) := trimmed.foldl (fun (acc, m) str =>
        let (v, m) := allocStrEnc m str bin; (acc.push v, m)) (#[], m)
      let (v, m) := allocArr m vs
      .ok v m
  subst (m : Machine) (s : String) (src : String) (opts : Nat) (rep : String)
      (global : Bool) (recvV repV : Value) : BRes :=
    match allMatches src opts s (if global then s.length + 2 else 1) 0 [] with
    | .error why => .unsupported why
    | .ok hits =>
      -- as `scan`: `sub`/`gsub` leave `$~` at their last match [V] (N39)
      let m := setLastMatch m s src opts hits (isBinaryStr m.heap recvV)
      if rep.any (· == '\\') then
        -- `\1` / `\0` / `\k<name>` in the replacement is its own sublanguage;
        -- gate rather than emit the backslash literally.
        .unsupported "String#sub/gsub replacement with a backreference"
      else
        let (out, last) := hits.foldl (fun (acc, cur) (a, b, _) =>
          (acc ++ charSlice s cur a ++ rep, b)) ("", 0)
        -- the result mixes subject and replacement bytes, so it takes the tag
        -- their concatenation would (L118) — and refuses the incompatible mix
        match concatEnc m.heap recvV s repV rep with
        | .error e => .unsupported e
        | .ok bin => okStrEnc m bin (out ++ charSlice s last s.length)
  applyTo (bid : String) (m : Machine) (src : String) (opts : Nat) (s : String)
      (bin : Bool) : BRes :=
    match runSearch src opts s with
    | .gate why => .unsupported why
    | .miss =>
      let m := setMatchGlobals m none
      .ok (if bid == "Regexp#match?" || bid == "Regexp#===" then .bool false else .nil) m
    | .hit a _ caps names =>
      if bid == "Regexp#match?" then .ok (.bool true) m       -- match? sets no globals [V]
      else if bid == "Regexp#===" then
        let (md, m) := allocMData m s caps names bin
        .ok (.bool true) (setMatchGlobals m (some md))
      else
        let (md, m) := allocMData m s caps names bin
        let m := setMatchGlobals m (some md)
        if bid == "Regexp#=~" then .ok (.int a) m else .ok md m

end Builtins

end RubyCore
