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

def allocMData (m : Machine) (subject : String) (caps : Array (Option (Nat × Nat)))
    (names : List (String × Nat)) : Value × Machine :=
  let (o, h) := m.heap.alloc
    { klass := Boot.matchDataId, payload := .mdata subject caps names }
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

/-- Characters `a` (inclusive) to `b` (exclusive) of `s`. -/
def charSlice (s : String) (a b : Nat) : String :=
  String.mk ((s.toList.drop a).take (b - a))

/-- Set `$~` and the numbered globals, the way a successful (or failed) match
    does [V]: on a miss they all become nil. -/
def setMatchGlobals (m : Machine) (md : Option Value) : Machine :=
  { m with globals := m.globals.filter (fun p => p.1 != "$~") ++ [("$~", md.getD .nil)] }

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
  /- ─── MatchData ─── -/
  | "MatchData#to_s" =>
    match mdataParts? h recv with
    | some (s, caps, _) =>
      match caps[0]? with
      | some (some (a, b)) => okStr m (charSlice s a b)
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
      | some (some (a, _)) => okStr m (charSlice s 0 a)
      | _ => .unsupported "MatchData#pre_match"
    | none => .unsupported "MatchData#pre_match on a non-MatchData"
  | "MatchData#post_match" =>
    match mdataParts? h recv with
    | some (s, caps, _) =>
      match caps[0]? with
      | some (some (_, b)) => okStr m (charSlice s b s.length)
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
      let (vs, m) := items.foldl (fun (acc, m) sp =>
        match sp with
        | some (a, b) => let (v, m) := allocStr m (charSlice s a b); (acc.push v, m)
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
      let (ps, m) := names.foldl (fun (acc, m) (n, i) =>
        let (k, m) := allocStr m n
        match caps[i]? with
        | some (some (a, b)) =>
          let (v, m) := allocStr m (charSlice s a b); (acc.push (k, v), m)
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
            | some (some (a, b)) => okStr m (charSlice s a b)
            | _ => .ok .nil m
        match key with
        | .int k =>
          if k < 0 then .ok .nil m
          else match caps[k.toNat]? with
            | some (some (a, b)) => okStr m (charSlice s a b)
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
  | "String#scan" =>
    binArg m args fun pat =>
      match strPayload? h recv, regexpParts? h pat with
      | some s, some (src, opts) => scanAll m s src opts
      | _, _ => .unsupported "String#scan"
  | "String#split" =>
    binArg m args fun pat =>
      match strPayload? h recv, regexpParts? h pat with
      | some s, some (src, opts) => splitBy m s src opts
      | _, _ => .unsupported "String#split with a Regexp"
  | "String#sub" | "String#gsub" =>
    match args, strPayload? h recv with
    | [pat, rep], some s =>
      match regexpParts? h pat, strPayload? h rep with
      | some (src, opts), some r => subst m s src opts r (bid == "String#gsub")
      | _, _ => .unsupported "String#sub/gsub arguments"
    | _, _ => .unsupported "String#sub/gsub arity"
  | _ => .unsupported s!"builtin {bid}"
where
  /-- `Regexp#match` / `#match?` / `#=~` / `#===` share one path: they differ
      only in what they build from the same search. -/
  regexApply (bid : String) (m : Machine) (re : Value) (subj : Value) : BRes :=
    match regexpParts? m.heap re with
    | none => .unsupported "Regexp match on a non-Regexp"
    | some (src, opts) =>
      match strPayload? m.heap subj, subj with
      | none, .sym s => applyTo bid m src opts s
      | none, _ =>
        -- `=~`/`match` against nil is nil; `===` against a non-string is false
        -- [V]; anything else would need `to_str` and is gated.
        match subj with
        | .nil => .ok (if bid == "Regexp#match?" || bid == "Regexp#===" then .bool false else .nil) m
        | _ =>
          if bid == "Regexp#===" then .ok (.bool false) m
          else .unsupported "Regexp match against a non-String"
      | some s, _ => applyTo bid m src opts s
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
  scanAll (m : Machine) (s : String) (src : String) (opts : Nat) : BRes :=
    match allMatches src opts s (s.length + 2) 0 [] with
    | .error why => .unsupported why
    | .ok hits =>
      -- With no groups `scan` yields strings; with groups it yields arrays of
      -- the captures [V].
      let (vs, m) := hits.foldl (fun (acc, m) (a, b, caps) =>
        if caps.size ≤ 1 then
          let (v, m) := allocStr m (charSlice s a b); (acc.push v, m)
        else
          let (inner, m) := (caps.toList.drop 1).foldl (fun (ia, m) sp =>
            match sp with
            | some (x, y) => let (v, m) := allocStr m (charSlice s x y); (ia.push v, m)
            | none => (ia.push Value.nil, m)) (#[], m)
          let (v, m) := allocArr m inner; (acc.push v, m)) (#[], m)
      let (v, m) := allocArr m vs
      .ok v m
  splitBy (m : Machine) (s : String) (src : String) (opts : Nat) : BRes :=
    match allMatches src opts s (s.length + 2) 0 [] with
    | .error why => .unsupported why
    | .ok hits =>
      let (pieces, last) := hits.foldl (fun (acc, cur) (a, b, _) =>
        if b == a && a == 0 then (acc, cur)         -- a leading empty match adds nothing
        else (acc ++ [charSlice s cur a], if b == a then a + 1 else b)) ([], 0)
      let pieces := pieces ++ [charSlice s last s.length]
      -- `split` drops *trailing* empty fields (but not leading or interior) [V].
      let trimmed := (pieces.reverse.dropWhile (·.isEmpty)).reverse
      let (vs, m) := trimmed.foldl (fun (acc, m) p =>
        let (v, m) := allocStr m p; (acc.push v, m)) (#[], m)
      let (v, m) := allocArr m vs
      .ok v m
  subst (m : Machine) (s : String) (src : String) (opts : Nat) (rep : String)
      (global : Bool) : BRes :=
    match allMatches src opts s (if global then s.length + 2 else 1) 0 [] with
    | .error why => .unsupported why
    | .ok hits =>
      if rep.any (· == '\\') then
        -- `\1` / `\0` / `\k<name>` in the replacement is its own sublanguage;
        -- gate rather than emit the backslash literally.
        .unsupported "String#sub/gsub replacement with a backreference"
      else
        let (out, last) := hits.foldl (fun (acc, cur) (a, b, _) =>
          (acc ++ charSlice s cur a ++ rep, b)) ("", 0)
        okStr m (out ++ charSlice s last s.length)
  applyTo (bid : String) (m : Machine) (src : String) (opts : Nat) (s : String) : BRes :=
    match runSearch src opts s with
    | .gate why => .unsupported why
    | .miss =>
      let m := setMatchGlobals m none
      .ok (if bid == "Regexp#match?" || bid == "Regexp#===" then .bool false else .nil) m
    | .hit a _ caps names =>
      if bid == "Regexp#match?" then .ok (.bool true) m       -- match? sets no globals [V]
      else if bid == "Regexp#===" then
        let (md, m) := allocMData m s caps names
        .ok (.bool true) (setMatchGlobals m (some md))
      else
        let (md, m) := allocMData m s caps names
        let m := setMatchGlobals m (some md)
        if bid == "Regexp#=~" then .ok (.int a) m else .ok md m

end Builtins

end RubyCore
