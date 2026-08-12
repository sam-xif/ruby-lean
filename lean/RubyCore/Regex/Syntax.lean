import RubyCore.Machine

/-!
The regex abstract syntax — the shape everything else in `RubyCore/Regex/` is
stated over.

Scope is set by measurement, not by ambition: these are exactly the constructs
used by the 86 regex literals of the Homebrew version + vulnerability slice
(`homebrew/PLAN.md` §2, W2a). Deliberately absent, because the slice contains
none: lookbehind, atomic groups, possessive quantifiers, `\b`, POSIX bracket
classes, `\p{…}`, `\x…`, conditionals, `\G`. The parser gates each of those by
name rather than mis-parsing it.

Two flags are resolved at **parse** time rather than carried at match time:

* `i` (ignore case) is pushed down onto the leaves (`lit`, `cls`), because
  `(?i:…)` scopes lexically and a match-time flag stack would have to be
  unwound on every backtrack.
* `x` (extended) is purely lexical — the parser drops whitespace and comments.

`m` survives as a field of `any`, since it changes only what `.` accepts. `^`
and `$` are line anchors in Ruby *regardless* of `m` (unlike Perl/PCRE), so no
flag reaches them.
-/

namespace RubyCore

namespace Rx

/-- One item of a bracket expression. The `\d`/`\w`/`\s` families are items
    rather than sugar for a range list so that negation composes the way Ruby's
    does (`[^\d]` is "not a digit", not "not one of 0..9" — the same here, but
    the intent stays readable). -/
inductive ClsItem where
  | ch (c : Char)
  | range (lo hi : Char)
  /-- `\d \D \w \W \s \S` inside a class; `neg` is the upper-case form. -/
  | esc (kind : Char) (neg : Bool)
deriving Repr, Inhabited, DecidableEq

/-- A bracket expression `[…]` / `[^…]`. -/
structure CharClass where
  neg : Bool
  items : List ClsItem
deriving Repr, Inhabited, DecidableEq

/-- Zero-width position assertions. -/
inductive Anchor where
  /-- `\A` — start of string. -/
  | bos
  /-- `\z` — end of string. -/
  | eos
  /-- `\Z` — end of string, or just before a trailing newline. -/
  | eosNl
  /-- `^` — start of string or just after a newline. -/
  | lineStart
  /-- `$` — end of string or just before a newline. -/
  | lineEnd
deriving Repr, Inhabited, DecidableEq

inductive Regex where
  /-- Matches the empty string. Also what an empty alternative branch is. -/
  | empty
  | lit (c : Char) (ic : Bool)
  | cls (cc : CharClass) (ic : Bool)
  /-- `.` — any character; `dotAll` is the `m` flag (then it accepts `\n` too). -/
  | any (dotAll : Bool)
  | anchor (a : Anchor)
  | cat (r₁ r₂ : Regex)
  | alt (r₁ r₂ : Regex)
  /-- `r{lo,hi}`, with `hi = none` for unbounded. `*` is `{0,}`, `+` is `{1,}`,
      `?` is `{0,1}`. `greedy = false` is the lazy form (`*?`). -/
  | rep (r : Regex) (lo : Nat) (hi : Option Nat) (greedy : Bool)
  /-- A group. `idx = none` is non-capturing (`(?:…)`); `name` is set for
      `(?<x>…)`, which also captures and so carries an index. -/
  | group (idx : Option Nat) (name : Option String) (r : Regex)
  /-- `(?=r)` / `(?!r)`. -/
  | look (neg : Bool) (r : Regex)
  /-- `\1` … `\9`. Non-regular: only `matchBR` accepts these (D2). -/
  | backref (n : Nat)
deriving Repr, Inhabited

/-- Does the pattern contain a backreference? The gate between the two entry
    points of D2: `match` (bounded, no backrefs) and `matchBR` (explicit fuel). -/
def Regex.hasBackref : Regex → Bool
  | .backref _ => true
  | .cat a b | .alt a b => a.hasBackref || b.hasBackref
  | .rep r _ _ _ | .group _ _ r | .look _ r => r.hasBackref
  | _ => false

/-- How many capture groups the pattern opens — i.e. the size of a `MatchData`
    minus the whole-match slot. -/
def Regex.groupCount : Regex → Nat
  | .group idx _ r => (if idx.isSome then 1 else 0) + r.groupCount
  | .cat a b | .alt a b => a.groupCount + b.groupCount
  | .rep r _ _ _ | .look _ r => r.groupCount
  | _ => 0

/-- Structural size, used to compute the match bound (D1). A bounded repetition
    counts its maximum unrolling, since that is how many nested `rep` descents a
    match can make without consuming input; an unbounded one counts `lo + 1`,
    because past `lo` the empty-progress guard forces every further iteration to
    consume a character and the input length factor in `bound` pays for those. -/
def Regex.cost : Regex → Nat
  | .empty | .lit .. | .cls .. | .any _ | .anchor _ | .backref _ => 1
  | .cat a b | .alt a b => 1 + a.cost + b.cost
  | .group _ _ r | .look _ r => 1 + r.cost
  | .rep r lo hi _ => 1 + (max lo (hi.getD lo) + 1) * (r.cost + 1)

/-- Named groups, in index order — what `MatchData#named_captures` needs. -/
def Regex.names : Regex → List (String × Nat)
  | .group idx name r =>
    let here := match idx, name with
      | some i, some n => [(n, i)]
      | _, _ => []
    here ++ r.names
  | .cat a b | .alt a b => a.names ++ b.names
  | .rep r _ _ _ | .look _ r => r.names
  | _ => []

end Rx

end RubyCore
