import RubyCore.Regex.Syntax

/-!
The executable matcher: Ruby-faithful leftmost, greedy-first backtracking, in
continuation-passing style, **structurally recursive on a fuel `Nat` computed
from the input** (D1).

Three things follow from that shape and are worth stating up front.

* *No `partial def`, no `termination_by`.* The recursion is structural on the
  first `Nat` argument, so the definition reduces in the kernel and a per-program
  `rfl` leaf proof stays possible (L73, L94).
* *Fuel exhaustion is a third outcome, not "no match".* `MRes.oof` is distinct
  from `MRes.no` and propagates to the top, where the API turns it into the SUT
  contract's `Unsupported` gate. A matcher that reported "no match" on running
  out of fuel would be a silent wrong answer — the one thing the ratchet cannot
  catch. Once `bound_suffices` is proved (`Bound.lean`), `oof` is unreachable for
  backref-free patterns and the gate becomes dead code rather than a caveat.
* *Backtracking order is the specification.* Greedy repetition tries the longer
  match first, lazy the shorter; alternation tries the left branch first; the
  search tries the leftmost start first. That order is what fixes *which* of
  several matches Ruby reports, and therefore what the capture groups contain.
-/

namespace RubyCore

namespace Rx

/-- Capture slots, indexed by group number; slot 0 is the whole match and is
    filled in by the caller. `(start, stop)` are character offsets. -/
abbrev Caps := Array (Option (Nat × Nat))

/-- The three outcomes of a match attempt. -/
inductive MRes where
  | no
  | yes (pos : Nat) (caps : Caps)
  | oof
deriving Inhabited

/-- A continuation: "the rest of the pattern matched from here". -/
abbrev Cont := Nat → Caps → MRes

def MRes.isOof : MRes → Bool
  | .oof => true
  | _ => false

/-- Try `a`; if it fails, try `b`. Out-of-fuel propagates rather than being
    treated as a failure to backtrack over. -/
@[inline] def orTry (a : MRes) (b : Unit → MRes) : MRes :=
  match a with
  | .no => b ()
  | x => x

def foldCase (c : Char) : Char := c.toLower

def isWordChar (c : Char) : Bool :=
  c.isAlphanum || c == '_'

def isSpaceChar (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' ||
  c == Char.ofNat 11 || c == Char.ofNat 12

def isHexChar (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

/-- Does one bracket item accept `c`? Case folding is applied by trying the
    folded character as well, which is exact for ASCII and is all the slice
    needs (its `(?i:…)` uses are ASCII keyword lists). -/
def itemMatch (it : ClsItem) (c : Char) : Bool :=
  match it with
  | .ch x => x == c
  | .range lo hi => lo ≤ c && c ≤ hi
  | .esc k neg =>
    let base :=
      if k == 'd' then c.isDigit
      else if k == 'w' then isWordChar c
      else if k == 's' then isSpaceChar c
      else if k == 'h' then isHexChar c
      else false
    if neg then !base else base

def clsMatch (cc : CharClass) (ic : Bool) (c : Char) : Bool :=
  let hit := cc.items.any (fun it => itemMatch it c) ||
    (ic && cc.items.any (fun it => itemMatch it (foldCase c) || itemMatch it c.toUpper))
  if cc.neg then !hit else hit

def litMatch (x : Char) (ic : Bool) (c : Char) : Bool :=
  x == c || (ic && foldCase x == foldCase c)

def anchorOk (a : Anchor) (inp : Array Char) (pos : Nat) : Bool :=
  let len := inp.size
  match a with
  | .bos => pos == 0
  | .eos => pos == len
  | .eosNl => pos == len || (pos + 1 == len && inp[pos]? == some '\n')
  | .lineStart => pos == 0 || inp[pos - 1]? == some '\n'
  | .lineEnd => pos == len || inp[pos]? == some '\n'

/-- Compare the input at `pos` against the text a capture group holds. -/
def backrefAt (inp : Array Char) (caps : Caps) (i pos : Nat) (ic : Bool) :
    Option Nat :=
  match caps[i]? with
  | some (some (a, b)) =>
    let n := b - a
    if pos + n ≤ inp.size &&
       (List.range n).all (fun j =>
          match inp[a + j]?, inp[pos + j]? with
          | some x, some y => litMatch x ic y
          | _, _ => false)
    then some (pos + n) else none
  -- An unset group backreferences nothing and never matches [V].
  | _ => none

/-- One match attempt of `r` at `pos`, calling `k` on success.

    `fuel` is structural: every recursive call passes the predecessor, so this
    is an ordinary structural recursion and the kernel can reduce it. -/
def go : Nat → Regex → Array Char → Nat → Caps → Cont → MRes
  | 0, _, _, _, _, _ => .oof
  | n + 1, r, inp, pos, caps, k =>
    match r with
    | .empty => k pos caps
    | .lit c ic =>
      match inp[pos]? with
      | some d => if litMatch c ic d then k (pos + 1) caps else .no
      | none => .no
    | .cls cc ic =>
      match inp[pos]? with
      | some d => if clsMatch cc ic d then k (pos + 1) caps else .no
      | none => .no
    | .any dotAll =>
      match inp[pos]? with
      | some d => if dotAll || d != '\n' then k (pos + 1) caps else .no
      | none => .no
    | .anchor a => if anchorOk a inp pos then k pos caps else .no
    | .cat r₁ r₂ =>
      go n r₁ inp pos caps (fun p c => go n r₂ inp p c k)
    | .alt r₁ r₂ =>
      orTry (go n r₁ inp pos caps k) (fun _ => go n r₂ inp pos caps k)
    | .group idx _ r' =>
      match idx with
      | none => go n r' inp pos caps k
      | some i =>
        go n r' inp pos caps (fun p c =>
          k p (if i < c.size then c.set! i (some (pos, p))
               else (c ++ Array.replicate (i + 1 - c.size) none).set! i (some (pos, p))))
    | .look neg r' =>
      -- Zero-width. A *positive* lookahead keeps the captures it made [V]; a
      -- negative one, having failed, has none to keep.
      let probe := go n r' inp pos caps (fun p c => .yes p c)
      match probe, neg with
      | .oof, _ => .oof
      | .yes _ c, false => k pos c
      | .no, false => .no
      | .yes _ _, true => .no
      | .no, true => k pos caps
    | .backref i =>
      match backrefAt inp caps i pos false with
      | some p => k p caps
      | none => .no
    | .rep r' lo hi greedy =>
      match hi with
      | some 0 => k pos caps
      | _ =>
        match lo with
        | l + 1 =>
          go n r' inp pos caps (fun p c =>
            go n (.rep r' l (hi.map (· - 1)) greedy) inp p c k)
        | 0 =>
          -- `more` is one further iteration. The `p == pos` guard is what makes
          -- `(a*)*` terminate — but note what it does *not* do: an iteration
          -- that consumed nothing still **happens**, and its captures stand;
          -- it is only barred from being followed by another. That is exactly
          -- CRuby's rule, and it is observable: `/(a*)*/ =~ "aaa"` leaves `$1`
          -- as the *empty* match at offset 3, not "aaa" [V], and `/(a?)*b/ =~
          -- "b"` sets `$1` to the empty string rather than leaving it nil.
          -- Refusing the empty iteration outright — the obvious reading of "no
          -- empty loops" — disagrees with CRuby on all eight such cases in the
          -- probe corpus.
          let more : Unit → MRes := fun _ =>
            go n r' inp pos caps (fun p c =>
              if p == pos then k p c
              else go n (.rep r' 0 (hi.map (· - 1)) greedy) inp p c k)
          if greedy then orTry (more ()) (fun _ => k pos caps)
          else orTry (k pos caps) more

/-- The fuel a match may need, computed from the pattern and the input (D1) —
    never a parameter of the *statement* of a theorem, only of the run.

    Each descent either consumes an input character or takes one structural step
    through the pattern, and the empty-progress guard stops a repetition from
    taking structural steps forever, so `(cost + 1) · (len + 2)` bounds the
    depth; the slack absorbs the anchors and the final continuation. -/
def bound (r : Regex) (len : Nat) : Nat :=
  (r.cost + 1) * (len + 2) + r.cost + 16

/-- The initial capture array for `r`: slot 0 plus one per group. -/
def initCaps (r : Regex) : Caps :=
  Array.replicate (r.groupCount + 1) none

/-- Result of a whole-pattern search. -/
inductive SRes where
  | no
  | yes (mstart mend : Nat) (caps : Caps)
  | oof
deriving Inhabited

/-- Anchored attempt at exactly `pos`. -/
def matchAt (r : Regex) (inp : Array Char) (pos : Nat) : SRes :=
  match go (bound r inp.size) r inp pos (initCaps r) (fun p c => .yes p c) with
  | .no => .no
  | .oof => .oof
  | .yes p c => .yes pos p (if 0 < c.size then c.set! 0 (some (pos, p)) else c)

/-- Leftmost search from `start`, trying each position in turn. Structural on
    the explicit step count, which is the number of remaining start positions. -/
def searchFrom : Nat → Regex → Array Char → Nat → SRes
  | 0, _, _, _ => .no
  | n + 1, r, inp, start =>
    if start > inp.size then .no
    else match matchAt r inp start with
      | .yes a b c => .yes a b c
      | .oof => .oof
      | .no => searchFrom n r inp (start + 1)

/-- Leftmost match at or after `start`. This is `Regexp#match`'s semantics. -/
def search (r : Regex) (inp : Array Char) (start : Nat := 0) : SRes :=
  searchFrom (inp.size + 2 - start) r inp start

/-- The backref-free entry point (D2). Refuses a pattern with a backreference
    rather than running it under a bound that provably cannot cover it. -/
def matchBackrefFree (r : Regex) (inp : Array Char) (start : Nat := 0) :
    Except String SRes :=
  if r.hasBackref then .error "regex: backreference (use matchBR)"
  else .ok (search r inp start)

/-- The backreference entry point (D2): the polynomial bound does not exist for
    a non-regular pattern, so the fuel is an explicit parameter and running out
    of it gates rather than answering. -/
def matchBR (r : Regex) (inp : Array Char) (fuel : Nat) (start : Nat := 0) : SRes :=
  let rec loop : Nat → Nat → SRes
    | 0, _ => .no
    | n + 1, p =>
      if p > inp.size then .no
      else
        match go fuel r inp p (initCaps r) (fun q c => .yes q c) with
        | .yes q c => .yes p q (if 0 < c.size then c.set! 0 (some (p, q)) else c)
        | .oof => .oof
        | .no => loop n (p + 1)
  loop (inp.size + 2 - start) start

end Rx

end RubyCore
