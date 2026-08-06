/-
The **symbolic shadow machine** (S1 of `docs/semantics/concolic-dataflow.md`).

Runs alongside the real `stepFn`, maintaining a symbolic term for the in-flight
value so the tracer can emit each branch condition as a **term over the symbolic
inputs** — the dataflow the concolic engine needs and cannot recover from a
concrete trace (value ambiguity, §1).

DESIGN COMMITMENTS (see the design doc for rationale)
* **No `stepFn` changes.** The shadow is driven by *observing* configurations:
  `stepFn` is deterministic and dispatches on `(ctl, kont-head)`, so from the
  pre-state we know which rule fires, and `m'` shows us its result.
* **No taint flag** (KLEE): a value is concrete iff its term is `lit`. The smart
  constructors constant-fold, so fully-concrete arithmetic collapses for free.
* **`opaque` is safe by construction**: anything unmodeled loses precision (no
  constraint) rather than producing a wrong one. Never guess a term.
* **Self-checking** (§6.4): every term assigned is a claim that evaluating it at
  the concrete inputs equals the machine's actual value. On mismatch we drop to
  `opaque` and note it, so a mirroring bug costs precision, never soundness.
-/
import RubyCore.Interp

namespace RubyCore
namespace Concolic

open Lean (Json)
open Interp

/-! ## Terms -/

inductive UnOp where | neg | succ | pred
deriving Repr, DecidableEq

inductive BinOp where
  | add | sub | mul
  | lt | le | gt | ge | eq | ne
  /-- Boolean disjunction (operands are 1/0-valued predicate terms). Needed to
      express a nil-guard such as `i < 0 ∨ i ≥ len` as a single term. -/
  | or
  /-- Boolean conjunction — expresses a Hash miss, `k ≠ k₁ ∧ … ∧ k ≠ kₙ`. -/
  | and
deriving Repr, DecidableEq

/-- A concrete value a term can denote: the two sorts the shadow tracks. Inputs are
    a heterogeneous vector of these, and `evalTerm` (the self-check oracle) returns
    one.

    Strings are here because **every reachable DRuby corpus defect branches on a
    string**, not an integer (`druby-reproduction-plan.md`). Only the well-behaved
    fragment is modeled — *equality against literals*. No concat, length, or regex:
    those are what make SMT string reasoning brittle, and none of the corpus's
    decisive guards need them. -/
inductive SymVal where
  | i (n : Int)
  | s (str : String)
deriving Repr, DecidableEq, Inhabited

def SymVal.toJson : SymVal → Json
  | .i n => Json.num ⟨n, 0⟩
  | .s str => Json.str str

/-- A symbolic term over the inputs. `opaque` = not tracked (see header). -/
inductive SymTerm where
  | inp (k : Nat)
  | lit (n : Int)
  /-- A **string literal**. Distinct from `conc`: we know its exact value, so an
      equality against it is a real constraint rather than lost precision. -/
  | slit (str : String)
  | un (op : UnOp) (a : SymTerm)
  | bin (op : BinOp) (a b : SymTerm)
  /-- A value we do not model *structurally*, but which we know does not depend on
      any symbolic input (a literal, or something built purely from literals).
      Distinguishing this from `opaque` is what lets us soundly read a *concrete*
      fact off the machine — e.g. the length of a literal array — and emit it as a
      `lit`, because that fact is the same on every run. Conflating the two (as a
      two-state design must) would either lose the fact or emit it unsoundly. -/
  | conc
  | opaque
deriving Repr, Inhabited

namespace SymTerm

def unOpName : UnOp → String
  | .neg => "neg" | .succ => "succ" | .pred => "pred"

def binOpName : BinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul"
  | .lt => "lt" | .le => "le" | .gt => "gt" | .ge => "ge"
  | .eq => "eq" | .ne => "ne" | .or => "or" | .and => "and"

/-- Is this a comparison (boolean-valued)? Arithmetic is integer-valued. -/
def binIsCmp : BinOp → Bool
  | .add | .sub | .mul => false
  | _ => true

partial def toJson : SymTerm → Json
  | .inp k => Json.arr #[Json.str "inp", Json.num ⟨Int.ofNat k, 0⟩]
  | .lit n => Json.arr #[Json.str "lit", Json.num ⟨n, 0⟩]
  | .slit s => Json.arr #[Json.str "slit", Json.str s]
  | .un op a => Json.arr #[Json.str "un", Json.str (unOpName op), toJson a]
  | .bin op a b =>
    Json.arr #[Json.str "bin", Json.str (binOpName op), toJson a, toJson b]
  -- `conc` carries no integer value, so it is not a solver term; the engine sees
  -- `null` and records no constraint (same treatment as `opaque`).
  | .conc | .opaque => Json.null

/-- Does the term mention an input? (Only such conditions are worth emitting —
    a purely-literal condition is not flippable.) -/
partial def hasInput : SymTerm → Bool
  | .inp _ => true
  | .lit _ => false
  | .slit _ => false
  | .un _ a => hasInput a
  | .bin _ a b => hasInput a || hasInput b
  | .conc => false
  | .opaque => false

/-- Is this value the same on every run (independent of the inputs)? Only such
    values may have a concrete fact read off the machine and frozen as a `lit`. -/
def isConst : SymTerm → Bool
  | .lit _ => true
  | .slit _ => true
  | .conc => true
  | _ => false

/-! ### Smart constructors (constant-folding — KLEE's `ExprBuilder` discipline) -/

def mkUn (op : UnOp) (a : SymTerm) : SymTerm :=
  match a with
  | .conc => .opaque
  | .opaque => .opaque
  -- no unary arithmetic on strings; `-@`/`succ`/`pred` on a String is either a
  -- different operation or an error, and guessing is exactly what we must not do
  | .slit _ => .opaque
  | .lit n => match op with
    | .neg => .lit (-n) | .succ => .lit (n + 1) | .pred => .lit (n - 1)
  | _ => .un op a

/-- Arithmetic/comparison, folding when both sides are literals. Comparisons
    fold to `lit 1`/`lit 0` (see `evalTerm`: booleans are 1/0). -/
def mkBin (op : BinOp) (a b : SymTerm) : SymTerm :=
  match a, b with
  | .conc, _ => .opaque
  | _, .conc => .opaque
  | .opaque, _ => .opaque
  | _, .opaque => .opaque
  | .lit x, .lit y =>
    match op with
    | .add => .lit (x + y) | .sub => .lit (x - y) | .mul => .lit (x * y)
    | .lt => .lit (if x < y then 1 else 0)
    | .le => .lit (if x ≤ y then 1 else 0)
    | .gt => .lit (if x > y then 1 else 0)
    | .ge => .lit (if x ≥ y then 1 else 0)
    | .eq => .lit (if x == y then 1 else 0)
    | .ne => .lit (if x != y then 1 else 0)
    | .or => .lit (if x != 0 || y != 0 then 1 else 0)
    | .and => .lit (if x != 0 && y != 0 then 1 else 0)
  -- String/String: only equality folds. Ordering (`<`) on strings IS defined in
  -- Ruby but is not modeled, and arithmetic (`+` = concat) is deliberately out —
  -- see the `SymVal` note on which fragment is well-behaved.
  | .slit x, .slit y =>
    match op with
    | .eq => .lit (if x == y then 1 else 0)
    | .ne => .lit (if x != y then 1 else 0)
    | _ => .opaque
  -- Mixed sorts: in Ruby `1 == "a"` is simply *false* (no coercion, no error), so
  -- equality is decidable across sorts and folds. Anything else is unmodeled.
  | .slit _, .lit _ | .lit _, .slit _ =>
    match op with
    | .eq => .lit 0
    | .ne => .lit 1
    | _ => .opaque
  | _, _ => .bin op a b

/-- Evaluate at the concrete inputs — the self-check oracle (§6.4). Booleans are
    `SymVal.i 1`/`i 0`, so comparisons of either sort land in the integer sort.
    A sort mismatch on an unmodeled operation yields `none` ("cannot say"), never
    a guessed value. -/
partial def evalTerm (inputs : List SymVal) : SymTerm → Option SymVal
  | .inp k => inputs[k]?
  | .lit n => some (.i n)
  | .slit s => some (.s s)
  | .conc => none
  | .opaque => none
  | .un op a => do
      match ← evalTerm inputs a with
      | .i x => pure (.i (match op with | .neg => -x | .succ => x + 1 | .pred => x - 1))
      | .s _ => none
  | .bin op a b => do
      let x ← evalTerm inputs a
      let y ← evalTerm inputs b
      let bool (c : Bool) : Option SymVal := pure (.i (if c then 1 else 0))
      match op, x, y with
      | .add, .i p, .i q => pure (.i (p + q))
      | .sub, .i p, .i q => pure (.i (p - q))
      | .mul, .i p, .i q => pure (.i (p * q))
      | .lt, .i p, .i q => bool (p < q)
      | .le, .i p, .i q => bool (p ≤ q)
      | .gt, .i p, .i q => bool (p > q)
      | .ge, .i p, .i q => bool (p ≥ q)
      | .or, .i p, .i q => bool (p != 0 || q != 0)
      | .and, .i p, .i q => bool (p != 0 && q != 0)
      -- equality is total across sorts (Ruby: `1 == "a"` is false, not an error)
      | .eq, _, _ => bool (x == y)
      | .ne, _, _ => bool (x != y)
      | _, _, _ => none

end SymTerm

/-! ## Operator recognition

    Names only — dispatch itself is never re-implemented here; §6.4's check
    confirms the guess against what the machine actually computed. -/

def unOpOf : String → Option UnOp
  | "-@" => some .neg | "succ" => some .succ | "pred" => some .pred
  | _ => none

/-- Zero-arg, deterministic, Int-returning methods. On an input-*independent*
    receiver their result is identical on every run, so it can be read off the
    machine and frozen as a `lit`. Deliberately a short whitelist: `rand`-like or
    address-dependent methods must never appear here, since the self-check cannot
    catch a wrongly-frozen literal (it only validates the current run). -/
def constIntMethod : String → Bool
  | "length" | "size" | "count" => true
  | _ => false

/-- Builtins that compare an argument against a collection's elements *internally*,
    so the comparison never surfaces as an observable `==`. For these, the
    collection's concrete elements are the interesting candidate domain
    (`search-and-proof.md` §2.3: "hash keys — bounded by the concrete key set"). -/
def collDomainMethod : String → Bool
  | "include?" | "member?" | "index" | "find_index" | "key?" | "has_key?"
  | "fetch" | "delete" | "count" | "rindex" | "assoc" => true
  | _ => false

/-- Cap on elements offered per collection, so a 10k-entry hash does not become
    10k candidate runs (`search-and-proof.md` §2.4 lists exactly this cost). When
    the cap bites it is reported on the frontier, never applied silently. -/
def collDomainCap : Nat := 16

def binOpOf : String → Option BinOp
  | "+" => some .add | "-" => some .sub | "*" => some .mul
  | "<" => some .lt | "<=" => some .le | ">" => some .gt | ">=" => some .ge
  | "==" => some .eq | "!=" => some .ne
  | _ => none

/-- The reserved input globals: `$__in0`, `$__in1`, … (§6.5). Name-distinctive,
    so recognizing them needs no node identity and cannot collide with a literal. -/
def inputIndexOf (name : String) : Option Nat :=
  if name.startsWith "$__in" then (name.drop 5).toString.toNat? else none

/-! ## Shadow state -/

/-- Mirror entry for one live kont. Only `argsK` needs a payload: it accumulates
    argument *values*, whose *terms* must ride alongside. -/
structure SymFrame where
  recvT : SymTerm := .opaque
  accT : List SymTerm := []
deriving Inhabited

structure SymState where
  /-- Term of the in-flight value. -/
  ctl : SymTerm := .opaque
  /-- Boolean term that is true exactly when the in-flight value is `nil`
      (`opaque` = we cannot say). This is what makes a *silent* nil source —
      one that produces no branch — visible to the solver at the send site that
      later dispatches on it. -/
  ctlNil : SymTerm := .opaque
  /-- Parallel to `m.kont`. -/
  mirror : List SymFrame := []
  /-- Locals, keyed by frame id (matches the model's frame store, so
      shared-scope closure locals are not a special case). -/
  locals : List ((FrameId × String) × SymTerm) := []
  /-- Nil-guards for locals, so a nil source survives being stored and re-read. -/
  localNils : List ((FrameId × String) × SymTerm) := []
  globals : List (String × SymTerm) := []
  notes : List String := []
deriving Inhabited

namespace SymState

def note (s : SymState) (msg : String) : SymState :=
  if s.notes.contains msg then s else { s with notes := s.notes ++ [msg] }

def getLocal (s : SymState) (fid : FrameId) (x : String) : SymTerm :=
  (s.locals.find? (fun e => e.1.1 == fid && e.1.2 == x)).map (·.2) |>.getD .opaque

def setLocal (s : SymState) (fid : FrameId) (x : String) (t : SymTerm) : SymState :=
  { s with locals := ((fid, x), t) ::
      s.locals.filter (fun e => !(e.1.1 == fid && e.1.2 == x)) }

/-- Read `x` the way the *machine* does: walk the block-frame `captured` chain into
    enclosing scopes (`Machine.getLocal`). Keying `locals` by `FrameId` is only half
    the story — a block body reads its enclosing method's locals, so the lookup has
    to walk too, or every closure-captured value silently goes `opaque`. That was
    costing the shadow every `{ |k| … outer … }` comparison. -/
def getLocalChain (s : SymState) (m : Machine) (x : String) : SymTerm :=
  let rec go : FrameId → Nat → SymTerm
    | _, 0 => .opaque
    | fid, fuel + 1 =>
      match s.locals.find? (fun e => e.1.1 == fid && e.1.2 == x) with
      | some e => e.2
      | none => match (m.frames.getD fid default).captured with
        | some p => go p fuel
        | none => .opaque
  go (m.stack.headD 0) (m.frames.size + 1)

/-- Nil-guard counterpart of `getLocalChain`. -/
def getLocalNilChain (s : SymState) (m : Machine) (x : String) : SymTerm :=
  let rec go : FrameId → Nat → SymTerm
    | _, 0 => .opaque
    | fid, fuel + 1 =>
      match s.localNils.find? (fun e => e.1.1 == fid && e.1.2 == x) with
      | some e => e.2
      | none => match (m.frames.getD fid default).captured with
        | some p => go p fuel
        | none => .opaque
  go (m.stack.headD 0) (m.frames.size + 1)

/-- Which frame owns `x`, mirroring `Machine.setLocal`: if some frame on the
    captured chain already binds it, assignment mutates *there* (shared closure
    locals); otherwise it is a new local in the current frame. -/
def ownerFrame (s : SymState) (m : Machine) (x : String) : FrameId :=
  let start := m.stack.headD 0
  let rec go : FrameId → Nat → FrameId
    | _, 0 => start
    | fid, fuel + 1 =>
      if s.locals.any (fun e => e.1.1 == fid && e.1.2 == x) then fid
      else match (m.frames.getD fid default).captured with
        | some p => go p fuel
        | none => start
  go start (m.frames.size + 1)

def getLocalNil (s : SymState) (fid : FrameId) (x : String) : SymTerm :=
  (s.localNils.find? (fun e => e.1.1 == fid && e.1.2 == x)).map (·.2) |>.getD .opaque

def setLocalNil (s : SymState) (fid : FrameId) (x : String) (t : SymTerm) : SymState :=
  { s with localNils := ((fid, x), t) ::
      s.localNils.filter (fun e => !(e.1.1 == fid && e.1.2 == x)) }

def getGlobal (s : SymState) (x : String) : SymTerm :=
  (s.globals.find? (·.1 == x)).map (·.2) |>.getD .opaque

def setGlobal (s : SymState) (x : String) (t : SymTerm) : SymState :=
  { s with globals := (x, t) :: s.globals.filter (·.1 != x) }

/-- Re-align the mirror to the post-state's kont depth. Pushes carry no payload
    (rules below fill them in); pops drop entries. This is what makes unhandled
    konts *safe*: they simply contribute no terms. -/
def realign (s : SymState) (depth : Nat) : SymState :=
  let cur := s.mirror.length
  if depth > cur then
    { s with mirror := (List.replicate (depth - cur) (default : SymFrame)) ++ s.mirror }
  else { s with mirror := s.mirror.drop (cur - depth) }

end SymState

/-! ## One shadow step -/

/-- A branch decision, with its condition as a term when one was tracked. -/
structure BranchEvent where
  kind : String
  taken : Bool
  cond : SymTerm
  deriving Inhabited

def BranchEvent.toJson (b : BranchEvent) : Json :=
  Json.mkObj [("kind", Json.str b.kind), ("taken", Json.bool b.taken),
              ("cond", SymTerm.toJson b.cond)]

/-- A **dispatch risk**: a send `recv.m` where, under some inputs, the receiver
    would be a *different class that does not define `m`* — i.e. a reachable
    `NoMethodError`. This is the general form of the bad-state query in
    `type-safety-by-reachability.md` §3/§9; `nil.to_sym` is merely its most common
    instance.

    Why it cannot be left to branch-flipping: the alternative class often arises
    *without a branch* (an out-of-range `Array#[]`, a `Hash` miss, a guarded `nil`
    return), so the same path simply carries a different value. `guard` is a boolean
    term that is true exactly when the receiver takes the bad class, so the engine
    can ask `pathCondition ∧ guard` directly.

    Currently the modeled alternative class is `NilClass` (by far the dominant one
    in practice); the structure generalizes to any class term. -/
structure DispatchRisk where
  /-- what makes the receiver take the bad class, e.g. `array_index_out_of_range` -/
  source : String
  /-- the method that would then be missing -/
  meth : String
  /-- the class the receiver would have (currently always `NilClass`) -/
  badClass : String
  /-- boolean term: true exactly when the receiver takes `badClass` -/
  guard : SymTerm
  deriving Inhabited

def DispatchRisk.toJson (r : DispatchRisk) : Json :=
  Json.mkObj [("source", Json.str r.source), ("meth", Json.str r.meth),
              ("badClass", Json.str r.badClass), ("guard", SymTerm.toJson r.guard)]

/-- **An observed comparison domain** (`search-and-proof.md` §2.3/§2.4).

    When an input is compared for equality against a value the shadow cannot express
    as a term — `k.name == base_class_name`, where `k.name` is a String produced by
    machinery we do not model — the *constraint* is lost, but the **concrete value
    that appeared on this run** is still observable. Recording it gives the engine a
    finite candidate domain: try each value the input was compared against, plus one
    value outside the set.

    Why this is sound where freezing a term would not be: a `DomainFact` is a
    *candidate input*, never a path-condition constraint. Every candidate is executed
    and its outcome comes from the semantics, so a wrong guess costs one iteration
    and nothing else. Freezing `k.name` as a literal, by contrast, would assert a
    fact about *other* runs that may not hold.

    This is deliberately an under-approximation — it sees only the comparisons this
    path performed. Per `search-and-proof.md` §2.2 that is acceptable for Direction A
    (missed witnesses, never false ones) and must never feed a safety claim. -/
structure DomainFact where
  /-- input indices appearing on the symbolic side of the comparison -/
  inputs : List Nat
  /-- the concrete value the *other* side had on this run -/
  value : SymVal
  /-- where it was observed, for reporting -/
  site : String
  deriving Inhabited

def DomainFact.toJson (d : DomainFact) : Json :=
  Json.mkObj [("inputs", Json.arr ((d.inputs.map (fun k => Json.num ⟨Int.ofNat k, 0⟩)).toArray)),
              ("value", d.value.toJson), ("site", Json.str d.site)]

/-- Input indices a term mentions. -/
partial def SymTerm.inputIdxs : SymTerm → List Nat
  | .inp k => [k]
  | .un _ a => a.inputIdxs
  | .bin _ a b => a.inputIdxs ++ b.inputIdxs
  | _ => []

/-- A machine value in one of the tracked sorts, if it is one. -/
def valueSym (h : Heap) : Value → Option SymVal
  | .int n => some (.i n)
  | .ref o => match (h.get o).payload with
    | .str s => some (.s s)
    | _ => none
  | _ => none

/-- The concrete integer the machine produced, if the post-state holds one. -/
def concreteInt (m' : Machine) : Option Int :=
  match m'.ctl with
  | .value (.int n) => some n
  | _ => none

/-- The concrete value the machine produced, in either tracked sort — the oracle
    for the self-check. Strings are heap objects, so this reads the payload. -/
def concreteVal (m' : Machine) : Option SymVal :=
  match m'.ctl with
  | .value (.int n) => some (.i n)
  | .value (.ref o) =>
    match (m'.heap.get o).payload with
    | .str s => some (.s s)
    | _ => none
  | _ => none

/-- **Self-check** (§6.4): a term assigned as `ctl` must evaluate, at the concrete
    inputs, to the value the machine actually produced. Mismatch ⇒ drop to
    `opaque` + note, so mirroring bugs cost precision, never soundness. -/
def checked (inputs : List SymVal) (s : SymState) (m' : Machine) (t : SymTerm)
    (site : String) : SymState :=
  match t, concreteVal m' with
  | .opaque, _ => { s with ctl := .opaque }
  | _, none => { s with ctl := t }   -- untracked sort: nothing to check against
  | _, some actual =>
    match SymTerm.evalTerm inputs t with
    | some predicted =>
      if predicted == actual then { s with ctl := t }
      else
        let s := s.note
          s!"SELF-CHECK FAILED at {site}: term={repr predicted} machine={repr actual} (term dropped)"
        { s with ctl := .opaque }
    | none => { s with ctl := t }

/-- **Param binding at method entry** (S2): a user method call pushes a frame whose
    `locals` are the parameter bindings, in order. We bind those names to the caller's
    argument *terms* positionally, so dataflow crosses the call boundary.

    Safety: we only bind when the shapes line up (equal length), and each binding is
    self-checked against the concrete value the machine stored — a mismatch records a
    note and drops that binding to `opaque` rather than asserting a wrong term. -/
def bindParams (inputs : List SymVal) (s : SymState) (m' : Machine)
    (argsT : List SymTerm) : SymState :=
  let fid := m'.stack.headD 0
  let f := m'.frames.getD fid default
  if f.locals.length != argsT.length then
    if argsT.any (·.hasInput) then
      s.note s!"param binding skipped (shape: {f.locals.length} locals vs {argsT.length} args)"
    else s
  else
    (f.locals.zip argsT).foldl (fun (st : SymState) (b : (String × Value) × SymTerm) =>
      let name := b.1.1
      -- the bound value may be either tracked sort; strings live on the heap
      let actual? : Option SymVal := match b.1.2 with
        | .int n => some (.i n)
        | .ref o => match (m'.heap.get o).payload with
          | .str str => some (.s str)
          | _ => none
        | _ => none
      match actual?, SymTerm.evalTerm inputs b.2 with
      | some actual, some predicted =>
        if predicted == actual then st.setLocal fid name b.2
        else (st.note s!"SELF-CHECK FAILED binding {name}: term={repr predicted} machine={repr actual} (dropped)").setLocal fid name .opaque
      | _, _ => st.setLocal fid name b.2) s

/-- Advance the shadow across one observed transition `m → m'`.
    Returns the new shadow state and a branch event if this step was a decision. -/
def symStep (inputs : List SymVal) (m m' : Machine) (s : SymState) :
    SymState × Option BranchEvent × Option DispatchRisk × List DomainFact :=
  let fid := m.stack.headD 0
  let s0 := { s.realign m'.kont.length with ctlNil := .opaque }
  match m.ctl, m.kont with
  -- ── expression evaluation ───────────────────────────────────────────────
  | .eval (.int n), _ => ({ s0 with ctl := .lit n }, none, none, [])
  -- a string literal is now a *term*, so `x == "lit"` is a real constraint
  | .eval (.str str), _ => ({ s0 with ctl := .slit str }, none, none, [])
  | .eval (.sym _), _ => ({ s0 with ctl := .conc }, none, none, [])
  | .eval .nil, _ => ({ s0 with ctl := .conc }, none, none, [])
  | .eval .tru, _ => ({ s0 with ctl := .conc }, none, none, [])
  | .eval .fls, _ => ({ s0 with ctl := .conc }, none, none, [])
  | .eval (.var .lvar x), _ =>
    ({ s0 with ctl := s.getLocalChain m x, ctlNil := s.getLocalNilChain m x },
     none, none, [])
  | .eval (.var .gvar x), _ =>
    -- the reserved input globals are the symbolic sources (§6.5)
    match inputIndexOf x with
    | some k => ({ s0 with ctl := .inp k }, none, none, [])
    | none => ({ s0 with ctl := s.getGlobal x }, none, none, [])
  -- ── value in flight: consume the top continuation ───────────────────────
  | .value _, (.asgnK .lvar x) :: _ =>
    -- assignment yields the assigned value: `ctl` and its nil-guard both survive
    let owner := s.ownerFrame m x
    (({ (s0.setLocal owner x s.ctl).setLocalNil owner x s.ctlNil with
          ctlNil := s.ctlNil }), none, none, [])
  | .value _, (.asgnK .gvar x) :: _ => ((s0.setGlobal x s.ctl), none, none, [])
  | .value _, (.recvK mname args _ _) :: _ =>
    -- Ask the *semantics* whether the alternative class defines `mname` — no
    -- duplicated method table here (cf. K9). Currently the modeled alternative is
    -- NilClass, which is the dominant real-world case.
    let risk : Option DispatchRisk :=
      if s.ctlNil.hasInput && (lookup m.heap Value.nil mname).isNone then
        some { source := "nil_source", meth := mname, badClass := "NilClass",
               guard := s.ctlNil }
      else none
    if args.isEmpty then
      -- zero-arg send: a unary primitive, or unknown
      match unOpOf mname with
      | some op => (checked inputs s0 m' (SymTerm.mkUn op s.ctl) s!"{mname}", none, risk, [])
      | none =>
        if s.ctl.isConst && constIntMethod mname then
          -- e.g. `[:a,:b,:c].length` -> lit 3, which makes a bounds guard
          -- `i < arr.length` solvable even though the collection is unmodeled.
          match concreteInt m' with
          | some n => ({ s0 with ctl := .lit n }, none, risk, [])
          | none => ({ s0 with ctl := .opaque }, none, risk, [])
        else
        -- A zero-arg *user method* pushes a frame; its body's term flows back out via
        -- the frameK passthrough, so nothing is lost and we must NOT cry frontier.
        -- An unmodeled *builtin* on a symbolic receiver DOES lose precision — report
        -- it, and attribute it, or the loss is silent (the string/`to_s` case).
        let userCall := m'.frames.size > m.frames.size
        let s1 := if !userCall && s.ctl.hasInput
                  then s0.note
                    s!"input-dependent `{mname}` not in the op map (term opaque)"
                  else s0
        ({ s1 with ctl := .opaque }, none, risk, [])
    else
      -- args follow: stash the receiver term on the incoming `argsK` mirror entry
      match s0.mirror with
      | f :: tl =>
        let f' : SymFrame := { f with recvT := s.ctl, accT := [] }
        ({ s0 with mirror := f' :: tl, ctl := .opaque }, none, risk, [])
      | [] => ({ s0 with ctl := .opaque }, none, risk, [])
  | .value argV, (.argsK recvV _ mname _ rest _) :: _ =>
    let entry := s.mirror.headD default
    let argsT := entry.accT ++ [s.ctl]
    if rest.isEmpty then
      -- all args in ⇒ this step dispatches; recognize a binary primitive
      match binOpOf mname, argsT with
      | some op, [argT] =>
        let t := SymTerm.mkBin op entry.recvT argT
        -- **Domain observation.** An equality we could not express as a term, where
        -- one side *is* input-dependent: the other side's concrete value on this run
        -- is a candidate input worth trying (`DomainFact`). This is what makes
        -- `k.name == base_class_name` productive even though `k.name` is opaque —
        -- we cannot say what `k.name` is in general, but we can see what it was.
        let dom : Option DomainFact :=
          match t, op with
          | .opaque, .eq | .opaque, .ne =>
            if argT.hasInput && !entry.recvT.hasInput then
              (valueSym m.heap recvV).map fun v =>
                { inputs := argT.inputIdxs, value := v, site := mname }
            else if entry.recvT.hasInput && !argT.hasInput then
              (valueSym m.heap argV).map fun v =>
                { inputs := entry.recvT.inputIdxs, value := v, site := mname }
            else none
          | _, _ => none
        (checked inputs s0 m' t s!"{mname}", none, none, dom.toList)
      | _, _ =>
        -- `arr[i]` with an input-dependent index over an array whose length is
        -- input-independent: out-of-range silently yields `nil`, which no branch
        -- reveals. Report it as a directed goal instead (see `NilRisk`).
        -- `arr[i]` with an input-dependent index over an input-independent array:
        -- out of range yields `nil` with NO branch, so record *when* that happens
        -- as a nil-guard on the result. The risk is raised later, at whatever send
        -- dispatches on this value — which is the general rule (see `DispatchRisk`).
        let nilGuard : SymTerm :=
          match mname, argsT, recvV with
          | "[]", [argT], .ref o =>
            if argT.hasInput && entry.recvT.isConst then
              match (m.heap.get o).payload with
              | .arr xs =>
                SymTerm.mkBin .or (SymTerm.mkBin .lt argT (.lit 0))
                                  (SymTerm.mkBin .ge argT (.lit (Int.ofNat xs.size)))
              -- Hash miss: `h[k]` yields nil when `k` is none of the (known,
              -- input-independent) keys AND the hash has no default. With a
              -- default the miss is not a nil source at all — ask the heap, do
              -- not assume.
              | .hsh pairs =>
                if (m.heap.get o).hashDflt.isSome then .opaque
                else
                  -- only integer keys are expressible as terms today; a
                  -- non-integer key means we cannot state the guard, so bail
                  -- rather than emit a partial (and therefore wrong) one.
                  if pairs.toList.all (fun kv => match kv.1 with | .int _ => true | _ => false)
                  then pairs.toList.foldl (fun acc kv =>
                        match kv.1 with
                        | .int k => SymTerm.mkBin .and acc (SymTerm.mkBin .ne argT (.lit k))
                        | _ => acc) (SymTerm.lit 1)
                  else .opaque
              | _ => .opaque
            else .opaque
          | _, _, _ => .opaque
        if !(nilGuard.isConst) && nilGuard.hasInput then
          ({ s0 with ctl := .opaque, ctlNil := nilGuard }, none, none, [])
        else
        if m'.frames.size > m.frames.size then
          -- a user method activation was pushed: carry arg terms into its params (S2)
          ({ bindParams inputs s0 m' argsT with ctl := .opaque }, none, none, [])
        else
          -- **Collection membership as a finite domain** (`search-and-proof.md`
          -- §2.3). `coll.include?(x)` / `coll.index(x)` with an input-dependent
          -- `x`: the comparison happens *inside* the builtin, so no `==` is ever
          -- observable and the branch on its result is unflippable. What we can do
          -- is read the collection's concrete elements and offer each as a
          -- candidate (the engine adds one value outside the set).
          --
          -- The receiver need NOT be input-independent: a `DomainFact` is a
          -- candidate, not a constraint, so a receiver that varies across runs
          -- costs at worst a wasted iteration. That freedom is exactly why
          -- candidate generation reaches cases constraint solving cannot.
          let doms : List DomainFact :=
            match argsT with
            | [argT] =>
              if argT.hasInput && collDomainMethod mname then
                let elems : List Value :=
                  match recvV with
                  | .ref o =>
                    match (m.heap.get o).payload with
                    | .arr xs => xs.toList
                    | .hsh pairs => pairs.toList.map (·.1)
                    | _ => []
                  | _ => []
                (elems.take collDomainCap).filterMap fun e =>
                  (valueSym m.heap e).map fun v =>
                    { inputs := argT.inputIdxs, value := v, site := mname }
              else []
            | _ => []
          -- No silent caps: if the collection was truncated, say so.
          let s1 := if doms.length == collDomainCap
                    then s0.note s!"domain for `{mname}` capped at {collDomainCap} elements"
                    else s0
          let s2 := if (entry.recvT.hasInput || argsT.any (·.hasInput)) && doms.isEmpty
                    then s1.note s!"input-dependent `{mname}` not in the op map (term opaque)"
                    else s1
          ({ s2 with ctl := .opaque }, none, none, doms)
    else
      -- more args to evaluate: carry the accumulated terms forward
      match s0.mirror with
      | f :: tl =>
        let f' : SymFrame := { f with recvT := entry.recvT, accT := argsT }
        ({ s0 with mirror := f' :: tl, ctl := .opaque }, none, none, [])
      | [] => ({ s0 with ctl := .opaque }, none, none, [])
  -- a method/block returning: its value's term passes through the boundary (S2)
  | .value _, (.frameK _) :: _ => (s0, none, none, [])
  | .value _, (.blkFrameK ..) :: _ => (s0, none, none, [])
  | .value _, (.seqK []) :: _ => (s0, none, none, [])
  | .value _, (.hshKeyK _ _ _) :: _ =>
    -- key evaluated: remember its term so the literal's const-ness can be judged
    let entry := s.mirror.headD default
    let f' : SymFrame := { entry with accT := entry.accT ++ [s.ctl] }
    let mirror' := f' :: s0.mirror.tail
    ({ s0 with mirror := mirror', ctl := .opaque }, none, none, [])
  | .value _, (.hshValK _ _ rest) :: _ =>
    -- value evaluated; on the last pair the hash is allocated in `m'`, and it is
    -- input-independent exactly when every key and value is
    let entry := s.mirror.headD default
    let partsT := entry.accT ++ [s.ctl]
    if rest.isEmpty then
      ({ s0 with ctl := if partsT.all SymTerm.isConst then .conc else .opaque },
       none, none, [])
    else
      let f' : SymFrame := { entry with accT := partsT }
      ({ s0 with mirror := f' :: s0.mirror.tail, ctl := .opaque }, none, none, [])
  | .value _, (.arrK _ rest) :: _ =>
    let entry := s.mirror.headD default
    let elemsT := entry.accT ++ [s.ctl]
    if rest.isEmpty then
      -- array allocated in `m'`: input-independent iff every element is
      ({ s0 with ctl := if elemsT.all SymTerm.isConst then .conc else .opaque }, none, none, [])
    else
      match s0.mirror with
      | f :: tl =>
        let f' : SymFrame := { f with accT := elemsT }
        ({ s0 with mirror := f' :: tl, ctl := .opaque }, none, none, [])
      | [] => ({ s0 with ctl := .opaque }, none, none, [])
  | .value v, (.ifK _ _) :: _ =>
    ({ s0 with ctl := .opaque },
     some { kind := "if", taken := v.truthy, cond := s.ctl }, none, [])
  | .value v, (.whileCondK _ _) :: _ =>
    ({ s0 with ctl := .opaque },
     some { kind := "while", taken := v.truthy, cond := s.ctl }, none, [])
  -- ── everything else: safe precision loss ───────────────────────────────
  | _, _ => ({ s0 with ctl := .opaque }, none, none, [])

/-- Initial shadow state for a run: bind the reserved input globals to `inp k`. -/
def initSym (inputs : List SymVal) : SymState :=
  { globals := (inputs.zipIdx).map (fun (_, k) => (s!"$__in{k}", SymTerm.inp k)) }

/-- Initial machine with the input globals preloaded — so **no AST rewriting** is
    needed to supply inputs (§6.5). -/
def initMachineOn (base : Machine) (inputs : List SymVal) : Machine :=
  -- String inputs are heap objects, so they must be allocated before binding;
  -- integers are immediates and need no heap.
  (inputs.zipIdx).foldl (fun (m : Machine) (vk : SymVal × Nat) =>
    let (v, k) := vk
    let (val, m) := match v with
      | .i n => (Value.int n, m)
      | .s str => Builtins.allocStr m str
    { m with globals := (s!"$__in{k}", val) :: m.globals })
    base

/-- Legacy entry point: inputs on a **bare** `Machine.init` heap, i.e. *without*
    the prelude. Kept only for tests that predate the prelude; the CLI now boots
    the prelude first (`initMachineOn`), so the tracer sees the same language the
    SUT does. Running the tracer on a bare heap silently loses everything the
    prelude provides (Enumerable, Comparable, Range enumeration …), which showed
    up as the tracer gating on `Array#any?` where the SUT was fine. -/
def initMachine (prog : Expr) (inputs : List SymVal) : Machine :=
  -- String inputs are heap objects, so they must be allocated before binding;
  -- integers are immediates and need no heap. Fold so each allocation threads
  -- through the machine it extends.
  (inputs.zipIdx).foldl (fun (m : Machine) (vk : SymVal × Nat) =>
    let (v, k) := vk
    let (val, m) := match v with
      | .i n => (Value.int n, m)
      | .s str => Builtins.allocStr m str
    { m with globals := (s!"$__in{k}", val) :: m.globals })
    (Machine.init prog)

end Concolic
end RubyCore
