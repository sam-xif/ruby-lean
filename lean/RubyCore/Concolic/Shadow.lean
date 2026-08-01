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
deriving Repr, DecidableEq

/-- A symbolic term over the inputs. `opaque` = not tracked (see header). -/
inductive SymTerm where
  | inp (k : Nat)
  | lit (n : Int)
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
  | .eq => "eq" | .ne => "ne" | .or => "or"

/-- Is this a comparison (boolean-valued)? Arithmetic is integer-valued. -/
def binIsCmp : BinOp → Bool
  | .add | .sub | .mul => false
  | _ => true

partial def toJson : SymTerm → Json
  | .inp k => Json.arr #[Json.str "inp", Json.num ⟨Int.ofNat k, 0⟩]
  | .lit n => Json.arr #[Json.str "lit", Json.num ⟨n, 0⟩]
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
  | .un _ a => hasInput a
  | .bin _ a b => hasInput a || hasInput b
  | .conc => false
  | .opaque => false

/-- Is this value the same on every run (independent of the inputs)? Only such
    values may have a concrete fact read off the machine and frozen as a `lit`. -/
def isConst : SymTerm → Bool
  | .lit _ => true
  | .conc => true
  | _ => false

/-! ### Smart constructors (constant-folding — KLEE's `ExprBuilder` discipline) -/

def mkUn (op : UnOp) (a : SymTerm) : SymTerm :=
  match a with
  | .conc => .opaque
  | .opaque => .opaque
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
  | _, _ => .bin op a b

/-- Evaluate at the concrete inputs — the self-check oracle (§6.4). Comparisons
    yield 1/0 so one `Int` result type covers both sorts. -/
partial def evalTerm (inputs : List Int) : SymTerm → Option Int
  | .inp k => inputs[k]?
  | .lit n => some n
  | .conc => none
  | .opaque => none
  | .un op a => (evalTerm inputs a).map fun x =>
      match op with | .neg => -x | .succ => x + 1 | .pred => x - 1
  | .bin op a b => do
      let x ← evalTerm inputs a
      let y ← evalTerm inputs b
      match op with
      | .add => pure (x + y) | .sub => pure (x - y) | .mul => pure (x * y)
      | .lt => pure (if x < y then 1 else 0)
      | .le => pure (if x ≤ y then 1 else 0)
      | .gt => pure (if x > y then 1 else 0)
      | .ge => pure (if x ≥ y then 1 else 0)
      | .eq => pure (if x == y then 1 else 0)
      | .ne => pure (if x != y then 1 else 0)
      | .or => pure (if x != 0 || y != 0 then 1 else 0)

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

/-- The concrete integer the machine produced, if the post-state holds one —
    the oracle for the self-check. -/
def concreteInt (m' : Machine) : Option Int :=
  match m'.ctl with
  | .value (.int n) => some n
  | _ => none

/-- **Self-check** (§6.4): a term assigned as `ctl` must evaluate, at the concrete
    inputs, to the value the machine actually produced. Mismatch ⇒ drop to
    `opaque` + note, so mirroring bugs cost precision, never soundness. -/
def checked (inputs : List Int) (s : SymState) (m' : Machine) (t : SymTerm)
    (site : String) : SymState :=
  match t, concreteInt m' with
  | .opaque, _ => { s with ctl := .opaque }
  | _, none => { s with ctl := t }   -- non-integer result: nothing to check against
  | _, some actual =>
    match SymTerm.evalTerm inputs t with
    | some predicted =>
      if predicted == actual then { s with ctl := t }
      else
        let s := s.note
          s!"SELF-CHECK FAILED at {site}: term={predicted} machine={actual} (term dropped)"
        { s with ctl := .opaque }
    | none => { s with ctl := t }

/-- **Param binding at method entry** (S2): a user method call pushes a frame whose
    `locals` are the parameter bindings, in order. We bind those names to the caller's
    argument *terms* positionally, so dataflow crosses the call boundary.

    Safety: we only bind when the shapes line up (equal length), and each binding is
    self-checked against the concrete value the machine stored — a mismatch records a
    note and drops that binding to `opaque` rather than asserting a wrong term. -/
def bindParams (inputs : List Int) (s : SymState) (m' : Machine)
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
      match b.1.2, SymTerm.evalTerm inputs b.2 with
      | .int actual, some predicted =>
        if predicted == actual then st.setLocal fid name b.2
        else (st.note s!"SELF-CHECK FAILED binding {name}: term={predicted} machine={actual} (dropped)").setLocal fid name .opaque
      | _, _ => st.setLocal fid name b.2) s

/-- Advance the shadow across one observed transition `m → m'`.
    Returns the new shadow state and a branch event if this step was a decision. -/
def symStep (inputs : List Int) (m m' : Machine) (s : SymState) :
    SymState × Option BranchEvent × Option DispatchRisk :=
  let fid := m.stack.headD 0
  let s0 := { s.realign m'.kont.length with ctlNil := .opaque }
  match m.ctl, m.kont with
  -- ── expression evaluation ───────────────────────────────────────────────
  | .eval (.int n), _ => ({ s0 with ctl := .lit n }, none, none)
  | .eval (.str _), _ => ({ s0 with ctl := .conc }, none, none)
  | .eval (.sym _), _ => ({ s0 with ctl := .conc }, none, none)
  | .eval .nil, _ => ({ s0 with ctl := .conc }, none, none)
  | .eval .tru, _ => ({ s0 with ctl := .conc }, none, none)
  | .eval .fls, _ => ({ s0 with ctl := .conc }, none, none)
  | .eval (.var .lvar x), _ =>
    ({ s0 with ctl := s.getLocal fid x, ctlNil := s.getLocalNil fid x }, none, none)
  | .eval (.var .gvar x), _ =>
    -- the reserved input globals are the symbolic sources (§6.5)
    match inputIndexOf x with
    | some k => ({ s0 with ctl := .inp k }, none, none)
    | none => ({ s0 with ctl := s.getGlobal x }, none, none)
  -- ── value in flight: consume the top continuation ───────────────────────
  | .value _, (.asgnK .lvar x) :: _ =>
    -- assignment yields the assigned value: `ctl` and its nil-guard both survive
    (({ (s0.setLocal fid x s.ctl).setLocalNil fid x s.ctlNil with
          ctlNil := s.ctlNil }), none, none)
  | .value _, (.asgnK .gvar x) :: _ => ((s0.setGlobal x s.ctl), none, none)
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
      | some op => (checked inputs s0 m' (SymTerm.mkUn op s.ctl) s!"{mname}", none, risk)
      | none =>
        if s.ctl.isConst && constIntMethod mname then
          -- e.g. `[:a,:b,:c].length` -> lit 3, which makes a bounds guard
          -- `i < arr.length` solvable even though the collection is unmodeled.
          match concreteInt m' with
          | some n => ({ s0 with ctl := .lit n }, none, risk)
          | none => ({ s0 with ctl := .opaque }, none, risk)
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
        ({ s1 with ctl := .opaque }, none, risk)
    else
      -- args follow: stash the receiver term on the incoming `argsK` mirror entry
      match s0.mirror with
      | f :: tl =>
        let f' : SymFrame := { f with recvT := s.ctl, accT := [] }
        ({ s0 with mirror := f' :: tl, ctl := .opaque }, none, risk)
      | [] => ({ s0 with ctl := .opaque }, none, risk)
  | .value _, (.argsK recvV _ mname _ rest _) :: _ =>
    let entry := s.mirror.headD default
    let argsT := entry.accT ++ [s.ctl]
    if rest.isEmpty then
      -- all args in ⇒ this step dispatches; recognize a binary primitive
      match binOpOf mname, argsT with
      | some op, [argT] =>
        (checked inputs s0 m' (SymTerm.mkBin op entry.recvT argT) s!"{mname}", none, none)
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
            if argT.hasInput then
              match (m.heap.get o).payload with
              | .arr xs =>
                SymTerm.mkBin .or (SymTerm.mkBin .lt argT (.lit 0))
                                  (SymTerm.mkBin .ge argT (.lit (Int.ofNat xs.size)))
              | _ => .opaque
            else .opaque
          | _, _, _ => .opaque
        if !(nilGuard.isConst) && nilGuard.hasInput then
          ({ s0 with ctl := .opaque, ctlNil := nilGuard }, none, none)
        else
        if m'.frames.size > m.frames.size then
          -- a user method activation was pushed: carry arg terms into its params (S2)
          ({ bindParams inputs s0 m' argsT with ctl := .opaque }, none, none)
        else
          let s1 := if entry.recvT.hasInput || argsT.any (·.hasInput)
                    then s0.note s!"input-dependent `{mname}` not in the op map (term opaque)"
                    else s0
          ({ s1 with ctl := .opaque }, none, none)
    else
      -- more args to evaluate: carry the accumulated terms forward
      match s0.mirror with
      | f :: tl =>
        let f' : SymFrame := { f with recvT := entry.recvT, accT := argsT }
        ({ s0 with mirror := f' :: tl, ctl := .opaque }, none, none)
      | [] => ({ s0 with ctl := .opaque }, none, none)
  -- a method/block returning: its value's term passes through the boundary (S2)
  | .value _, (.frameK _) :: _ => (s0, none, none)
  | .value _, (.blkFrameK _ _ _) :: _ => (s0, none, none)
  | .value _, (.seqK []) :: _ => (s0, none, none)
  | .value _, (.arrK _ rest) :: _ =>
    let entry := s.mirror.headD default
    let elemsT := entry.accT ++ [s.ctl]
    if rest.isEmpty then
      -- array allocated in `m'`: input-independent iff every element is
      ({ s0 with ctl := if elemsT.all SymTerm.isConst then .conc else .opaque }, none, none)
    else
      match s0.mirror with
      | f :: tl =>
        let f' : SymFrame := { f with accT := elemsT }
        ({ s0 with mirror := f' :: tl, ctl := .opaque }, none, none)
      | [] => ({ s0 with ctl := .opaque }, none, none)
  | .value v, (.ifK _ _) :: _ =>
    ({ s0 with ctl := .opaque },
     some { kind := "if", taken := v.truthy, cond := s.ctl }, none)
  | .value v, (.whileCondK _ _) :: _ =>
    ({ s0 with ctl := .opaque },
     some { kind := "while", taken := v.truthy, cond := s.ctl }, none)
  -- ── everything else: safe precision loss ───────────────────────────────
  | _, _ => ({ s0 with ctl := .opaque }, none, none)

/-- Initial shadow state for a run: bind the reserved input globals to `inp k`. -/
def initSym (inputs : List Int) : SymState :=
  { globals := (inputs.zipIdx).map (fun (_, k) => (s!"$__in{k}", SymTerm.inp k)) }

/-- Initial machine with the input globals preloaded — so **no AST rewriting** is
    needed to supply inputs (§6.5). -/
def initMachine (prog : Expr) (inputs : List Int) : Machine :=
  { Machine.init prog with
      globals := (inputs.zipIdx).map (fun (v, k) => (s!"$__in{k}", Value.int v)) }

end Concolic
end RubyCore
