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
deriving Repr, DecidableEq

/-- A symbolic term over the inputs. `opaque` = not tracked (see header). -/
inductive SymTerm where
  | inp (k : Nat)
  | lit (n : Int)
  | un (op : UnOp) (a : SymTerm)
  | bin (op : BinOp) (a b : SymTerm)
  | opaque
deriving Repr, Inhabited

namespace SymTerm

def unOpName : UnOp → String
  | .neg => "neg" | .succ => "succ" | .pred => "pred"

def binOpName : BinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul"
  | .lt => "lt" | .le => "le" | .gt => "gt" | .ge => "ge"
  | .eq => "eq" | .ne => "ne"

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
  | .opaque => Json.null

/-- Does the term mention an input? (Only such conditions are worth emitting —
    a purely-literal condition is not flippable.) -/
partial def hasInput : SymTerm → Bool
  | .inp _ => true
  | .lit _ => false
  | .un _ a => hasInput a
  | .bin _ a b => hasInput a || hasInput b
  | .opaque => false

/-! ### Smart constructors (constant-folding — KLEE's `ExprBuilder` discipline) -/

def mkUn (op : UnOp) (a : SymTerm) : SymTerm :=
  match a with
  | .opaque => .opaque
  | .lit n => match op with
    | .neg => .lit (-n) | .succ => .lit (n + 1) | .pred => .lit (n - 1)
  | _ => .un op a

/-- Arithmetic/comparison, folding when both sides are literals. Comparisons
    fold to `lit 1`/`lit 0` (see `evalTerm`: booleans are 1/0). -/
def mkBin (op : BinOp) (a b : SymTerm) : SymTerm :=
  match a, b with
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
  | _, _ => .bin op a b

/-- Evaluate at the concrete inputs — the self-check oracle (§6.4). Comparisons
    yield 1/0 so one `Int` result type covers both sorts. -/
partial def evalTerm (inputs : List Int) : SymTerm → Option Int
  | .inp k => inputs[k]?
  | .lit n => some n
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

end SymTerm

/-! ## Operator recognition

    Names only — dispatch itself is never re-implemented here; §6.4's check
    confirms the guess against what the machine actually computed. -/

def unOpOf : String → Option UnOp
  | "-@" => some .neg | "succ" => some .succ | "pred" => some .pred
  | _ => none

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
  /-- Parallel to `m.kont`. -/
  mirror : List SymFrame := []
  /-- Locals, keyed by frame id (matches the model's frame store, so
      shared-scope closure locals are not a special case). -/
  locals : List ((FrameId × String) × SymTerm) := []
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

/-- Advance the shadow across one observed transition `m → m'`.
    Returns the new shadow state and a branch event if this step was a decision. -/
def symStep (inputs : List Int) (m m' : Machine) (s : SymState) :
    SymState × Option BranchEvent :=
  let fid := m.stack.headD 0
  let s0 := s.realign m'.kont.length
  match m.ctl, m.kont with
  -- ── expression evaluation ───────────────────────────────────────────────
  | .eval (.int n), _ => ({ s0 with ctl := .lit n }, none)
  | .eval (.var .lvar x), _ => ({ s0 with ctl := s.getLocal fid x }, none)
  | .eval (.var .gvar x), _ =>
    -- the reserved input globals are the symbolic sources (§6.5)
    match inputIndexOf x with
    | some k => ({ s0 with ctl := .inp k }, none)
    | none => ({ s0 with ctl := s.getGlobal x }, none)
  -- ── value in flight: consume the top continuation ───────────────────────
  | .value _, (.asgnK .lvar x) :: _ =>
    -- assignment yields the assigned value, so `ctl` is unchanged
    ((s0.setLocal fid x s.ctl), none)
  | .value _, (.asgnK .gvar x) :: _ => ((s0.setGlobal x s.ctl), none)
  | .value _, (.recvK mname args _ _) :: _ =>
    if args.isEmpty then
      -- zero-arg send: a unary primitive, or unknown
      match unOpOf mname with
      | some op => (checked inputs s0 m' (SymTerm.mkUn op s.ctl) s!"{mname}", none)
      | none => ({ s0 with ctl := .opaque }, none)
    else
      -- args follow: stash the receiver term on the incoming `argsK` mirror entry
      match s0.mirror with
      | f :: tl =>
        let f' : SymFrame := { f with recvT := s.ctl, accT := [] }
        ({ s0 with mirror := f' :: tl, ctl := .opaque }, none)
      | [] => ({ s0 with ctl := .opaque }, none)
  | .value _, (.argsK _ _ mname _ rest _) :: _ =>
    let entry := s.mirror.headD default
    let argsT := entry.accT ++ [s.ctl]
    if rest.isEmpty then
      -- all args in ⇒ this step dispatches; recognize a binary primitive
      match binOpOf mname, argsT with
      | some op, [argT] =>
        (checked inputs s0 m' (SymTerm.mkBin op entry.recvT argT) s!"{mname}", none)
      | _, _ =>
        let s1 := if entry.recvT.hasInput || argsT.any (·.hasInput)
                  then s0.note s!"input-dependent `{mname}` not in the op map (term opaque)"
                  else s0
        ({ s1 with ctl := .opaque }, none)
    else
      -- more args to evaluate: carry the accumulated terms forward
      match s0.mirror with
      | f :: tl =>
        let f' : SymFrame := { f with recvT := entry.recvT, accT := argsT }
        ({ s0 with mirror := f' :: tl, ctl := .opaque }, none)
      | [] => ({ s0 with ctl := .opaque }, none)
  | .value v, (.ifK _ _) :: _ =>
    ({ s0 with ctl := .opaque },
     some { kind := "if", taken := v.truthy, cond := s.ctl })
  | .value v, (.whileCondK _ _) :: _ =>
    ({ s0 with ctl := .opaque },
     some { kind := "while", taken := v.truthy, cond := s.ctl })
  -- ── everything else: safe precision loss ───────────────────────────────
  | _, _ => ({ s0 with ctl := .opaque }, none)

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
