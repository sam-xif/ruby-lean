/-
The machine configuration (artifact 00 §2, lean-model-sketch §3): an explicit
control state, a continuation (kont) stack, a frame *store* addressed by
FrameId with the activation stack as a list of ids (sketch §1.2 — Essence's
variable store and generative-jump-tag store unified), the heap, and the
effect accumulators the observation needs (stdout, $!).

Non-local control (artifact 04 §3) is a distinguished `jump` control state
that unwinds the kont stack, honoring marker konts (frame boundaries, begin
blocks with live rescues, while-loop markers) and running `ensure`s as it
passes them.
-/
import RubyCore.Heap

namespace RubyCore

abbrev FrameId := Nat

inductive FrameKind where
  | toplevel | method
deriving Repr, DecidableEq, Inhabited

structure Frame where
  self : Value
  locals : List (String × Value) := []
  /-- Module the enclosing `def` targets / `super` searches from (unused
      until L2 but load-bearing in the frame shape). -/
  defmod : ObjId
  blk : Option Value := none
  kind : FrameKind
deriving Inhabited

/-- In-flight non-local transfer (artifact 04 §3's `C^ctl` variants). -/
inductive Jump where
  | raiseJ (exc : Value)
  | retJ (v : Value)
  | brkJ (v : Value)
  | nxtJ (v : Value)
  | retryJ
deriving Inhabited

/-- What an `ensure` resumes when it finishes normally. -/
inductive Pending where
  | val (v : Value)
  | jmp (j : Jump)
deriving Inhabited

inductive Ctl where
  | eval (e : Expr)
  | value (v : Value)
  | jump (j : Jump)
deriving Inhabited

/-- Which jump a `return`/`break`/`next` value expression feeds. -/
inductive JumpKind where
  | retK | brkK | nxtK
deriving Repr, DecidableEq, Inhabited

/-- A begin/rescue/else/ensure region (kept whole for `retry`). -/
structure BeginNode where
  body : Expr
  rescues : List (List Expr × Option (TargetKind × String) × Expr)
  els : Option Expr
  ens : Option Expr
deriving Inhabited

inductive Kont where
  /-- Remaining statements of a `seq`; the in-flight value is discarded. -/
  | seqK (rest : List Expr)
  | asgnK (k : VarKind) (name : String)
  | casgnK (name : String)
  | ifK (t : Expr) (e : Option Expr)
  /-- Value is the while condition's result. Loop marker for brk/nxt. -/
  | whileCondK (c body : Expr)
  /-- Value is the while body's result (discarded). Loop marker. -/
  | whileBodyK (c body : Expr)
  /-- Got the receiver; evaluate args next. -/
  | recvK (m : String) (args : List Expr) (implicit : Bool)
  /-- Evaluating args left to right. -/
  | argsK (recv : Value) (implicit : Bool) (m : String)
      (acc : List Value) (rest : List Expr)
  /-- Value in flight is a `*e` splat operand of a send: spread it. -/
  | argsSplatK (recv : Value) (implicit : Bool) (m : String)
      (acc : List Value) (rest : List Expr)
  | arrK (acc : List Value) (rest : List Expr)
  /-- Value in flight is a `*e` splat operand of an array literal. -/
  | arrSplatK (acc : List Value) (rest : List Expr)
  | hshKeyK (acc : List (Value × Value)) (vExpr : Expr)
      (rest : List (Expr × Expr))
  | hshValK (acc : List (Value × Value)) (k : Value)
      (rest : List (Expr × Expr))
  /-- Value feeds `return`/`break`/`next`. -/
  | jumpValK (kind : JumpKind)
  /-- Method-activation boundary (generative jump target = frame identity,
      sketch §1.1). Pops `stack` on normal or unwinding passage. -/
  | frameK (fid : FrameId)
  /-- Begin body executing: rescues are live, node kept for retry/ensure. -/
  | beginBodyK (node : BeginNode)
  /-- Rescue-clause matching: evaluating candidate class exprs one at a
      time against in-flight `exc`. -/
  | rescMatchK (node : BeginNode) (exc : Value)
      (pendingExcs : List Expr) (ref : Option (TargetKind × String))
      (handler : Expr)
      (restClauses : List (List Expr × Option (TargetKind × String) × Expr))
  /-- Rescue handler executing (retry restarts node; ensure still pending).
      `savedExc` is the outer `$!`, restored when the handler exits [V]. -/
  | rescueK (node : BeginNode) (savedExc : Option Value)
  /-- Else clause executing (rescues no longer live; ensure pending). -/
  | elseK (node : BeginNode)
  /-- Ensure body executing; its value is discarded and `pending` resumes —
      unless the ensure itself jumps, which supersedes (artifact 04 §5).
      When pending is an in-flight raise, `$!` is set to it for the ensure's
      duration; `restore = some old` puts the previous `$!` back after [V]. -/
  | ensureK (pending : Pending) (restore : Option (Option Value) := none)
deriving Inhabited

structure Machine where
  ctl : Ctl
  kont : List Kont := []
  stack : List FrameId
  frames : Array Frame
  heap : Heap
  globals : List (String × Value) := []
  /-- Accumulated stdout (the observation's trace). -/
  out : String := ""
  /-- `$!` — the exception being handled (set on rescue entry). -/
  currentExc : Option Value := none
  /-- False once a user `def` shadows a repr-sensitive builtin
      (to_s/inspect/==/eql?/message/to_str); pure repr is then inadmissible
      and builtins that need it must answer Unsupported. -/
  reprPure : Bool := true
deriving Inhabited

namespace Machine

def currentFrame (m : Machine) : Frame :=
  match m.stack with
  | fid :: _ => m.frames.getD fid default
  | [] => default

def setCurrentFrame (m : Machine) (f : Frame) : Machine :=
  match m.stack with
  | fid :: _ => { m with frames := m.frames.set! fid f }
  | [] => m

def getLocal (m : Machine) (x : String) : Value :=
  match (m.currentFrame.locals.find? (·.1 == x)) with
  | some (_, v) => v
  | none => .nil

def setLocal (m : Machine) (x : String) (v : Value) : Machine :=
  let f := m.currentFrame
  m.setCurrentFrame
    { f with locals := (x, v) :: f.locals.filter (·.1 != x) }

def getGlobal (m : Machine) (x : String) : Value :=
  if x == "$!" then m.currentExc.getD .nil
  else
    match m.globals.find? (·.1 == x) with
    | some (_, v) => v
    | none => .nil

def setGlobal (m : Machine) (x : String) (v : Value) : Machine :=
  { m with globals := (x, v) :: m.globals.filter (·.1 != x) }

def emit (m : Machine) (s : String) : Machine :=
  { m with out := m.out ++ s }

/-- Initial machine for a program: H₀, one toplevel frame, self = main. -/
def init (program : Expr) : Machine :=
  let heap := Boot.initHeap
  let top : Frame :=
    { self := .ref Boot.mainId, defmod := Boot.objectId, kind := .toplevel }
  { ctl := .eval program,
    stack := [0],
    frames := #[top],
    heap }

end Machine

end RubyCore
