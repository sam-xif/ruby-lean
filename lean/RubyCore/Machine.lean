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
  | toplevel | method | block
  /-- A `class`/`module` body (artifact 01 §5): `self` and the `def`-target
      (`defmod`) are the class object; not a method activation. -/
  | classBody
deriving Repr, DecidableEq, Inhabited

structure Frame where
  self : Value
  locals : List (String × Value) := []
  /-- Module the enclosing `def` targets / `super` searches from (unused
      until L2 but load-bearing in the frame shape). -/
  defmod : ObjId
  /-- Lexical constant scope (cref): the enclosing class/module bodies at this
      point, innermost first (artifact 03 §4). Constant lookup checks each's own
      consts before the ancestor phase. A method carries the cref of where it was
      *defined* (not its dispatch owner — matters for `def self.m` in a module). -/
  cref : List ObjId := []
  blk : Option Value := none
  /-- The block the *call* supplied, kept separately from `blk` because a
      `define_method` body rebinds `blk` to its defining scope's (L66). Used only
      to answer "which active method was this proc passed to?" when a `break`
      leaves a proc invoked via `#call`. -/
  callBlk : Option Value := none
  kind : FrameKind
  /-- Name of the method this activation is running (`""` for toplevel/class
      bodies/blocks) — the target `super`/`zsuper` re-dispatch (artifact 02 §2). -/
  meth : String := ""
  /-- Block frames: the defining frame's id. Free-variable reads/writes walk
      this chain into the enclosing scope (sketch §1.2, artifact 03 §2). -/
  captured : Option FrameId := none
  /-- Block frames: the method activation a non-lambda `return` unwinds to. -/
  home : FrameId := 0
  /-- Block frames: lambda semantics (strict arity, local return/break). -/
  lam : Bool := false
  /-- Default visibility for `def`s in this class body — set by a bare `private`
      / `public` / `protected` (artifact 02 §5, L71). -/
  defVis : Visibility := .pub
deriving Inhabited

/-- In-flight non-local transfer (artifact 04 §3's `C^ctl` variants).
    `retJ` carries its target frame id — a method-body return targets the
    current method frame, a non-lambda block `return` its closure's `home`,
    a lambda its own frame (sketch §1.1: generativity = frame identity). -/
inductive Jump where
  | raiseJ (exc : Value)
  | retJ (v : Value) (target : FrameId)
  | brkJ (v : Value)
  | nxtJ (v : Value)
  | retryJ
  /-- `redo` — re-run the current loop body/iteration without re-testing the
      condition or advancing (artifact 04). -/
  | redoJ
  /-- `throw tag, v` (artifact 04, L69): unwinds to the matching `catch tag`.
      A tag-carrying transfer, so one Jump constructor covers every use. -/
  | throwJ (tag : Value) (v : Value)
deriving Inhabited

/-- What the call site looked like — needed for visibility (artifact 02 §5) and
    for the vcall/fcall `NameError` split (L71):
    - `implicit`: no receiver written (`m()`), so private methods are callable and
      a bare zero-arg miss is the vcall/fcall ambiguity;
    - `selfRecv`: a literal `self.m`, which may call private methods (Ruby 2.7+)
      but is unambiguously a method call;
    - `explicit`: any other receiver — visibility is enforced;
    - `reflective`: via `send`/`__send__`, which bypass visibility entirely
      (`public_send` uses `explicit`). -/
inductive SendSite where
  | implicit | selfRecv | explicit | reflective
  /-- A bare-identifier **vcall** (`foo`, not `foo()`). Identical to `implicit`
      for visibility and dispatch; differs only in the dispatch-*miss* error,
      which CRuby reports as `NameError: undefined local variable or method`
      rather than `NoMethodError: undefined method` (L75). -/
  | vcall
deriving Repr, DecidableEq, Inhabited

/-- A send's block child, carried through arg evaluation. A literal block is
    reified (capturing the caller frame) only once args are in; a `&e`
    block-pass is evaluated last (eval order) then coerced via `to_proc`. -/
inductive PendingBlk where
  | none
  | lit (params : List Param) (locals : List String) (body : Expr)
  | passExpr (e : Expr)
  | passAnon
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

/-- How a native block-iterator (`each`/`map`/`inject`/…) treats each block
    result and computes its final value. -/
inductive IterKind where
  | ignore    -- each / times / each_with_index: discard result, return `retVal`
  | collect   -- map / collect: gather results into a new Array
  | fold      -- inject / reduce: thread the accumulator (block gets `acc :: args`)
  | maxBy     -- max_by: keep the element whose block value is greatest
  | minBy     -- min_by: keep the element whose block value is least
deriving Repr, Inhabited

inductive Kont where
  /-- Remaining statements of a `seq`; the in-flight value is discarded. -/
  | seqK (rest : List Expr)
  | asgnK (k : VarKind) (name : String)
  | casgnK (name : String)
  /-- Value in flight is a `class C < S` superclass expression: with `S`
      resolved, open (or create) the class and run its body (artifact 01 §5). -/
  | classDefK (name : String) (body : Expr)
  /-- `Class#new` when the class has a user `initialize`: the in-flight value
      is `initialize`'s (discarded) result; yield the fresh instance instead
      (artifact 02 §3 — `new` = allocate ∘ initialize ∘ return self). -/
  | newK (inst : Value)
  /-- `def` fired the `Module#method_added` hook: the in-flight value is the
      hook's (discarded) result; `def` still evaluates to the method name
      (artifact 02 §6 — a definition hook is ordinary dispatch on the defining
      module, not a new evaluation rule). -/
  | methodAddedK (name : String)
  /-- `Array.try_convert(x)` dispatched `x.to_ary` (L72): the in-flight value is
      its result — an Array is the answer, nil is nil, anything else is a
      `TypeError` naming both classes. -/
  | tryConvertK (srcClass : String)
  /-- `raise C` / `raise C, msg` where `C` has a *user* `initialize` (L70): the
      in-flight value is that initializer's (discarded) result; raise the freshly
      built instance. -/
  | raiseNewK (inst : Value)
  /-- `include M` when `M` defines `self.included`: the in-flight value is the
      hook's (discarded) result; `include` evaluates to the receiver instead. -/
  | includeK (recv : Value)
  /-- `def RECV.name … end`: the in-flight value is the evaluated `RECV`; install
      the method on its eigenclass (artifact 01 §5, 02 §1). -/
  | defsK (name : String) (params : List Param) (body : Expr)
  /-- `class << OBJ … end`: the in-flight value is `OBJ`; run the body with
      `self`/cref = its eigenclass (artifact 01 §5). -/
  | sclassK (body : Expr)
  /-- `A::name` read: the in-flight value is the evaluated base `A`; resolve
      constant `name` in its namespace (artifact 03 §5). -/
  | cpathK (name : String)
  /-- `A::name = rhs`: the in-flight value is base `A`; evaluate `rhs` next. -/
  | cpathAsgnK (name : String) (rhs : Expr)
  /-- `A::name = rhs`: the in-flight value is `rhs`; assign into base's consts. -/
  | cpathAsgnValK (name : String) (base : ObjId)
  /-- `class/module A::name … end`: the in-flight value is base `A`; open (or
      create) `name` in its namespace and run the body. -/
  | scopedClassDefK (name : String) (isMod : Bool) (body : Expr)
  | ifK (t : Expr) (e : Option Expr)
  /-- Value is the while condition's result. Loop marker for brk/nxt. -/
  | whileCondK (c body : Expr)
  /-- Value is the while body's result (discarded). Loop marker. -/
  | whileBodyK (c body : Expr)
  /-- `for` collection evaluated: the in-flight value is the collection; begin
      iterating it (artifact 04). -/
  | forStartK (targets : List (TargetKind × String)) (body : Expr)
  /-- `for` body finished for one element (value discarded). Loop marker for
      brk/nxt; `rest` are the not-yet-visited elements, `coll` the loop value. -/
  | forBodyK (targets : List (TargetKind × String)) (body : Expr)
      (rest : List Value) (coll : Value)
  /-- A native block-iterator finished one block call. The in-flight value is the
      block's result; handle it per `kind`, then call the block for the next
      element (`rest` = remaining per-iteration arg lists) or deliver the final
      value. `cl` is the block, `brk` the iterator's activation frame (a `break`
      returns from it), `acc` the collect/fold accumulator, `retVal` the
      ignore-kind result. -/
  | iterK (cl : Closure) (brk : FrameId) (rest : List (List Value))
      (kind : IterKind) (acc : List Value) (retVal : Value) (cur : Value)
  /-- Got the receiver; evaluate args next. `blk` rides along to the dispatch. -/
  | recvK (m : String) (args : List Expr) (blk : PendingBlk) (implicit : SendSite)
  /-- Evaluating args left to right. -/
  | argsK (recv : Value) (implicit : SendSite) (m : String)
      (acc : List Value) (rest : List Expr) (blk : PendingBlk)
  /-- Value in flight is a `*e` splat operand of a send: spread it. -/
  | argsSplatK (recv : Value) (implicit : SendSite) (m : String)
      (acc : List Value) (rest : List Expr) (blk : PendingBlk)
  /-- Value in flight is a `&e` block-pass operand: coerce via to_proc, then
      dispatch (args + keywords already evaluated). -/
  | blkCoerceK (recv : Value) (implicit : SendSite) (m : String) (acc : List Value)
      (kw : List (Value × Value))
  /-- Evaluating a call-site `k: v` keyword value; then continue the kwargs. -/
  | kwPairK (key : String) (rest : List KwEntry) (kwacc : List (Value × Value))
      (recv : Value) (implicit : SendSite) (m : String) (posArgs : List Value) (pblk : PendingBlk)
  /-- Evaluating a call-site `**h` double-splat; then continue the kwargs. -/
  | kwSplatK (rest : List KwEntry) (kwacc : List (Value × Value))
      (recv : Value) (implicit : SendSite) (m : String) (posArgs : List Value) (pblk : PendingBlk)
  /-- Evaluating `yield` args left to right. -/
  | yieldArgK (acc : List Value) (rest : List Expr)
  | yieldSplatK (acc : List Value) (rest : List Expr)
  /-- Evaluating explicit `super(args)` left to right; `blk` is the block super
      forwards/passes (artifact 02 §2). -/
  | superArgK (acc : List Value) (rest : List Expr) (blk : Option Value)
  | superSplatK (acc : List Value) (rest : List Expr) (blk : Option Value)
  | arrK (acc : List Value) (rest : List Expr)
  /-- Value in flight is a `*e` splat operand of an array literal. -/
  | arrSplatK (acc : List Value) (rest : List Expr)
  | hshKeyK (acc : List (Value × Value)) (vExpr : Expr)
      (rest : List (Expr × Expr))
  | hshValK (acc : List (Value × Value)) (k : Value)
      (rest : List (Expr × Expr))
  /-- Value feeds `return`/`break`/`next`. -/
  | jumpValK (kind : JumpKind)
  /-- Evaluating an omitted optional param's default in the callee frame
      (artifact 02 §3). The in-flight value is the default for `name`; bind it,
      then evaluate the next omitted default (`rest`), and once all defaults are
      bound, install the post/rest/block bindings (`post`) and run `body`.
      (Post/rest/block bind *after* defaults — a default cannot see them [V].) -/
  | optDefK (name : String) (rest : List (String × Expr))
      (post : List (String × Value)) (body : Expr)
  /-- Method-activation boundary (generative jump target = frame identity,
      sketch §1.1). Pops `stack` on normal or unwinding passage. -/
  | frameK (fid : FrameId)
  /-- Block-activation boundary (artifact 04 §2). `lam` = lambda semantics;
      `brk` = the method activation a `break` returns from (`none` for a
      detached proc `.call`, where `break` is a LocalJumpError). Consumes
      `next` (block value) and a lambda-targeted `return`/`break`.
      `cl`/`args` are kept so `redo` can re-run this invocation from the top with
      the same arguments (L69). -/
  | blkFrameK (fid : FrameId) (lam : Bool) (brk : Option FrameId)
      (cl : Closure) (args : List Value)
  /-- `catch tag do … end` (L69): consumes a `throw` carrying an `equal?` tag,
      yielding its value. -/
  | catchK (tag : Value)
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
  /-- `defined?(recv.m)`: the in-flight value is the evaluated receiver; answer
      `"method"` or nil (artifact 03 §6, L67). -/
  | definedRecvK (mname : String)
  /-- `defined?(A::B)`: the in-flight value is the evaluated base; answer
      `"constant"` or nil. -/
  | definedCpathK (name : String)
  /-- `defined?` guard: any exception raised while evaluating that receiver/base
      makes the whole `defined?` nil [V] (`defined?(F.new.x)` with a raising
      `initialize` is nil), so this marker swallows an in-flight raise. -/
  | definedGuardK
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
  /-- True only while the **prelude** (the core library written in RubyCore,
      `prelude/prelude.rb`) is being loaded: methods defined in this phase are
      marked `fromPrelude` (L62). -/
  preludeMode : Bool := false
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

/-- Read `x`, walking the block-frame `captured` chain into enclosing scopes
    (sketch §1.2). Own locals (params, block-locals) shadow outer ones. -/
def getLocal (m : Machine) (x : String) : Value :=
  let rec go : FrameId → Nat → Value
    | _, 0 => .nil
    | fid, fuel + 1 =>
      let f := m.frames.getD fid default
      match f.locals.find? (·.1 == x) with
      | some (_, v) => v
      | none => match f.captured with
        | some p => go p fuel
        | none => .nil
  go (m.stack.headD 0) (m.frames.size + 1)

/-- Assign `x`. If some enclosing frame on the captured chain already binds it,
    mutate *there* (shared locals, artifact 03 §2); otherwise it is a new local
    in the current frame. -/
def setLocal (m : Machine) (x : String) (v : Value) : Machine :=
  let start := m.stack.headD 0
  let rec owner : FrameId → Nat → FrameId
    | _, 0 => start
    | fid, fuel + 1 =>
      let f := m.frames.getD fid default
      if f.locals.any (·.1 == x) then fid
      else match f.captured with
        | some p => owner p fuel
        | none => start
  let target := owner start (m.frames.size + 1)
  let f := m.frames.getD target default
  let f' := { f with locals := (x, v) :: f.locals.filter (·.1 != x) }
  { m with frames := m.frames.set! target f' }

/-- Is `x` bound as a local in the current frame or anywhere up its `captured`
    chain? (`getLocal` cannot answer this: an unbound read is also nil.) -/
def hasLocal (m : Machine) (x : String) : Bool :=
  let rec go : FrameId → Nat → Bool
    | _, 0 => false
    | fid, fuel + 1 =>
      let f := m.frames.getD fid default
      if f.locals.any (·.1 == x) then true
      else match f.captured with
        | some p => go p fuel
        | none => false
  go (m.stack.headD 0) (m.frames.size + 1)

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

/-- Initial machine for a program running on an already-booted heap `heap`
    (fresh frames/kont/stack; stdout and `$!` reset). Used for the two-phase
    prelude boot: phase 1 runs `prelude/prelude.rb` from H₀, phase 2 runs the
    program on the resulting heap (L62). `init` is `initOn Boot.initHeap`. -/
def initOn (heap : Heap) (program : Expr) : Machine :=
  let top : Frame :=
    { self := .ref Boot.mainId, defmod := Boot.objectId, kind := .toplevel,
      cref := [Boot.objectId] }
  { ctl := .eval program,
    stack := [0],
    frames := #[top],
    heap }

/-- Initial machine for a program: H₀, one toplevel frame, self = main. -/
def init (program : Expr) : Machine := initOn Boot.initHeap program

end Machine

end RubyCore
