/-
The machine configuration (artifact 00 §2, `RubyCore/README.md` §Mechanization): an explicit
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
  /-- For callbacks have fresh control scopes but share this local environment. -/
  localAlias : Option FrameId := none
  /-- Target of an unqualified def/alias/undef in this environment. -/
  defmod : ObjId
  /-- Dispatch owner used by super, independently of the lexical definee. -/
  methodOwner : Option ObjId := none
  /-- Ordinary blocks and define_method bodies share their defining visibility
      scope. *_eval blocks instead start a fresh definition context. -/
  definitionFrame : Option FrameId := none
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
      bodies/blocks) — the target `super`/`zsuper` re-dispatch (artifact 02 §2).
      For an **alias** this is the *original* name, which is what CRuby's `super`
      searches for (L108). -/
  meth : String := ""
  superScope : Option ObjId := none
  /-- The running body's own parameter list, and whether it came from
      `define_method`. `zsuper` reconstructs its arguments from these; it used to
      re-look-up `meth` in `defmod`, which stopped working once `meth` could be an
      alias's original name and therefore find a *different* method (L108). -/
  runParams : List Param := []
  runFromDM : Bool := false
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
  /-- `$~` — the last match, which CRuby keeps **per frame**, not in a global
      (L121). A callee's match is therefore invisible to its caller, and `$1`…`$9`
      / `` $` `` / `$'` are views of *this* slot. -/
  lastMatch : Value := .nil
  /-- Do `$~` reads and writes in this activation resolve to the **caller's**
      slot? True for the prelude methods standing in for CRuby *C* functions,
      which write the frame of whoever called them (`String#sub`/`#gsub`/`#index`,
      `Regexp.last_match`); set by the `__match_to_caller` primitive as the first
      statement of such a body (L121). -/
  matchXparent : Bool := false
  /-- A native Enumerator fiber started at top level shares that environment's
      match slot. This does not capture its locals or its control stack. -/
  matchAlias : Option FrameId := none
  /-- Source origin, distinct from boot mode: library loading still runs hooks. -/
  libraryOrigin : Bool := false
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

/-- The already evaluated call awaiting `&operand` conversion (L275). -/
structure BlockPassCall where
  recv : Value
  site : SendSite
  name : String
  args : List Value
  kw : List (Value × Value)
deriving Inhabited

/-- Checked conversion's suspended user calls. A missing-method failure retains
    both response answers and the lookup owner, since redefinition during the
    handler affects whether its NoMethodError propagates (L275). -/
inductive BlockPassPhase where
  | start
  | respond
  | respondMissing (promised : Bool)
  | converted (direct : Bool)
  | missing (owner : ObjId) (respond : Bool) (respondMissing : Bool)
deriving Inhabited

/-- Rendering a receiver for FrozenError uses inspect, then rb_obj_as_string. -/
inductive FrozenPhase where
  | start | className
  | initialized (exc message : Value)
  | inspected (exc message : Value)
  | stringified (exc message source : Value)
deriving Inhabited

/-- A send's block child, carried through arg evaluation. A literal block is
    reified (capturing the caller frame) only once args are in; a `&e`
    block-pass is evaluated last (eval order) then coerced via `to_proc`. -/
inductive PendingBlk where
  | none
  | lit (params : List Param) (locals : List String) (body : Expr)
  | passExpr (e : Expr)
  | passAnon
deriving Inhabited

/-- The evaluation already completed around a splat operand. -/
inductive SplatCall where
  | args (recv : Value) (site : SendSite) (name : String) (acc : List Value)
      (rest : List Expr) (blk : PendingBlk)
  | superArgs (acc : List Value) (rest : List Expr) (blk : Option Value)
  | yieldArgs (acc : List Value) (rest : List Expr)
  | array (acc : List Value) (rest : List Expr)
deriving Inhabited

/-- The operation suspended while a Ruby conversion method runs. -/
inductive ConversionCall where
  | block (call : BlockPassCall)
  | stringPlus (recv : Value)
  | splat (call : SplatCall)
  | closureArgs (cl : Closure) (brk : Option FrameId)
      (selfOv : Option Value) (defmodOv : Option ObjId)
  | paramDestructure (subs : List Param) (remaining : List (Param × Value)) (body : Expr)
  | forDestructure (targets : List (TargetKind × String)) (body : Expr)
  | objectInspect
  | enumRewind (object : ObjId)
  | raiseString
  | stopMessage (result : Value)
  | raiseException (args : List Value)
  | exceptionString (viaToS : Bool)
  | constantSet (target : ObjId) (value : Value)
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
  /-- A native operation queues ordinary dispatch for the next transition. -/
  | send (recv : Value) (site : SendSite) (name : String) (args : List Value)
      (blk : Option Value) (kw : List (Value × Value))
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
  | times (limit index : Nat)
  | scan (object : ObjId) (revision : Nat) (subject pattern : String) (options index : Nat)
      (last : Option Value) (binary : Bool)
  | arrayEach (array : ObjId) (index : Nat) -- read the live payload after each yield
  | arrayIndex (array : ObjId) (index : Nat)
  | hashEach (hash : ObjId) (keys : List Value) (index mode : Nat)
  | arrayMap (array : ObjId) (index : Nat) -- live cursor, collect block results
  | ignore    -- each / times / each_with_index: discard result, return `retVal`
  | fold      -- inject / reduce: thread the accumulator (block gets `acc :: args`)
  | maxBy     -- max_by: keep the element whose block value is greatest
  | minBy     -- min_by: keep the element whose block value is least
deriving Repr, Inhabited

inductive MethodEdit where
  | define (target : ObjId) (name : String) (method : MethodDef)
  | aliasMethod (target : ObjId) (name original : String)
  | remove (target : ObjId) (name : String) (undefine : Bool)
  | visibility (target : ObjId) (name : String) (vis : Visibility)
  | moduleFunction (target : ObjId) (name : String)
deriving Inhabited

inductive Kont where
  | requireK (feature : String) (frame : FrameId)
  | enumFinishK (id : ObjId)
  | enumStopK (owner : Option ObjId) (exc result : Value)
  /-- Remaining statements of a `seq`; the in-flight value is discarded. -/
  | seqK (rest : List Expr)
  | asgnK (k : VarKind) (name : String)
  | casgnK (name : String)
  /-- Value in flight is a `class C < S` superclass expression: with `S`
      resolved, open (or create) the class and run its body (artifact 01 §5). -/
  | classDefK (name : String) (body : Expr)
  /-- A bound namespace waits for const_added before inherited and its body. -/
  | constClassK (klass : ObjId) (superclass : Option ObjId) (libraryName : String) (body : Expr)
  /-- A newly bound class sends inherited before entering its saved body. -/
  | classBodyK (klass : ObjId) (libraryName : String) (body : Expr)
  /-- Native Class#initialize waits for inherited before executing its block. -/
  | classInitK (klass : ObjId) (block : Option Value)
  /-- Native type diagnostics render the selected Class object's live to_s. -/
  | classNameErrorK (klass : ObjId) (lead tail : String)
  /-- An invalid constant-name argument is inspected, then converted to String. -/
  | constantNameErrorK (source : Option Value)
  /-- `Class#new`: the in-flight value is `initialize`'s (discarded) result;
      yield the allocated instance instead
      (artifact 02 §3 — `new` = allocate ∘ initialize ∘ return self). -/
  | newK (inst : Value)
  /-- A checked exception constructor returned; validate and raise its result. -/
  | raiseValueK
  | exceptionCopyK (copy message original : Value)
  /-- The call supplied a literal block. A break targets this boundary even
      through initialize, super, or further block forwarding. -/
  | blockCallK (scope : FrameId)
  | arrayInitK (recv : ObjId) (block : Value) (index size : Nat)
  /-- `def` fired the `Module#method_added` hook: the in-flight value is the
      hook's (discarded) result; `def` still evaluates to the method name
      (artifact 02 §6 — a definition hook is ordinary dispatch on the defining
      module, not a new evaluation rule). -/
  | methodAddedK (name : String)
  /-- Resume a native method-table operation after its Ruby callback. -/
  | methodEditsK (remaining : List MethodEdit) (result : Value)
  /-- A native error's initializer returned: discard its result and raise the
      freshly allocated instance (L286). -/
  | raiseNewK (inst : Value)
  | uncaughtInspectK (source : Option Value)
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
  | forStartK (targets : List (TargetKind × String)) (body : Expr) (multiple : Bool)
  /-- Assign the remaining for targets, then evaluate the body. -/
  | forAssignK (pending : List ((TargetKind × String) × Value)) (body : Expr)
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
  /-- Suspend a native operation during checked to_proc/to_str conversion. -/
  | blkConvertK (call : ConversionCall) (source : Value) (phase : BlockPassPhase)
  | frozenErrorK (recv : Value) (phase : FrozenPhase)
  /-- Evaluating a call-site `k: v` keyword value; then continue the kwargs. -/
  | kwPairK (key : String) (rest : List KwEntry) (kwacc : List (Value × Value))
      (recv : Value) (implicit : SendSite) (m : String) (posArgs : List Value) (pblk : PendingBlk)
  /-- Evaluating the *key* of a call-site `kExpr => v` pair; the value follows. -/
  | kwDynKeyK (valE : Expr) (rest : List KwEntry) (kwacc : List (Value × Value))
      (recv : Value) (implicit : SendSite) (m : String) (posArgs : List Value) (pblk : PendingBlk)
  /-- Evaluating the *value* of a call-site `kExpr => v` pair (key already in hand). -/
  | kwDynValK (key : Value) (rest : List KwEntry) (kwacc : List (Value × Value))
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
  | paramBindK (pending : List (Param × Value)) (body : Expr)
  | optDefK (name : String) (rest : List (String × Expr))
      (post : List (String × Value)) (body : Expr)
  /-- Method-activation boundary (generative jump target = frame identity,
      sketch §1.1). Pops `stack` on normal or unwinding passage. -/
  | frameK (fid : FrameId)
  /-- define_method retains block-local break/next/redo semantics. -/
  | dmFrameK (frame : FrameId) (body : Expr)
  | objectInspectK (recv filter : Value) (remaining : List String) (text : String)
      (stringifying : Option Value)
  /-- Block-activation boundary (artifact 04 §2). `lam` = lambda semantics;
      `brk` = the method activation a `break` returns from (`none` for a
      detached proc `.call`, where `break` is a LocalJumpError). Consumes
      `next` (block value) and a lambda-targeted `return`/`break`.
      `cl`/`args` retain the invocation descriptor. `redo` restarts cl.body in
      this same frame, preserving local writes and completed conversion (L277). -/
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

/-- CRuby retains the last failed call's reason in its execution context.
    The native method_missing reads it even through a user handler's super. -/
inductive MissingReason where
  | ordinary | vcall | privateCall | protectedCall | superCall
deriving Repr, DecidableEq, Inhabited

/-- A fiber owns control and dynamic context; heap, frame store, globals and
    output remain shared. Captured locals therefore survive suspension. -/
structure Execution where
  ctl : Ctl
  kont : List Kont
  stack : List FrameId
  currentExc : Option Value
  missingReason : MissingReason
  activeEnumerator : Option ObjId
deriving Inhabited

structure EnumState where
  suspended : Option Execution := none
  caller : Option Execution := none
  lookahead : Option (List Value) := none
  feed : Option Value := none
  /-- The first native StopIteration object, whose live message/result seed later errors. -/
  finished : Option Value := none
  peek : Bool := false
  values : Bool := false
deriving Inhabited

structure Machine where
  ctl : Ctl
  kont : List Kont := []
  stack : List FrameId
  frames : Array Frame
  heap : Heap
  enumerators : List (ObjId × EnumState) := []
  /-- Rewind abandons a fiber without running native Hash iteration cleanup.
      CRuby retains these insertion restrictions even after explicit GC. -/
  abandonedHashIterations : List ObjId := []
  activeEnumerator : Option ObjId := none
  /-- Frozen numeric literals are shared on repeated execution of one syntax
      site. Constructor calls allocate independently. Keys include the unit. -/
  numericLiterals : List (String × Value) := []
  globals : List (String × Value) := []
  /-- Accumulated stdout (the observation's trace). -/
  out : String := ""
  /-- `$!` — the exception being handled (set on rescue entry). -/
  currentExc : Option Value := none
  missingReason : MissingReason := .ordinary
  /-- True only while the **prelude** (the core library written in RubyCore,
      `prelude/prelude.rb`) is being loaded: methods defined in this phase are
      marked `fromPrelude` (L62). -/
  preludeMode : Bool := false
  featurePrograms : List (String × Expr) := []
  loadedFeatures : List String := ["pathname.so"]
  loadingFeatures : List String := []
  /-- A failed load can leave declarations behind; missing dependency APIs
      remain explicit gates even while the feature is eligible for retry. -/
  attemptedFeatures : List String := []
deriving Inhabited

namespace Machine

/-- Hash's insertion restriction survives external suspension. Normal unwind
    releases a live lock; abandoning the fiber retains it separately. -/
def hashIterationActive (m : Machine) (o : ObjId) : Bool :=
  let holds := fun (kont : List Kont) => kont.any fun k => match k with
    | .iterK _ _ _ (.hashEach h ..) _ _ _ => h == o
    | _ => false
  m.abandonedHashIterations.contains o || holds m.kont || m.enumerators.any fun (_, s) =>
    s.suspended.any (fun e => holds e.kont) || s.caller.any (fun e => holds e.kont)

def currentFrame (m : Machine) : Frame :=
  match m.stack with
  | fid :: _ => m.frames.getD fid default
  | [] => default

def setCurrentFrame (m : Machine) (f : Frame) : Machine :=
  match m.stack with
  | fid :: _ => { m with frames := m.frames.set! fid f }
  | [] => m

def definitionFrameId (m : Machine) (fid : FrameId) : FrameId :=
  go (m.frames.size + 1) fid
where
  go : Nat → FrameId → FrameId
    | 0, fid => fid
    | fuel + 1, fid =>
      match (m.frames.getD fid default).definitionFrame with
      | some parent => go fuel parent
      | none => fid

def currentDefinitionFrame (m : Machine) : Frame :=
  m.frames.getD (m.definitionFrameId (m.stack.headD 0)) default

def setDefinitionVisibility (m : Machine) (vis : Visibility) : Machine :=
  let fid := m.definitionFrameId (m.stack.headD 0)
  let f := m.frames.getD fid default
  -- Ruby warns and ignores bare visibility changes in an ordinary method.
  if f.kind == .method then m else
    { m with frames := m.frames.set! fid { f with defVis := vis } }

/-- Attribute/define_method macros use body visibility only for the matching
    class/eval scope. Top-level calls and calls targeting another class are public. -/
def macroVisibility (m : Machine) (target : ObjId) : Visibility :=
  let f := m.currentDefinitionFrame
  if f.kind != .toplevel && f.defmod == target then f.defVis else .pub

/-- Literal constants follow lexical nesting; *_eval does not change it. -/
def lexicalNamespace (m : Machine) : ObjId :=
  m.currentFrame.cref.headD Boot.objectId

/-- Follow for's local-environment alias without reviving an activation. -/
def localFrameId (m : Machine) (fid : FrameId) : FrameId :=
  go fid (m.frames.size + 1)
where
  go : FrameId → Nat → FrameId
    | fid, 0 => fid
    | fid, fuel + 1 => match (m.frames.getD fid default).localAlias with
      | some parent => go parent fuel
      | none => fid

/-- Read `x`, walking the block-frame `captured` chain into enclosing scopes
    (sketch §1.2). Own locals (params, block-locals) shadow outer ones. -/
def getLocal (m : Machine) (x : String) : Value :=
  let rec go : FrameId → Nat → Value
    | _, 0 => .nil
    | fid, fuel + 1 =>
      let fid := m.localFrameId fid
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
  let start := m.localFrameId (m.stack.headD 0)
  let rec owner : FrameId → Nat → FrameId
    | _, 0 => start
    | fid, fuel + 1 =>
      let fid := m.localFrameId fid
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
      let fid := m.localFrameId fid
      let f := m.frames.getD fid default
      if f.locals.any (·.1 == x) then true
      else match f.captured with
        | some p => go p fuel
        | none => false
  go (m.stack.headD 0) (m.frames.size + 1)

/-- Walk a block frame's `captured` chain to the activation that owns its `$~`
    slot. **Lexical, not dynamic**, and that is observable: a proc built in one
    method and `call`ed from another writes the frame it was *defined* in, so the
    calling method sees nothing [V]. The `dropWhile`-on-the-stack path in
    `matchFrameId` cannot answer that case, which is why this one exists. -/
def matchFrameOwner (m : Machine) : FrameId → Nat → FrameId
  | fid, 0 => fid
  | fid, fuel + 1 =>
    match (m.frames.getD fid default).matchAlias <|> (m.frames.getD fid default).captured with
    | some p => matchFrameOwner m p fuel
    | none => fid

/-- Which frame's `$~` slot the current control position reads and writes (L121).
    Three cases, one per way a frame can fail to own its own last match:

    * `matchXparent` (a prelude stand-in for a C function) → the **caller**, the
      frame below it on the stack;
    * a **block** → its *defining* frame, via `captured`. When that frame is still
      on the stack we continue from there, so a block inside a transparent method
      keeps resolving outward — that is how the block passed to the prelude
      `gsub` reads the very match `gsub` is making (L120);
    * anything else owns its slot. -/
def matchFrameId (m : Machine) : FrameId :=
  let rec go : List FrameId → Nat → FrameId
    | [], _ => 0
    | fid :: _, 0 => fid
    | fid :: rest, fuel + 1 =>
      let f := m.frames.getD fid default
      if f.matchXparent then
        match rest with
        | [] => fid          -- nothing below: keep the slot rather than lose the write
        | _ => go rest fuel
      else match f.matchAlias <|> f.captured with
        | some p =>
          match rest.dropWhile (· != p) with
          | [] => matchFrameOwner m p fuel
          | l => go l fuel
        | none => fid
  go m.stack (m.frames.size + 1)

/-- `$~`, read through `matchFrameId`. -/
def lastMatchValue (m : Machine) : Value :=
  (m.frames.getD m.matchFrameId default).lastMatch

/-- Write `$~` into the frame `matchFrameId` picks. -/
def setLastMatchValue (m : Machine) (v : Value) : Machine :=
  let fid := m.matchFrameId
  if fid < m.frames.size then
    { m with frames := m.frames.set! fid { m.frames.getD fid default with lastMatch := v } }
  else m

def getGlobal (m : Machine) (x : String) : Value :=
  if x == "$!" then m.currentExc.getD .nil
  -- `$~` is not in `globals` at all (L121); routing it here rather than at each
  -- read site keeps `Step.varGvar`'s "a gvar read is `getGlobal`" true, and picks
  -- up the views (`matchGlobal` reads `$~` through this) and `$~ = md` for free.
  else if x == "$~" then m.lastMatchValue
  else
    match m.globals.find? (·.1 == x) with
    | some (_, v) => v
    | none => .nil

def setGlobal (m : Machine) (x : String) (v : Value) : Machine :=
  if x == "$~" then m.setLastMatchValue v
  else { m with globals := (x, v) :: m.globals.filter (·.1 != x) }

def emit (m : Machine) (s : String) : Machine :=
  { m with out := m.out ++ s }

/-- Initial machine for a program running on an already-booted heap `heap`
    (fresh frames/kont/stack; stdout and `$!` reset). Used for the two-phase
    prelude boot: phase 1 runs `prelude/prelude.rb` from H₀, phase 2 runs the
    program on the resulting heap (L62). `init` is `initOn Boot.initHeap`. -/
def initOn (heap : Heap) (program : Expr) : Machine :=
  let top : Frame :=
    { self := .ref Boot.mainId, defmod := Boot.objectId, kind := .toplevel,
      defVis := .priv }
  { ctl := .eval program,
    stack := [0],
    frames := #[top],
    heap }

/-- Initial machine for a program: H₀, one toplevel frame, self = main. -/
def init (program : Expr) : Machine := initOn Boot.initHeap program

end Machine

end RubyCore
