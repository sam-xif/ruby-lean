import RubyCore.Builtins
import RubyCore.CRubyNames

/-!
Machine-level helpers: control/kont constructors, exception-region
bookkeeping, parameter classification and binding, splat spreading, the
return target, and closure creation/invocation.

Split out of `RubyCore/Interp.lean` (L99) with no behaviour change. The helpers
in this machine are deliberately *not* mutually recursive — each performs one
transition — so the file cuts along that existing order and the import chain
records it.
-/

namespace RubyCore

inductive StepResult where
  | next (m : Machine)
  | done (v : Value) (m : Machine)
  | uncaught (exc : Value) (m : Machine)
  | unsupported (reason : String)
  | stuck (msg : String)
deriving Inhabited

namespace Interp

def loaderGlobal (name : String) : Bool :=
  ["$LOADED_FEATURES", "$\"", "$LOAD_PATH", "$:", "$-I"].contains name

def lexicalConstant (m : Machine) (name : String) : Option Value :=
  (m.currentFrame.cref.firstM (fun k => constOwn m.heap k name)).orElse fun _ =>
    (constLookupFrom m.heap m.lexicalNamespace name).orElse fun _ =>
      if (m.heap.classPayload? m.lexicalNamespace).any (·.isModule) then
        constLookupFrom m.heap Boot.objectId name else none

def executionOf (m : Machine) : Execution :=
  ⟨m.ctl, m.kont, m.stack, m.currentExc, m.missingReason, m.activeEnumerator⟩

def restoreExecution (m : Machine) (e : Execution) : Machine :=
  { m with ctl := e.ctl, kont := e.kont, stack := e.stack, currentExc := e.currentExc, missingReason := e.missingReason, activeEnumerator := e.activeEnumerator }

def enumState (m : Machine) (o : ObjId) : EnumState :=
  ((m.enumerators.find? (·.1 == o)).map Prod.snd).getD {}

def libraryNamespace (h : Heap) (o : ObjId) : Option String :=
  (h.classPayload? o).bind (·.libraryNamespace)

def featureHas (table : List (String × List String)) (h : Heap) (o : ObjId) (name : String) : Bool :=
  ((libraryNamespace h o).bind fun ns => table.find? (·.1 == ns)).any (·.2.contains name)

def nativeSingletonMethod (h : Heap) (o : ObjId) (name : String) : Bool :=
  ((h.classPayload? o).bind (·.attached)).any
    (fun target => if target == Boot.mainId then crubyMainSingletonNames.contains name
      else crubySingletonDefines (className h target) name)

def featureMethod (h : Heap) (o : ObjId) (name : String) : Bool :=
  featureHas crubyFeatureMethods h o name ||
    ((h.classPayload? o).bind (·.attached)).any
      (fun target => featureHas crubyFeatureSingletonMethods h target name)

def unmodeledFeatureRoot (m : Machine) (name : String) : Bool :=
  m.attemptedFeatures.any fun f =>
    (crubyFeatureRoots.find? (·.1 == f)).any (·.2.contains name)

def unmodeledNamespaceConstant (m : Machine) (o : ObjId) (name : String) (inherit := true) : Bool :=
  (if inherit then ancestors m.heap o else [o]).any fun k =>
    ((crubyNamespaceConstants.find? (·.1 == className m.heap k)).map Prod.snd |>.getD []).contains name ||
    featureHas crubyFeatureConstants m.heap k name ||
    (k == Boot.objectId && (crubyStdlibConstants.contains name || unmodeledFeatureRoot m name))

def setEnumState (m : Machine) (o : ObjId) (s : EnumState) : Machine :=
  { m with enumerators := (o, s) :: m.enumerators.filter (·.1 != o) }

/-- Discarding a suspended fiber does not unwind its native Hash cleanup. -/
def resetEnumerator (m : Machine) (o : ObjId) : Machine :=
  let locks := ((enumState m o).suspended.map fun e => e.kont.filterMap fun k => match k with
    | .iterK _ _ _ (.hashEach h ..) _ _ _ => some h
    | _ => none).getD []
  setEnumState { m with abandonedHashIterations := locks ++ m.abandonedHashIterations } o {}

def allocEnumerator (m : Machine) (data : EnumData) (klass := Boot.enumeratorId) : Value × Machine :=
  let (o, h) := m.heap.alloc { klass, payload := .enumerator (some data) }
  (.ref o, { m with heap := h })

def enumPack (m : Machine) (args : List Value) (values : Bool) : Value × Machine :=
  if values then Builtins.allocArr m args.toArray else
  match args with
  | [] => (.nil, m)
  | [v] => (v, m)
  | _ => Builtins.allocArr m args.toArray

/-- A yield suspends exactly where the native callback was invoked. Frame store
    and heap remain shared; restoring the caller never replays Ruby effects. -/
def suspendEnumerator (m : Machine) (o : ObjId) (args : List Value) : StepResult :=
  let st := enumState m o
  match st.caller with
  | none => .unsupported "detached Enumerator yield callback"
  | some caller =>
    let execution := executionOf { m with ctl := .value .nil }
    let m := setEnumState m o { st with suspended := some execution, caller := none, lookahead := if st.peek then some args else none }
    let m := restoreExecution m caller
    let (v, m) := enumPack m args st.values
    .next { m with ctl := .value v }

def enumStop (m : Machine) (result : Value) : StepResult :=
  let (message, m) := Builtins.allocStr m "iteration reached an end"
  let (o, h) := m.heap.alloc { klass := Boot.stopIterationId, payload := .exc message, iterationResult := result }
  .next { m with heap := h, ctl := .jump (.raiseJ (.ref o)) }

def finishEnumerator (m : Machine) (o : ObjId) (result : Value) : StepResult :=
  let st := enumState m o
  match st.caller with
  | none => .stuck "Enumerator completion without a caller"
  | some caller =>
    let m := setEnumState m o { finished := some result }
    enumStop (restoreExecution m caller) result

def raiseErr (m : Machine) (cls : ObjId) (msg : String) : Machine :=
  let (v, m) := Builtins.allocExc m cls msg
  { m with ctl := .jump (.raiseJ v) }

def withCtl (m : Machine) (c : Ctl) : Machine := { m with ctl := c }

def withKont (m : Machine) (c : Ctl) (k : Kont) : Machine :=
  { m with ctl := c, kont := k :: m.kont }

/-- Suspend a rejected mutation to render its class and receiver. -/
def raiseFrozen (m : Machine) (recv : Value) : StepResult :=
  .next (withKont m (.value recv) (.frozenErrorK recv "" .start))

def bindIvar (m : Machine) (x : String) (v : Value) : Machine :=
  match m.currentFrame.self with
  | .ref o =>
    let obj := m.heap.get o
    let obj := { obj with ivars := (x, v) :: obj.ivars.filter (·.1 != x) }
    { m with heap := m.heap.set o obj }
  | _ => m

/-- Enter the ensure body (if any) with `pending` to resume; else resume
    pending immediately. While an ensure runs for an in-flight raise, `$!`
    is that exception [V] (test_exception_010). -/
def finishRegion (m : Machine) (ens : Option Expr) (pending : Pending) : Machine :=
  match ens with
  | some e =>
    match pending with
    | .jmp (.raiseJ exc) =>
      let saved := m.currentExc
      withKont { m with currentExc := some exc } (.eval e)
        (.ensureK pending (some saved))
    | _ => withKont m (.eval e) (.ensureK pending none)
  | none =>
    match pending with
    | .val v => withCtl m (.value v)
    | .jmp j => withCtl m (.jump j)

/-- Transfer control into a rescue handler: set `$!`, bind the `=> x`
    target, remember the outer `$!` for restore (artifact 04 §5). -/
def enterHandler (m : Machine) (node : BeginNode) (exc : Value)
    (ref : Option (TargetKind × String)) (handler : Expr) : Machine :=
  let saved := m.currentExc
  let m := { m with currentExc := some exc }
  let m := match ref with
    | some (.lvar, x) => m.setLocal x exc
    | some (.gvar, x) => m.setGlobal x exc
    | some (.ivar, x) => bindIvar m x exc
    | some (.const, n) => { m with heap := constSet m.heap n exc }
    | some (.cvar, _) => m   -- gated at begin' eval; unreachable
    | none => m
  withKont m (.eval handler) (.rescueK node saved)

/-- Advance rescue-clause matching for in-flight `exc` (artifact 04 §5).
    Clause exprs evaluate lazily, one at a time; an empty exc list is the
    default `[StandardError]` and needs no evaluation. -/
def nextClause (m : Machine) (node : BeginNode) (exc : Value)
    (clauses : List (List Expr × Option (TargetKind × String) × Expr)) : Machine :=
  match clauses with
  | [] => finishRegion m node.ens (.jmp (.raiseJ exc))
  | (excs, ref, handler) :: rest =>
    match excs with
    | [] =>
      if isA m.heap exc Boot.standardErrorId then
        enterHandler m node exc ref handler
      else nextClause m node exc rest
    | e :: es =>
      withKont m (.eval e) (.rescMatchK node exc es ref handler rest)

abbrev receiverDesc := RubyCore.receiverDesc

/-- Would CRuby find `mname` on some class of `chain` (per the generated
    name tables) even though our model doesn't define it there? -/
def crubyShadow (h : Heap) (chain : List ObjId) (mname : String) : Option String :=
  chain.firstM fun k =>
    let cname := className h k
    if crubyClassDefines cname mname || nativeSingletonMethod h k mname || featureMethod h k mname then some cname else none

/-- Class-aware allocation builtins model core singleton constructors too.
    Keep other shadow checks, including optional-library constructors. -/
def crubyResolvedShadow (h : Heap) (chain : List ObjId) (mname : String)
    (md : MethodDef) : Option String :=
  if md.builtin.any (["Class#new", "Module#new", "Class#allocate"].contains ·) then
    chain.firstM fun k =>
      let cname := className h k
      if crubyClassDefines cname mname || featureMethod h k mname then some cname else none
  else crubyShadow h chain mname

/-- For a *class object* receiver: would CRuby find `mname` on the class's
    singleton chain (e.g. `Hash.ruby2_keywords_hash`)? We have no
    explicit entries for every native singleton method. This fallback is for a
    lookup miss; resolved calls check the chain before their actual owner. -/
def crubySingletonShadow (h : Heap) (recv : Value) (mname : String) : Option String :=
  match recv with
  | .ref o =>
    if o == Boot.mainId && crubyMainSingletonNames.contains mname then some "main" else
    match (h.get o).payload with
    | .cls _ =>
      (ancestors h o).firstM fun k =>
        let cname := className h k
        if crubySingletonDefines cname mname || featureHas crubyFeatureSingletonMethods h k mname then some cname else none
    | _ => none
  | _ => none

/-- The legacy `(pre, rest?, post, block?)` binding shape for a param list that
    uses only `req`/`rest`/`block` kinds. -/
structure SimpleParams where
  pre : List String
  rest? : Option String
  post : List String
  block? : Option String

/-- Phase-2 increment-1 lowering: reduce a `List Param` to `SimpleParams` when it
    uses only the three already-modeled kinds (`req`/`rest`/`block`); any
    `opt`/`key`/`kwrest`/`fwd`/`destr` present returns `none`, so the caller
    gates Unsupported. Anonymous `*`/`&` lower to the name `""` (parity with the
    old sigil convention: `"*".drop 1 = ""`). Later increments replace this with
    native per-kind binding. -/
def classifySimple (ps0 : List Param) : Option SimpleParams :=
  let reqName : Param → Option String := fun p => match p with | .req n => some n | _ => none
  let (ps, block?) := match ps0.reverse with
    | (.block n) :: more => (more.reverse, some (n.getD ""))
    | _ => (ps0, none)
  if ps.any (fun p => match p with | .req _ | .rest _ => false | _ => true) then none
  else match ps.findIdx? (fun p => match p with | .rest _ => true | _ => false) with
    | none => some { pre := ps.filterMap reqName, rest? := none, post := [], block? }
    | some i =>
      let restName := match ps[i]! with | .rest n => n.getD "" | _ => ""
      some { pre := (ps.take i).filterMap reqName, rest? := some restName,
             post := (ps.drop (i + 1)).filterMap reqName, block? }

/-- Positional param structure including optionals (`req` / `opt` / `rest` /
    trailing `req` / `block`). Returns `none` if any keyword/`kwrest`/`fwd`/
    `destr` kind is present (still gated at this increment). Canonical Ruby
    order: leading required, optionals, `*rest`, trailing required, `&block`. -/
structure FullParams where
  pre : List String
  opt : List (String × Expr)
  rest? : Option String
  post : List String
  keys : List (String × Option Expr)   -- keyword params (name, default?)
  kwrest? : Option (Option String)     -- `**o` present? outer some, inner name
  block? : Option String
  -- destructuring params `(a, b)` carried as synthetic positional names paired
  -- with their sub-params; expanded after positional binding (P5).
  destrs : List (String × List Param) := []

/-- Reserved local names for `...` argument forwarding (`def m(...)`). -/
def fwdRest := "__fwd_rest"
def fwdKw := "__fwd_kw"
def fwdBlk := "__fwd_blk"

def classifyFull (ps0 : List Param) : Option FullParams :=
  -- `...` (pfwd) captures all remaining positional + keyword + block args:
  -- expand it to a synthetic `*__fwd_rest, **__fwd_kw, &__fwd_blk` (reuses the
  -- rest/kwrest/block machinery; `g(...)` re-expands from these locals).
  let ps0 := ps0.flatMap fun p => match p with
    | .fwd => [.rest (some fwdRest), .kwrest (some fwdKw), .block (some fwdBlk)]
    | _ => [p]
  -- destructuring params `(a,b)` occupy one positional slot each: replace with a
  -- synthetic required name and record the obligation, expanded post-binding (P5).
  let destrs := (ps0.zipIdx).filterMap fun (p, i) =>
    match p with | .destr subs => some (s!"__destr_{i}", subs) | _ => none
  let ps0 := (ps0.zipIdx).map fun (p, i) =>
    match p with | .destr _ => Param.req s!"__destr_{i}" | _ => p
  let (ps, block?) := match ps0.reverse with
    | (.block n) :: more => (more.reverse, some (n.getD ""))
    | _ => (ps0, none)
  -- fwd expanded, destr synthesized, keywords captured below: nothing left to gate
  if false then none
  else
    let isReq : Param → Bool := fun p => match p with | .req _ => true | _ => false
    let isOpt : Param → Bool := fun p => match p with | .opt _ _ => true | _ => false
    let isKey : Param → Bool := fun p => match p with | .key _ _ => true | _ => false
    let pre := ps.takeWhile isReq
    let a1 := ps.dropWhile isReq
    let optPs := a1.takeWhile isOpt
    let a2 := a1.dropWhile isOpt
    let (rest?, a3) := match a2 with
      | (.rest n) :: t => (some (n.getD ""), t)
      | _ => (none, a2)
    let post := a3.takeWhile isReq
    let a4 := a3.dropWhile isReq
    let keyPs := a4.takeWhile isKey
    let a5 := a4.dropWhile isKey
    let (kwrest?, a6) := match a5 with
      | (.kwrest n) :: t => (some n, t)
      | _ => (none, a5)
    if !a6.isEmpty then none  -- non-canonical order → gate
    else some {
      pre := pre.filterMap (fun p => match p with | .req n => some n | _ => none),
      opt := optPs.filterMap (fun p => match p with | .opt n d => some (n, d) | _ => none),
      rest?,
      post := post.filterMap (fun p => match p with | .req n => some n | _ => none),
      keys := keyPs.filterMap (fun p => match p with | .key n d => some (n, d) | _ => none),
      kwrest?, block?, destrs }

/-- The nesting depth of `.destr` sub-params, which is the fuel `destructureBind` needs. A
    plain structural recursion (and computable, unlike `sizeOf`, whose `SizeOf` instance has
    no LCNF signature). -/
def destrDepth : List Param → Nat
  | [] => 0
  | .destr subs :: ps => max (1 + destrDepth subs) (destrDepth ps)
  | _ :: ps => destrDepth ps

/-- Destructure `v` into a param list (`(a, *b, (c,d))`, massign-style): coerce
    `v` to an array (its elements if an Array, else wrap as `[v]`), bind leading
    positionals from the front, a `*rest` the middle, trailing positionals from
    the back; nested `(…)` recurse. Only req/rest/destr sub-params occur (P5).

    **Fuel-bounded, not `partial`** (clink 53). The recursion is on nested
    `.destr` sub-params but it goes through a `foldl`, so the decrease is not
    visible to the termination checker — which is why this was `partial def`,
    and a `partial def` compiles to an opaque constant with no equation lemmas,
    so *nothing* about it is provable. That blocked the continuation-framing
    metatheorem the semantic ladder (`Denote/Sem/`) needs
    (`Denote/Sem/notes.md` §The fifth stall point, item 3), which is the
    same trap `../../AGENTS.md` L73 warns about and the same fix `ancestors`
    already took (`Heap.lean` L73).
    Callers pass `destrDepth subs + 1` — the nesting depth *of the sub-list*
    plus the level being bound here — so the `0` arm is unreachable and the
    behaviour is unchanged. (`destrDepth` alone is off by one, and the symptom
    is a silent `nil` binding: `def f((a, b), c)` answered
    `NoMethodError: undefined method '+' for nil`. Caught by running it.) -/
def destructureBind (m : Machine) (subs : List Param) (v : Value)
    : Nat → List (String × Value) × Machine
  | 0 => ([], m)
  | fuel + 1 =>
  let vals := match v with
    | .ref o => match (m.heap.get o).payload with | .arr xs => xs.toList | _ => [v]
    | _ => [v]
  let isPos : Param → Bool := fun p => match p with | .rest _ => false | _ => true
  let preP := subs.takeWhile isPos
  let a1 := subs.dropWhile isPos
  let (rest?, postP) := match a1 with
    | (.rest n) :: t => (some n, t)
    | _ => (none, a1)
  let np := preP.length; let npost := postP.length; let n := vals.length
  let bindPos : List (String × Value) × Machine → Param × Value →
      List (String × Value) × Machine := fun (acc, m) (p, val) =>
    match p with
    | .req nm => (acc ++ [(nm, val)], m)
    | .destr subs' => let (bs, m) := destructureBind m subs' val fuel; (acc ++ bs, m)
    | _ => (acc, m)
  let (preB, m) := (preP.zip (vals.take np)).foldl bindPos ([], m)
  let (restB, m) := match rest? with
    | some (some rn) =>
      let mid := (vals.drop np).take (n - npost - np)
      let (rv, m) := Builtins.allocArr m mid.toArray; ([(rn, rv)], m)
    | _ => ([], m)
  let (postB, m) := (postP.zip (vals.drop (n - npost))).foldl bindPos ([], m)
  (preB ++ restB ++ postB, m)

/-- Ruby-3 keyword→positional collapse: when the callee has no keyword params, a
    trailing keyword bundle becomes one positional `Hash` argument (an *empty*
    bundle vanishes) [V]. Also used to feed builtins / method_missing, which
    receive keywords positionally in the model. -/
def appendKwHash (m : Machine) (args : List Value)
    (kw : List (Value × Value)) : List Value × Machine :=
  if kw.isEmpty then (args, m)
  else let (hv, m) := Builtins.allocHsh m kw.toArray; (args ++ [hv], m)

/-- Lookup a keyword by name among evaluated `(Symbol, Value)` pairs. -/
def kwLookup (kw : List (Value × Value)) (name : String) : Option Value :=
  (kw.find? (fun p => match p.1 with | .sym s => s == name | _ => false)).map (·.2)

/-- Render a `:a, :b` symbol list for missing/unknown-keyword `ArgumentError`s. -/
def kwNameList (names : List String) : String :=
  String.intercalate ", " (names.map (fun n => ":" ++ n))

/-- Is `name` a `private_constant` anywhere in `o`'s ancestry? Heap-only, and named for the
    continuation-framing proof: as the inline `let isPrivate := (ancestors …).any …` it was,
    `simp` normalises the `List.any` into an `∃` on the *pushed* side only (that side is the
    one the framing rewrites touch), the two `if` scrutinees stop being syntactically equal,
    and `split` sends the two sides down different arms — one reporting an uninitialized
    constant, the other a private one. -/
def isPrivateConst (h : Heap) (o : ObjId) (name : String) : Bool :=
  (ancestors h o).any fun a =>
    match h.classPayload? a with
    | some cp => cp.privateConsts.contains name
    | none => false

/-- The method activation governing the current frame (itself if a
    method/toplevel frame; its `home` if a block frame). -/
def methodFrameOf (m : Machine) : FrameId :=
  let fid := m.stack.headD 0
  match (m.frames.getD fid default).kind with
  | .block => (m.frames.getD fid default).home
  | _ => fid

/-- Target frame of a `return` evaluated in the current frame (artifact 04 §4):
    the method itself; a lambda block returns from itself; a non-lambda block
    from its closure's `home` method. -/
def returnTarget (m : Machine) : FrameId :=
  let fid := m.stack.headD 0
  let f := m.frames.getD fid default
  match f.kind with
  | .block => if f.lam then fid else f.home
  | _ => fid

/-- Perform a `return`: if the target return-scope is still on the stack, jump
    to it; otherwise the home method already exited (a detached non-lambda
    proc) — raise `LocalJumpError` *here*, at the call site, so an enclosing
    `rescue` can catch it (artifact 04 §4) [V]. -/
def doReturn (m : Machine) (v : Value) : StepResult :=
  let target := returnTarget m
  if m.stack.contains target then
    .next (withCtl m (.jump (.retJ v target)))
  else
    .next (raiseErr m Boot.localJumpErrorId "unexpected return")

/-- Reify a literal block into a Proc, capturing the current (caller) frame
    (artifact 04 §1; sketch §1.1/§1.2). -/
def reifyBlock (m : Machine) (params : List Param) (locals : List String) (body : Expr)
    (lam : Bool) : Value × Machine :=
  let cur := m.stack.headD 0
  -- `home` = the enclosing return-scope of the *definition* point: a method,
  -- or a lambda (lambdas are return-scopes), else walk out of plain blocks.
  -- This is exactly `returnTarget` evaluated at the defining frame — so a
  -- `proc { return }` created inside a lambda returns from that lambda [V].
  let home := returnTarget m
  let cl : Closure := { params, locals, body, captured := some cur, home, lam, libraryOrigin := m.currentFrame.libraryOrigin || m.preludeMode }
  let (o, h) := m.heap.alloc { klass := Boot.procId, payload := .proc cl }
  (.ref o, { m with heap := h })

/-- Bind break once, at the literal block's call site. The fresh tag uses a
    reserved frame-store slot without adding an activation or lexical scope. -/
def reifyCallBlock (m : Machine) (params : List Param) (locals : List String)
    (body : Expr) (lam : Bool) : Value × Machine :=
  let (v, m) := reifyBlock m params locals body lam
  let scope := m.frames.size
  let h := match v with
    | .ref o => match (m.heap.get o).payload with
      | .proc cl => m.heap.set o { m.heap.get o with payload := .proc { cl with breakScope := some scope } }
      | _ => m.heap
    | _ => m.heap
  (v, { m with heap := h, frames := m.frames.push m.currentFrame, kont := .blockCallK scope :: m.kont })

/-- The innermost active frame whose block *is* this proc — i.e. the method the
    block was passed to. `break` inside a proc called via `#call` returns from
    that method (and is a `LocalJumpError` once it has exited) [V], so this is
    the `brk` target for the `Proc#call` path (L66). -/
def blockOwner (m : Machine) (p : Value) : Option FrameId :=
  m.stack.find? fun fid =>
    match (m.frames.getD fid default).callBlk with
    | some b => b.identEq p
    | none => false

/-- Enter a closure after its argument conversions have completed. Keeping this
    separate prevents a one-element conversion result from being converted twice. -/
def enterClosure (m : Machine) (cl : Closure) (args : List Value)
    (brk : Option FrameId) (selfOv : Option Value := none)
    (defmodOv : Option ObjId := none) : StepResult :=
  match classifySimple cl.params with
  | none => .unsupported "unmodeled block param kind (optional/keyword/forwarding/destructuring)"
  | some sp =>
  let pre := sp.pre; let rest? := sp.rest?; let post := sp.post
  let required := pre.length + post.length
  let arityOk :=
    if cl.lam then
      match rest? with | some _ => args.length ≥ required | none => args.length == required
    else true
  if !arityOk then
    let expected := match rest? with | some _ => s!"{required}+" | none => toString required
    .next (raiseErr m Boot.argumentErrorId
      s!"wrong number of arguments (given {args.length}, expected {expected})")
  else
    let (locals, m) :=
      match rest? with
      | none =>
        let vals := (List.range pre.length).map (fun i => args.getD i .nil)
        (pre.zip vals, m)
      | some rname =>
        let preVals := (List.range pre.length).map (fun i => args.getD i .nil)
        let afterPre := args.drop pre.length
        let midCount := max 0 (afterPre.length - post.length)
        let midArgs := afterPre.take midCount
        let postSrc := afterPre.drop midCount
        let postVals := (List.range post.length).map (fun i => postSrc.getD i .nil)
        let (rv, m) := Builtins.allocArr m midArgs.toArray
        (pre.zip preVals ++ [(rname, rv)] ++ post.zip postVals, m)
    let locals := locals ++ cl.locals.map (fun n => (n, Value.nil))
    -- `getD 0` for a capture-free closure (`captured = none`, the `Symbol#to_proc`
    -- fiction — L266): reads the toplevel frame's `self`/`defmod`/`blk`/`cref`,
    -- exactly the frame this line read when the field was a bare `Nat` written `0`.
    -- What changed is the *pushed* frame's own `captured` below, which is now `none`.
    let capF := m.frames.getD (cl.captured.getD 0) default
    -- `selfOv`/`defmodOv` are the `instance_eval`/`class_eval` rebinding (L64):
    -- everything else about the block frame (captured chain, home, cref, lam) is
    -- unchanged, so free variables, `return` and constant lookup keep the
    -- block's own semantics while `self` / the `def` target move.
    let frame : Frame :=
      { self := selfOv.getD capF.self, defmod := defmodOv.getD capF.defmod,
        definitionFrame := if defmodOv.isSome then none else
          some (m.definitionFrameId (cl.captured.getD 0)),
        blk := capF.blk,
        locals, kind := .block, captured := cl.captured,
        home := cl.home, lam := cl.lam, cref := capF.cref, libraryOrigin := cl.libraryOrigin }
    let fid := m.frames.size
    let m := { m with frames := m.frames.push frame, stack := fid :: m.stack }
    .next (withKont m (.eval cl.body) (.blkFrameK fid cl.lam brk cl args))

/-- A lenient block with multiple positional slots expands its sole argument via
    checked to_ary. Lambdas and single/rest-only parameter shapes skip expansion. -/
def callClosure (m : Machine) (cl : Closure) (args : List Value)
    (brk : Option FrameId) (selfOv : Option Value := none)
    (defmodOv : Option ObjId := none) : StepResult :=
  let brk := match cl.breakScope with
    | none => brk
    | some scope => if m.kont.any (fun k => match k with
        | .blockCallK s => s == scope | _ => false) then some scope else none
  if let some o := cl.enumYield then suspendEnumerator m o args else
  match classifySimple cl.params with
  | none => .unsupported "unmodeled block param kind (optional/keyword/forwarding/destructuring)"
  | some sp =>
    let required := sp.pre.length + sp.post.length
    let autoSplat := !cl.lam && args.length == 1 &&
      (required ≥ 2 || (sp.rest?.isSome && required ≥ 1))
    if autoSplat then
      let source := args.headD .nil
      match Builtins.arrPayload? m.heap source with
      | some xs => enterClosure m cl xs.toList brk selfOv defmodOv
      | none => .next (withKont m (.value source)
          (.blkConvertK (.closureArgs cl brk selfOv defmodOv) source .start))
    else enterClosure m cl args brk selfOv defmodOv

def procCallBid (bid : String) : Bool :=
  bid == "Proc#call" || bid == "Proc#[]" || bid == "Proc#yield"

/-- String#+ keeps native payload concatenation for two Strings; other operands
    suspend the resolved operation while checked to_str conversion runs. -/
def callStringPlusBuiltin (m : Machine) (recv : Value) (args : List Value)
    (kw : List (Value × Value)) : StepResult :=
  let (args, m) := appendKwHash m args kw
  match args with
  | [source] =>
    if (Builtins.strPayload? m.heap source).isNone then
      .next (withKont m (.value source) (.blkConvertK (.stringPlus recv) source .start))
    else
      match Builtins.run "String#+" recv args m with
      | .ok v m => .next (withCtl m (.value v))
      | .err cls msg m => .next (raiseErr m cls msg)
      | .throwV v m => .next (withCtl m (.jump (.raiseJ v)))
      | .frozen recv m => raiseFrozen m recv
      | .unsupported r => .unsupported r
  | _ => .next (raiseErr m Boot.argumentErrorId
      s!"wrong number of arguments (given {args.length}, expected 1)")

/-- Execute a resolved Proc call marker, after normal lookup/visibility checks (L272).
Aliases retain the marker; singleton overrides and undef never reach this helper. -/
def callProcBuiltin (m : Machine) (recv : Value) (args : List Value)
    (kw : List (Value × Value)) : StepResult :=
  match recv with
  | .ref o =>
    match (m.heap.get o).payload with
    | .proc cl =>
      if kw.isEmpty then callClosure m cl args (blockOwner m recv)
      else .unsupported "keyword arguments to a Proc call"
    | _ => .unsupported "Proc call builtin without a Proc payload"
  | _ => .unsupported "Proc call builtin without a Proc receiver"

/-- The `$~`-view read itself. `none` for any other global name, so the ordinary
    path is untouched. -/
def matchGlobal (m : Machine) (x : String) : Option (Value × Machine) :=
  let idx? := matchViewIdx? x
  let pre := x == "$`"
  let post := x == "$'"
  if !isMatchView x then none
  else
    match m.getGlobal "$~" with
    | .ref o =>
      match (m.heap.get o).payload with
      | .mdata subject caps _ =>
        let bin := (m.heap.get o).binary
        let slice (a b : Nat) : Value × Machine :=
          Builtins.allocStrEnc m (Builtins.charSlice subject a b) bin
        match caps[0]? with
        | some (some (wa, wb)) =>
          if pre then some (slice 0 wa)
          else if post then some (slice wb subject.length)
          else match idx? with
            | some i =>
              match caps[i]? with
              | some (some (a, b)) => some (slice a b)
              | _ => some (.nil, m)
            | none => some (.nil, m)
        | _ => some (.nil, m)
      | _ => some (.nil, m)
    | _ => some (.nil, m)


end Interp

end RubyCore
