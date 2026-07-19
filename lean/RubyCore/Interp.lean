/-
The executable step function (lean-model-sketch §3): `stepFn` is one
small-step transition of the machine; `run` iterates it under fuel.

The inductive `Step : Config → Config → Prop` (the definition of record)
will be authored against this — `stepFn` is its constructive witness; for
now the interpreter comes first so the model can meet the difftest engine
immediately (sketch §4). Note the helpers below are NOT mutually recursive:
each performs exactly one transition — evidence the machine really is
small-step.

Out-of-fragment RubyCore constructs surface as `.unsupported` — the SUT
contract's clean gate, never a guessed value.
-/
import RubyCore.Builtins
import RubyCore.CRubyNames

namespace RubyCore

inductive StepResult where
  | next (m : Machine)
  | done (v : Value) (m : Machine)
  | uncaught (exc : Value) (m : Machine)
  | unsupported (reason : String)
  | stuck (msg : String)
deriving Inhabited

namespace Interp

/-- User `def`s of these names shadow builtins that pure repr silently
    assumes; flip `reprPure` when one lands (Builtins.pureOk gates). -/
def reprSensitive : List String :=
  ["to_s", "inspect", "==", "eql?", "message", "to_str"]

def raiseErr (m : Machine) (cls : ObjId) (msg : String) : Machine :=
  let (v, m) := Builtins.allocExc m cls msg
  { m with ctl := .jump (.raiseJ v) }

def withCtl (m : Machine) (c : Ctl) : Machine := { m with ctl := c }

def withKont (m : Machine) (c : Ctl) (k : Kont) : Machine :=
  { m with ctl := c, kont := k :: m.kont }

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

/-- How a NoMethodError describes its receiver [V]:
    main / nil / true / false literally; classes as "class C";
    everything else "an instance of C". -/
def receiverDesc (h : Heap) (v : Value) : String :=
  match v with
  | .nil => "nil"
  | .bool b => toString b
  | .ref o =>
    if o == Boot.mainId then "main"
    else match (h.get o).payload with
      | .cls c => (if c.isModule then "module " else "class ") ++ c.name
      | _ => s!"an instance of {className h (h.get o).klass}"
  | _ => s!"an instance of {className h (classOf h v)}"

/-- Would CRuby find `mname` on some class of `chain` (per the generated
    name tables) even though our model doesn't define it there? -/
def crubyShadow (h : Heap) (chain : List ObjId) (mname : String) : Option String :=
  chain.firstM fun k =>
    let cname := className h k
    if crubyClassDefines cname mname then some cname else none

/-- For a *class object* receiver: would CRuby find `mname` on the class's
    singleton chain (e.g. `Hash.ruby2_keywords_hash`)? We have no
    eigenclasses yet, so any singleton hit is unmodeled. Only consulted when
    our lookup did NOT resolve to a builtin (our class-aware builtins like
    Class#new deliberately subsume the common singleton constructors). -/
def crubySingletonShadow (h : Heap) (recv : Value) (mname : String) : Option String :=
  match recv with
  | .ref o =>
    match (h.get o).payload with
    | .cls _ =>
      (ancestors h o).firstM fun k =>
        let cname := className h k
        if crubySingletonDefines cname mname then some cname else none
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

/-- Destructure `v` into a param list (`(a, *b, (c,d))`, massign-style): coerce
    `v` to an array (its elements if an Array, else wrap as `[v]`), bind leading
    positionals from the front, a `*rest` the middle, trailing positionals from
    the back; nested `(…)` recurse. Only req/rest/destr sub-params occur (P5). -/
partial def destructureBind (m : Machine) (subs : List Param) (v : Value)
    : List (String × Value) × Machine :=
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
    | .destr subs' => let (bs, m) := destructureBind m subs' val; (acc ++ bs, m)
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

/-- Spread a splat operand [V]: array splices, nil vanishes, anything else
    (without to_a) is itself. Hash's pair-conversion is gated for now. -/
def spread (m : Machine) (v : Value) : Except String (List Value) :=
  match v with
  | .ref o =>
    match (m.heap.get o).payload with
    | .arr xs => .ok xs.toList
    | .hsh _ => .error "splat of a Hash (to_a pairs)"
    | _ =>
      -- CRuby splats a non-Array via `to_a` if it responds; a *user* `to_a`
      -- is a side-effecting dispatch a pure spread can't run → gate.
      match lookup m.heap v "to_a" with
      | some (_, md) => if md.builtin.isNone then .error "splat via user to_a (dispatch)" else .ok [v]
      | none => .ok [v]
  | .nil => .ok []
  | _ => .ok [v]

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
  let cl : Closure := { params, locals, body, captured := cur, home, lam }
  let (o, h) := m.heap.alloc { klass := Boot.procId, payload := .proc cl }
  (.ref o, { m with heap := h })

/-- Coerce a `&e` block-pass operand: a Proc is used directly, `nil` means no
    block, a Symbol builds `:m.to_proc`; anything else gates (`to_proc`
    dispatch is out of L1). -/
def coerceToProc (m : Machine) (v : Value) : Except String (Option Value × Machine) :=
  match v with
  | .nil => .ok (none, m)
  | .ref o =>
    match (m.heap.get o).payload with
    | .proc _ => .ok (some v, m)
    | _ => .error "block-pass of a non-Proc (to_proc dispatch is L2)"
  | .sym s =>
    -- `:m.to_proc` ≈ `->(x, *a){ x.m(*a) }` — lambda-like so it does NOT
    -- auto-splat an Array receiver (`[[1,2]].map(&:first)` → `[1,2].first`).
    let cl : Closure :=
      { params := [.req "__recv", .rest (some "__rest")], locals := [],
        body := .send (some (.var .lvar "__recv")) s
                  [.splat (some (.var .lvar "__rest"))] none,
        captured := 0, home := 0, lam := true }
    let (o, h) := m.heap.alloc { klass := Boot.procId, payload := .proc cl }
    .ok (some (.ref o), { m with heap := h })
  | _ => .error "block-pass of a non-Proc"

/-- Invoke a closure: push a block frame parented at `captured`, bind params
    (lenient for blocks/procs — pad nil, drop extras, auto-splat a single
    Array across ≥2 positionals; strict for lambdas), evaluate the body under
    a `blkFrameK` marker (artifact 04 §2). `brk` is the method a `break`
    returns from. -/
def callClosure (m : Machine) (cl : Closure) (args : List Value)
    (brk : Option FrameId) : StepResult :=
  let sp? := classifySimple cl.params
  if sp?.isNone then
    .unsupported "unmodeled block param kind (optional/keyword/forwarding/destructuring)"
  else
  let sp := sp?.getD ⟨[], none, [], none⟩
  let pre := sp.pre; let rest? := sp.rest?; let post := sp.post
  let required := pre.length + post.length
  let args :=
    if !cl.lam && args.length == 1 && (required ≥ 2 || (rest?.isSome && required ≥ 1)) then
      match args.head? with
      | some (.ref o) => match (m.heap.get o).payload with
        | .arr xs => xs.toList
        | _ => args
      | _ => args
    else args
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
    let capF := m.frames.getD cl.captured default
    let frame : Frame :=
      { self := capF.self, defmod := capF.defmod, blk := capF.blk,
        locals, kind := .block, captured := some cl.captured,
        home := cl.home, lam := cl.lam, cref := capF.cref }
    let fid := m.frames.size
    let m := { m with frames := m.frames.push frame, stack := fid :: m.stack }
    .next (withKont m (.eval cl.body) (.blkFrameK fid cl.lam brk))

/-- First module in `ancestors k` defining `m` directly, with its owner — like
    `lookup` but keyed on a class ObjId rather than a receiver value (used to
    inspect a class before any instance of it exists, e.g. for `initialize`). -/
def methodOn (h : Heap) (k : ObjId) (mname : String) : Option (ObjId × MethodDef) :=
  (ancestors h k).firstM fun c =>
    match h.classPayload? c with
    | some cp => (cp.methods.find? (·.1 == mname)).map (fun (_, md) => (c, md))
    | none => none

/-- The user-defined `initialize` an instance of class `k` would run, if any
    (a builtin `initialize` — none is modeled — does not count). `Class#new`
    intercepts only when this is `some`; otherwise dispatch falls to the
    `Class#new` builtin (artifact 02 §3). -/
def userInit? (h : Heap) (k : ObjId) : Option MethodDef :=
  match methodOn h k "initialize" with
  | some (_, md) => if md.builtin.isNone then some md else none
  | none => none

/-- Enter a RubyCore-defined method activation: bind params (required + rest +
    post; block-capture `&blk`), push the method frame, evaluate the body under
    a `frameK` boundary (artifact 02 §3). Factored out of dispatch so `Class#new`
    can reuse it for `initialize`. Arity failures raise `ArgumentError` [V]. -/
def enterUserMethod (m : Machine) (recv : Value) (mname : String) (md : MethodDef)
    (args : List Value) (blk : Option Value) (kw : List (Value × Value) := []) : StepResult :=
  let fp? := classifyFull md.params
  if fp?.isNone then
    .unsupported "unmodeled param kind (forwarding/destructuring)"
  else
  let fp := fp?.getD ⟨[], [], none, [], [], none, none, []⟩
  let hasKw := !fp.keys.isEmpty || fp.kwrest?.isSome
  -- Ruby-3 separation: a callee without keyword params receives a keyword bundle
  -- as one trailing positional Hash (empty vanishes) [V].
  let (args, m) := if hasKw then (args, m) else appendKwHash m args kw
  let np := fp.pre.length; let nopt := fp.opt.length; let npost := fp.post.length
  let n := args.length
  let required := np + npost
  let arityOk := match fp.rest? with
    | some _ => n ≥ required
    | none => n ≥ required && n ≤ required + nopt
  if !arityOk then
    let expected := match fp.rest? with
      | some _ => s!"{required}+"
      | none => if nopt == 0 then toString required else s!"{required}..{required + nopt}"
    -- CRuby appends *all* required keywords (those without a default) to the arity
    -- error, e.g. `(given 1, expected 0; required keywords: a, b)` — even ones the
    -- caller supplied, since the positional-arity check fires before keywords are
    -- bound (kwargs/004: `c:` is listed though `c: 3` was passed). Names are *bare*
    -- here (no leading `:`), unlike the standalone "missing keyword: :a" message.
    let reqKeys := fp.keys.filterMap (fun (kn, d?) => if d?.isNone then some kn else none)
    let kwSuffix := if reqKeys.isEmpty then ""
      else s!"; required keyword{if reqKeys.length == 1 then "" else "s"}: " ++
           String.intercalate ", " reqKeys
    .next (raiseErr m Boot.argumentErrorId
      s!"wrong number of arguments (given {n}, expected {expected}{kwSuffix})")
  else
    -- keyword validation (missing required / unknown, byte-exact ArgumentError [V]).
    let missing := fp.keys.filterMap (fun (kn, d?) =>
      if (kwLookup kw kn).isNone && d?.isNone then some kn else none)
    let keyNames := fp.keys.map (·.1)
    let leftover := kw.filter (fun p => match p.1 with | .sym s => !keyNames.contains s | _ => true)
    if hasKw && !missing.isEmpty then
      .next (raiseErr m Boot.argumentErrorId
        s!"missing keyword{if missing.length == 1 then "" else "s"}: {kwNameList missing}")
    else if hasKw && fp.kwrest?.isNone && !leftover.isEmpty then
      let names := leftover.filterMap (fun p => match p.1 with | .sym s => some s | _ => none)
      .next (raiseErr m Boot.argumentErrorId
        s!"unknown keyword{if names.length == 1 then "" else "s"}: {kwNameList names}")
    else
    -- positional distribution: pre from the front, post from the back, optionals
    -- fill the leftmost middle args, a `*rest` absorbs the surplus (artifact 02 §3).
    let preVals := args.take np
    let postVals := args.drop (n - npost)
    let middle := (args.drop np).take (n - npost - np)
    let filled := min nopt middle.length
    let optFilled := ((fp.opt.take filled).map (·.1)).zip (middle.take filled)
    let optOmitted := fp.opt.drop filled           -- (name, default-expr), eval in-frame
    let restVals := middle.drop filled
    -- keyword partition: provided bind directly; omitted-with-default via optDefK.
    let kwProvided := fp.keys.filterMap (fun (kn, _) => (kwLookup kw kn).map (fun v => (kn, v)))
    let kwOmitted := fp.keys.filterMap (fun (kn, d?) =>
      if (kwLookup kw kn).isNone then d?.map (fun d => (kn, d)) else none)
    -- Phase A: pre + filled optionals + provided keywords (visible to defaults).
    let localsA := fp.pre.zip preVals ++ optFilled ++ kwProvided
    -- Phase B (bound AFTER defaults [V]): rest, post, block, kwrest.
    let (restBinding, m) := match fp.rest? with
      | some r => let (rv, m) := Builtins.allocArr m restVals.toArray; ([(r, rv)], m)
      | none => ([], m)
    let (kwrestBinding, m) := match fp.kwrest? with
      | some (some kr) => let (hv, m) := Builtins.allocHsh m leftover.toArray; ([(kr, hv)], m)
      | _ => ([], m)
    let localsB := restBinding ++ fp.post.zip postVals ++
      (match fp.block? with | some b => [(b, blk.getD .nil)] | none => []) ++ kwrestBinding
    -- P5: expand destructuring params — the synthetic `__destr_k` slots hold the
    -- raw arg; destructure each into its sub-names (added to Phase A so they are
    -- visible to defaults), and drop the synthetic names.
    let (destrB, m) := fp.destrs.foldl (fun (acc, m) (sn, subs) =>
      let dv := ((localsA ++ localsB).find? (·.1 == sn)).map (·.2) |>.getD .nil
      let (bs, m) := destructureBind m subs dv
      (acc ++ bs, m)) ([], m)
    let notSynth : (String × Value) → Bool := fun b => !(fp.destrs.any (·.1 == b.1))
    let localsA := localsA.filter notSynth ++ destrB
    let localsB := localsB.filter notSynth
    let frame : Frame :=
      { self := recv, locals := localsA, defmod := md.owner, kind := .method, blk, meth := mname,
        cref := md.cref }
    let fid := m.frames.size
    let m := { m with frames := m.frames.push frame, stack := fid :: m.stack }
    let m := { m with kont := .frameK fid :: m.kont }
    -- positional-opt defaults first, then keyword defaults (Ruby order [V]).
    match optOmitted ++ kwOmitted with
    | [] =>
      let m := localsB.foldl (fun m (nv : String × Value) => m.setLocal nv.1 nv.2) m
      .next (withCtl m (.eval md.body))
    | (n0, d0) :: more =>
      .next (withKont m (.eval d0) (.optDefK n0 more localsB md.body))

/-- Get (or lazily create) the eigenclass of object `o` (artifact 01 §5). Its
    superclass realizes the metaclass chain so dispatch through `classOf` finds
    both singleton methods and inherited ones:
    - a regular object's eigenclass superclasses its real class (so ordinary
      methods still resolve);
    - a class/module's metaclass superclasses the metaclass of *its* superclass
      (so class methods are inherited: `B < A ⇒ B.classmethod` finds `A`'s),
      bottoming out at `Class` (so `new`/`name`/… still resolve).
    Fuel-bounded on the (finite, strictly-decreasing) superclass chain. -/
def eigenclassOf (m : Machine) (o : ObjId) : ObjId × Machine :=
  go m o (m.heap.objs.size + 1)
where
  go (m : Machine) (o : ObjId) : Nat → ObjId × Machine
  | 0 => (Boot.classId, m)   -- unreachable from H₀; keep the function total
  | fuel + 1 =>
    match (m.heap.get o).eigen with
    | some e => (e, m)
    | none =>
      let obj := m.heap.get o
      let (supr, m) := match obj.payload with
        | .cls c => match c.superclass with
          | some s => go m s fuel
          | none => (Boot.classId, m)   -- top of the metaclass chain
        | _ => (obj.klass, m)
      let ename := s!"#<Class:{className m.heap o}>"
      let (e, h) := m.heap.alloc
        { klass := Boot.classId,
          payload := .cls { superclass := some supr, name := ename, isModule := false } }
      let h := h.set o { h.get o with eigen := some e }
      (e, { m with heap := h })

/-- Open (or create) a class/module named `name` and run its `body` in a fresh
    class-body frame with `self` = `defmod` = the class object (artifact 01 §5).
    Reopening checks class/module agreement and, for `class`, superclass match
    [V]. `sup?` is the resolved superclass (classes default to Object). -/
def enterClassBody (m : Machine) (name : String) (isMod : Bool)
    (sup? : Option ObjId) (body : Expr) : StepResult :=
  let kindWord := if isMod then "module" else "class"
  let pushFrame (m : Machine) (k : ObjId) : StepResult :=
    let frame : Frame :=
      { self := .ref k, defmod := k, kind := .classBody, cref := k :: m.currentFrame.cref }
    let fid := m.frames.size
    let m := { m with frames := m.frames.push frame, stack := fid :: m.stack }
    .next (withKont m (.eval body) (.frameK fid))
  -- Reopen detection looks up `name` in the *current innermost namespace only*
  -- (`defmod`), NOT a flat toplevel lookup and NOT the full lexical cref chain.
  -- So `module B` inside a reopened `module A` finds the existing `A::B` (A's own
  -- constant) and reuses that object instead of allocating a duplicate and
  -- clobbering `A::B`. Crucially it is *not* the cref-walk used for constant
  -- *reads*: `class Foo` nested in `M` must create `M::Foo`, it does NOT reopen a
  -- lexically-visible `::Foo` (verified against CRuby). At the toplevel `defmod`
  -- is `Object`, so this coincides with the old flat lookup.
  match constOwn m.heap m.currentFrame.defmod name with
  | some (.ref k) =>
    match m.heap.classPayload? k with
    | some c =>
      if c.isModule != isMod then
        .next (raiseErr m Boot.typeErrorId s!"{name} is not a {kindWord}")
      else match sup? with
        | some s =>
          if c.superclass == some s then pushFrame m k
          else .next (raiseErr m Boot.typeErrorId s!"superclass mismatch for class {name}")
        | none => pushFrame m k
    | none => .next (raiseErr m Boot.typeErrorId s!"{name} is not a {kindWord}")
  | some _ => .next (raiseErr m Boot.typeErrorId s!"{name} is not a {kindWord}")
  | none =>
    let superclass := if isMod then none else some (sup?.getD Boot.objectId)
    -- A nested definition (`module B` inside `A`) takes the qualified constant
    -- path `A::B` as its `name` (CRuby derives the name from where the constant
    -- is bound); a toplevel definition (`defmod` = Object) keeps the bare name.
    let defmod := m.currentFrame.defmod
    let qualName := if defmod == Boot.objectId then name
                    else s!"{className m.heap defmod}::{name}"
    let obj : Object :=
      { klass := (if isMod then Boot.moduleId else Boot.classId),
        payload := .cls { superclass, name := qualName, isModule := isMod } }
    let (k, h) := m.heap.alloc obj
    -- register the class name in the *enclosing* namespace (Object at toplevel)
    let h := constSetIn h m.currentFrame.defmod name (.ref k)
    -- eagerly realize the metaclass chain so inherited class methods resolve
    -- (`B < A` ⇒ `B`'s metaclass superclasses `A`'s) even before any `def self.`
    let (_, m) := eigenclassOf { m with heap := h } k
    pushFrame m k

/-- `class/module A::name … end` (artifact 03 §5): open (or create) `name`
    inside the already-resolved namespace object `container`, then run the body.
    Like `enterClassBody` but the lookup/registration namespace is `container`
    (not the flat toplevel) and the class name is the full path `Container::name`
    (so `A::B.name` is `"A::B"` [V]). Scoped defs carry no explicit superclass
    (gated at decode), so a new class superclasses `Object`. -/
def enterScopedClassBody (m : Machine) (container : ObjId) (name : String)
    (isMod : Bool) (body : Expr) : StepResult :=
  let kindWord := if isMod then "module" else "class"
  let fullName := s!"{className m.heap container}::{name}"
  let pushFrame (m : Machine) (k : ObjId) : StepResult :=
    let frame : Frame := { self := .ref k, defmod := k, kind := .classBody }
    let fid := m.frames.size
    let m := { m with frames := m.frames.push frame, stack := fid :: m.stack }
    .next (withKont m (.eval body) (.frameK fid))
  let existing : Option Value := (m.heap.classPayload? container).bind fun c =>
    (c.consts.find? (·.1 == name)).map (·.2)
  match existing with
  | some (.ref k) =>
    match m.heap.classPayload? k with
    | some c =>
      if c.isModule != isMod then
        .next (raiseErr m Boot.typeErrorId s!"{fullName} is not a {kindWord}")
      else pushFrame m k
    | none => .next (raiseErr m Boot.typeErrorId s!"{fullName} is not a {kindWord}")
  | some _ => .next (raiseErr m Boot.typeErrorId s!"{fullName} is not a {kindWord}")
  | none =>
    let superclass := if isMod then none else some Boot.objectId
    let obj : Object :=
      { klass := (if isMod then Boot.moduleId else Boot.classId),
        payload := .cls { superclass, name := fullName, isModule := isMod } }
    let (k, h) := m.heap.alloc obj
    let h := constSetIn h container name (.ref k)
    let (_, m) := eigenclassOf { m with heap := h } k
    pushFrame m k

/-- Resolve a `cpath` base value to a namespace `ObjId`, or a `TypeError`
    result if it is not a class/module ("`<inspect>` is not a class/module"). -/
def cpathContainer (m : Machine) (base : Value) : Except StepResult ObjId :=
  match base with
  | .ref o =>
    if (m.heap.classPayload? o).isSome then .ok o
    else
      match Builtins.inspectP m base with
      | .ok r => .error (.next (raiseErr m Boot.typeErrorId s!"{r} is not a class/module"))
      | .error e => .error (.unsupported e)
  | _ =>
    match Builtins.inspectP m base with
    | .ok r => .error (.next (raiseErr m Boot.typeErrorId s!"{r} is not a class/module"))
    | .error e => .error (.unsupported e)

/-- Default `method_missing` (artifact 02 §4): the bare implicit-self zero-arg
    send is ambiguous (vcall `NameError` vs fcall `NoMethodError`; RubyCore
    conflates them) — gate; otherwise the byte-exact `NoMethodError`. -/
def missNoMethod (m : Machine) (recv : Value) (implicit : Bool) (mname : String)
    (args : List Value) : StepResult :=
  if implicit && args.isEmpty then
    .unsupported s!"vcall/fcall NameError ambiguity: {mname}"
  else
    .next (raiseErr m Boot.noMethodErrorId
      s!"undefined method '{mname}' for {receiverDesc m.heap recv}")

/-- Advance a native block-iterator: deliver the block's next call, or its final
    value once the per-iteration arg lists are exhausted. Reuses `callClosure`
    (a fresh block frame per element) with `brk` = the iterator's own activation
    frame, so `break` inside the block returns from the iterator call, `next`
    supplies that iteration's value, and `return` still targets the block's home
    method. Non-recursive: the loop is driven by the `iterK` continuation. -/
def iterStep (m : Machine) (cl : Closure) (brk : FrameId) (rest : List (List Value))
    (kind : IterKind) (acc : List Value) (retVal : Value) : StepResult :=
  match rest with
  | [] =>
    let (finalV, m) := match kind with
      | .ignore => (retVal, m)
      | .collect => let (a, m) := Builtins.allocArr m acc.toArray; (a, m)
      | .fold => (acc.headD .nil, m)
    .next (withCtl m (.value finalV))   -- `frameK brk` pops the iterator frame
  | a :: rest' =>
    let callArgs := match kind with | .fold => acc ++ a | _ => a
    let m := { m with kont := .iterK cl brk rest' kind acc retVal :: m.kont }
    callClosure m cl callArgs (some brk)

/-- Begin a native block-iterator: push an activation frame (the `break`/return
    target) under a `frameK`, then start the block-call loop. -/
def startIter (m : Machine) (recv : Value) (mname : String) (cl : Closure)
    (elemArgs : List (List Value)) (kind : IterKind) (initAcc : List Value)
    (retVal : Value) : StepResult :=
  let frame : Frame :=
    { self := recv, defmod := classOf m.heap recv, kind := .method, meth := mname }
  let fid := m.frames.size
  let m := { m with frames := m.frames.push frame, stack := fid :: m.stack }
  let m := { m with kont := .frameK fid :: m.kont }
  iterStep m cl fid elemArgs kind initAcc retVal

/-- If `(recv, mname)` is a native block-iterator invoked *with* a block, run it
    (returns `some`); otherwise `none` (fall through to the normal miss path — a
    blockless `each` etc. would be an Enumerator, still gated). Only reached on a
    lookup miss, so a user override of the method takes precedence. -/
def tryIterator (m : Machine) (recv : Value) (mname : String) (args : List Value)
    (blk : Option Value) : Option StepResult :=
  match blk with
  | some (.ref bo) =>
    match (m.heap.get bo).payload with
    | .proc cl =>
      match recv with
      | .ref o =>
        match (m.heap.get o).payload with
        | .arr xs =>
          let each1 := xs.toList.map (fun e => [e])
          match mname with
          | "each" => some (startIter m recv mname cl each1 .ignore [] recv)
          | "map" | "collect" => some (startIter m recv mname cl each1 .collect [] .nil)
          | "each_with_index" =>
            let ei := xs.toList.zipIdx.map (fun (e, i) => [e, Value.int (Int.ofNat i)])
            some (startIter m recv mname cl ei .ignore [] recv)
          | "inject" | "reduce" =>
            -- block form only; `inject(:sym)` has no block ⇒ not reached here.
            match args with
            | [] => match xs.toList with
              | [] => some (.next (withCtl m (.value .nil)))   -- empty, no seed → nil
              | h :: t => some (startIter m recv mname cl (t.map (fun e => [e])) .fold [h] .nil)
            | [seed] => some (startIter m recv mname cl each1 .fold [seed] .nil)
            | _ => none
          | _ => none
        | .hsh pairs =>
          match mname with
          | "each" | "each_pair" =>
            -- Hash#each yields one `[k, v]` array per entry (block `|k,v|`
            -- auto-splats it; `|pair|` gets the whole array).
            let (elemArgs, m) := pairs.toList.foldl (fun (acc, m) (kv : Value × Value) =>
              let (pa, m) := Builtins.allocArr m #[kv.1, kv.2]; (acc ++ [[pa]], m)) ([], m)
            some (startIter m recv mname cl elemArgs .ignore [] recv)
          | "each_key" =>
            -- yields the key alone per entry; returns the hash.
            some (startIter m recv mname cl (pairs.toList.map (fun kv => [kv.1])) .ignore [] recv)
          | "each_value" =>
            -- yields the value alone per entry; returns the hash.
            some (startIter m recv mname cl (pairs.toList.map (fun kv => [kv.2])) .ignore [] recv)
          | _ => none
        | _ => none
      | .int n =>
        match mname with
        | "times" =>
          some (startIter m recv mname cl
            ((List.range n.toNat).map (fun i => [Value.int (Int.ofNat i)])) .ignore [] recv)
        | _ => none
      | _ => none
    | _ => none
  | _ => none

/-- Standard library modules a core class includes in real CRuby but which the
    L0 heap does not put in its ancestor chain yet (no MRO/mixins). Used to gate
    a miss that CRuby would resolve through one of these (e.g. a user method
    monkey-patched onto `Enumerable` and called on an `Array`). Superseded once
    `include`/MRO lands (MX1). -/
def stdMixins (cls : ObjId) : List String :=
  -- `Kernel` is a universal ancestor (every Object includes it); the rest are
  -- per core class. Only matters when the user has reopened one of these.
  "Kernel" :: (
    if cls == Boot.arrayId || cls == Boot.hashId then ["Enumerable"]
    else if cls == Boot.integerId || cls == Boot.floatId || cls == Boot.stringId then ["Comparable"]
    else [])

/-- Does a standard mixin of `cls` (user-reopened `Kernel`/`Enumerable`/…) define
    `name`? Used both to gate a dispatch miss and to answer `respond_to?`/
    `method_defined?` for methods the model can't reach via its ancestor chain. -/
def mixinDefines (m : Machine) (cls : ObjId) (name : String) : Bool :=
  (stdMixins cls).any fun modName =>
    match constLookup m.heap modName with
    | some (.ref mo) => (methodOn m.heap mo name).isSome
    | _ => false

/-- Would CRuby resolve `mname` on `recv` via a standard mixin the model doesn't
    put in the ancestor chain? Returns the module name for the gate message. -/
def mixinShadow (m : Machine) (recv : Value) (mname : String) : Option String :=
  (stdMixins (classOf m.heap recv)).firstM fun modName =>
    match constLookup m.heap modName with
    | some (.ref mo) => if (methodOn m.heap mo mname).isSome then some modName else none
    | _ => none

/-- The user-defined `self.included`/`self.extended` hook of module `mo`, if any
    (a singleton method on its eigenclass). -/
def moduleHook (m : Machine) (mo : ObjId) (name : String) : Option MethodDef :=
  match (m.heap.get mo).eigen with
  | some e => (methodOn m.heap e name).map (·.2)
  | none => none

/-- `include`/`extend` (artifact 02 §1). `include M` (single module, on a class/
    module receiver) appends `M` to the receiver's `includes` (MRO) and fires
    `M.included(recv)` if defined. `obj.extend(M)` mixes `M` into `obj`'s
    eigenclass (so `M`'s instance methods become singleton methods). Returns
    `some` if handled; `none` falls through to the normal miss path. -/
def tryMixin (m : Machine) (recv : Value) (mname : String)
    (args : List Value) : Option StepResult :=
  match mname, recv, args with
  | "include", .ref o, [.ref mo] =>
    match m.heap.classPayload? o, m.heap.classPayload? mo with
    | some c, some _ =>
      let m := { m with heap := m.heap.setClassPayload o { c with includes := c.includes ++ [mo] } }
      match moduleHook m mo "included" with
      | some hook =>
        let m := { m with kont := .includeK recv :: m.kont }
        some (enterUserMethod m (.ref mo) "included" hook [recv] none)
      | none => some (.next (withCtl m (.value recv)))
    | _, _ => none
  | "extend", .ref o, [.ref mo] =>
    match m.heap.classPayload? mo with
    | some _ =>
      -- `extend` = include the module into the receiver's eigenclass; the
      -- `extended` hook is unmodeled → gate if present.
      match moduleHook m mo "extended" with
      | some _ => some (.unsupported "extend with an `extended` hook")
      | none =>
        let (e, m) := eigenclassOf m o
        match m.heap.classPayload? e with
        | some ec =>
          let m := { m with heap := m.heap.setClassPayload e { ec with includes := ec.includes ++ [mo] } }
          some (.next (withCtl m (.value recv)))
        | none => none
    | none => none
  | _, _, _ => none

/-- A method-name argument: a Symbol or a String (`send`/`respond_to?`/… accept
    both). -/
def symOrStr (m : Machine) (v : Value) : Option String :=
  match v with
  | .sym s => some s
  | .ref o => match (m.heap.get o).payload with | .str s => some s | _ => none
  | _ => none

/-- `attr_reader`/`attr_writer`/`attr_accessor` install `@x` getter / `x=` setter
    methods (bodies synthesized as ordinary RubyCore) on `cls`, returning the
    defined method names as symbols (Ruby-3 [V]). -/
def defineAttr (m : Machine) (cls : ObjId) (mname : String)
    (args : List Value) : Machine × List Value :=
  args.foldl (fun (m, names) arg =>
    match arg with
    | .sym s =>
      -- accessor methods are named `s`/`s=`, but the backing ivar is `@s` [V].
      let iv := "@" ++ s
      let getter : MethodDef := { params := [], body := .var .ivar iv, owner := cls }
      let setter : MethodDef :=
        { params := [.req "__v"], body := .vasgn .ivar iv (.var .lvar "__v"), owner := cls }
      let m := if mname != "attr_writer" then { m with heap := defineMethod m.heap cls s getter } else m
      let m := if mname != "attr_reader" then { m with heap := defineMethod m.heap cls (s ++ "=") setter } else m
      let names := names
        ++ (if mname != "attr_writer" then [Value.sym s] else [])
        ++ (if mname != "attr_reader" then [Value.sym (s ++ "=")] else [])
      (m, names)
    | _ => (m, names)) (m, [])

/-- Class macros + reflection (artifact 02): `attr_*` (define accessors),
    `method_defined?` (instance-method presence on a class), `respond_to?`
    (method presence on a receiver — user or modeled/CRuby builtin). Only reached
    on a lookup miss, so a user override wins. -/
def tryReflect (m : Machine) (recv : Value) (mname : String)
    (args : List Value) : Option StepResult :=
  match mname with
  | "attr_reader" | "attr_writer" | "attr_accessor" =>
    match recv with
    | .ref o => match m.heap.classPayload? o with
      | some _ =>
        let (m, names) := defineAttr m o mname args
        let (arr, m) := Builtins.allocArr m names.toArray
        some (.next (withCtl m (.value arr)))
      | none => none
    | _ => none
  | "method_defined?" =>
    match recv, args with
    | .ref o, [nameArg] =>
      match symOrStr m nameArg, m.heap.classPayload? o with
      | some name, some _ =>
        let found := (match methodOn m.heap o name with | some (_, md) => !md.undefined | none => false)
          || (crubyShadow m.heap (ancestors m.heap o) name).isSome
          || mixinDefines m o name
        some (.next (withCtl m (.value (.bool found))))
      | _, _ => none
    | _, _ => none
  | "respond_to?" =>
    match args with
    | nameArg :: _ =>   -- ignore the optional include_private flag
      match symOrStr m nameArg with
      | some name =>
        let found := (match lookup m.heap recv name with | some (_, md) => !md.undefined | none => false)
          || (crubyShadow m.heap (ancestors m.heap (classOf m.heap recv)) name).isSome
          || mixinDefines m (classOf m.heap recv) name
        if found then some (.next (withCtl m (.value (.bool true))))
        else
          -- not a real method; CRuby then consults a user `respond_to_missing?`,
          -- which can run arbitrary code — gate rather than guess `false`.
          match methodOn m.heap (classOf m.heap recv) "respond_to_missing?" with
          | some (_, md) =>
            if md.builtin.isNone then some (.unsupported "respond_to? with user respond_to_missing?")
            else some (.next (withCtl m (.value (.bool false))))
          | none => some (.next (withCtl m (.value (.bool false))))
      | none => none
    | _ => none
  | _ => none

/-- A lookup miss (no entry, or an `undef` tombstone): gate CRuby-shadowed
    names, else route to `method_missing` (user override) or the byte-exact
    `NoMethodError` (artifact 02 §4). Shared by the genuine-miss and
    tombstone-hit dispatch paths. -/
def dispatchMiss (m : Machine) (recv : Value) (implicit : Bool) (mname : String)
    (args : List Value) (blk : Option Value) : StepResult :=
  match tryIterator m recv mname args blk with
  | some sr => sr
  | none =>
  match tryMixin m recv mname args with
  | some sr => sr
  | none =>
  match tryReflect m recv mname args with
  | some sr => sr
  | none =>
  let chain := ancestors m.heap (classOf m.heap recv)
  match crubySingletonShadow m.heap recv mname with
  | some cname => .unsupported s!"unmodeled singleton method {cname}.{mname}"
  | none =>
  match crubyShadow m.heap chain mname with
  | some cname => .unsupported s!"unmodeled method {cname}#{mname}"
  | none =>
  match mixinShadow m recv mname with
  | some modName => .unsupported s!"method via unmodeled mixin {modName}#{mname}"
  | none =>
    match methodOn m.heap (classOf m.heap recv) "method_missing" with
    | some (_, mm) =>
      if mm.builtin.isNone then
        enterUserMethod m recv "method_missing" mm (.sym mname :: args) blk
      else missNoMethod m recv implicit mname args
    | none => missNoMethod m recv implicit mname args

/-- All args evaluated → dispatch (artifact 02 §3 SEND-INVOKE). A Proc
    receiver called via call/()/[]/yield runs its closure directly (a builtin
    cannot push a frame). -/
partial def invoke (m : Machine) (recv : Value) (implicit : Bool) (mname : String)
    (args : List Value) (blk : Option Value) (kw : List (Value × Value) := []) : StepResult :=
  -- `send`/`public_send`/`__send__`: re-dispatch the (symbol/string) first arg on
  -- `recv` with the rest. Only when unshadowed by a user `send` (rare) [V].
  if (mname == "send" || mname == "public_send" || mname == "__send__")
      && (lookup m.heap recv mname).isNone then
    match args with
    | nameArg :: rest =>
      match symOrStr m nameArg with
      | some m2 => invoke m recv false m2 rest blk kw
      | none => invokeDispatch m recv implicit mname args blk kw
    | [] => invokeDispatch m recv implicit mname args blk kw
  else
  match recv with
  | .ref o =>
    match (m.heap.get o).payload with
    | .proc cl =>
      if mname == "call" || mname == "()" || mname == "[]" || mname == "yield" then
        if kw.isEmpty then callClosure m cl args none
        else .unsupported "keyword arguments to a Proc call"
      else invokeDispatch m recv implicit mname args blk kw
    | .cls c =>
      -- `Class#new` on a class with a user `initialize` must allocate then run
      -- `initialize` (a frame the builtin cannot push); yield the instance via
      -- `newK`. Special-payload subclasses (String/Array/Exception/…) need
      -- allocation we don't model → gate. No user init ⇒ fall to the builtin.
      if mname == "new" && !c.isModule then
        match userInit? m.heap o with
        | some md =>
          if (ancestors m.heap o).any (fun a =>
              Builtins.payloadCoreClasses.contains a || a == Boot.exceptionId) then
            .unsupported "Class#new with user initialize on a special-payload subclass"
          else
            let (io, h) := m.heap.alloc { klass := o }
            let inst := Value.ref io
            let m := { m with heap := h, kont := .newK inst :: m.kont }
            enterUserMethod m inst "initialize" md args blk kw
        | none => invokeDispatch m recv implicit mname args blk kw
      else invokeDispatch m recv implicit mname args blk kw
    | _ => invokeDispatch m recv implicit mname args blk kw
  | _ => invokeDispatch m recv implicit mname args blk kw
where
  invokeDispatch (m : Machine) (recv : Value) (implicit : Bool) (mname : String)
      (args : List Value) (blk : Option Value) (kw : List (Value × Value)) : StepResult :=
  let chain := ancestors m.heap (classOf m.heap recv)
  match lookup m.heap recv mname with
  | some (owner, md) =>
    if md.undefined then
      -- `undef` tombstone: the walk stopped here, dispatch as a miss.
      let (args, m) := appendKwHash m args kw
      dispatchMiss m recv implicit mname args blk
    else
    -- Dispatch fidelity: if CRuby defines `mname` on a class BETWEEN the
    -- receiver's class and our resolved owner, CRuby would dispatch there —
    -- we'd be running the wrong method. Gate. (Builtins are exempt only
    -- from their own owner downward.)
    let between := chain.takeWhile (· != owner)
    match crubyShadow m.heap between mname with
    | some cname => .unsupported s!"unmodeled builtin would shadow: {cname}#{mname}"
    | none =>
      match md.builtin with
      | some bid =>
        -- builtins have no keyword params in the model: keywords collapse to a
        -- trailing positional Hash (Ruby-3 [V]).
        let (args, m) := appendKwHash m args kw
        match Builtins.run bid recv args m with
        | .ok v m => .next (withCtl m (.value v))
        | .err cls msg m => .next (raiseErr m cls msg)
        | .throwV v m => .next (withCtl m (.jump (.raiseJ v)))
        | .unsupported r => .unsupported r
      | none =>
        match crubySingletonShadow m.heap recv mname with
        | some cname => .unsupported s!"unmodeled singleton method {cname}.{mname}"
        | none =>
          -- a RubyCore-defined method: bind params + push the activation
          enterUserMethod m recv mname md args blk kw
  | none =>
    let (args, m) := appendKwHash m args kw
    dispatchMiss m recv implicit mname args blk

/-- Super-dispatch (artifact 02 §2): re-run the current method name starting
    *after* its `defmod` in `self`'s ancestor chain, keeping the same `self` and
    forwarding/passing `blk`. A miss raises `NoMethodError "super: no superclass
    method '{m}' for {recv}"` [V]. `super` is evaluated in the enclosing method
    activation (`methodFrameOf`), so it works from inside a block too. -/
def doSuper (m : Machine) (args : List Value) (blk : Option Value) : StepResult :=
  let f := m.frames.getD (methodFrameOf m) default
  if f.meth == "" then .unsupported "super outside a method"
  else
    let self := f.self
    let after := (ancestors m.heap (classOf m.heap self)).dropWhile (· != f.defmod) |>.drop 1
    let found : Option (ObjId × MethodDef) := after.firstM fun c =>
      match m.heap.classPayload? c with
      | some cp => (cp.methods.find? (·.1 == f.meth)).map (fun (_, md) => (c, md))
      | none => none
    match found with
    | some (_, md) =>
      match md.builtin with
      | some bid =>
        match Builtins.run bid self args m with
        | .ok v m => .next (withCtl m (.value v))
        | .err cls msg m => .next (raiseErr m cls msg)
        | .throwV v m => .next (withCtl m (.jump (.raiseJ v)))
        | .unsupported r => .unsupported r
      | none => enterUserMethod m self f.meth md args blk
    | none =>
      .next (raiseErr m Boot.noMethodErrorId
        s!"super: no superclass method '{f.meth}' for {receiverDesc m.heap self}")

/-- Args that bare `super` forwards: the *current* values of the enclosing
    method's formal parameters — read from the method frame's locals, a splat
    param spreading its array (artifact 02 §2) [V: `x=x+1; super` forwards the
    reassigned value]. `none` if the param shape is beyond L2b. -/
def zsuperArgs (m : Machine) : Option (List Value) :=
  let f := m.frames.getD (methodFrameOf m) default
  match methodOn m.heap f.defmod f.meth with
  | some (_, md) =>
    match classifySimple md.params with
    | none => none
    | some sp =>
    let pre := sp.pre; let rest? := sp.rest?; let post := sp.post
    let readL (n : String) : Value := (f.locals.find? (·.1 == n)).map (·.2) |>.getD .nil
    let preV := pre.map readL
    let postV := post.map readL
    match rest? with
    | none => some (preV ++ postV)
    | some rname =>
      match f.locals.find? (·.1 == rname) with
      | some (_, .ref o) =>
        match (m.heap.get o).payload with
        | .arr xs => some (preV ++ xs.toList ++ postV)
        | _ => none
      | _ => none
  | none => none

/-- The block bare `super`/`super(args)` forwards: the enclosing method's. -/
def methodBlk (m : Machine) : Option Value :=
  (m.frames.getD (methodFrameOf m) default).blk

/-- Evaluate an explicit `super(args)` left to right, then dispatch. -/
def startSuperArgs (m : Machine) (acc : List Value) (rest : List Expr)
    (blk : Option Value) : StepResult :=
  match rest with
  | [] => doSuper m acc blk
  | e :: rest' =>
    match e with
    | .splat (some e) => .next (withKont m (.eval e) (.superSplatK acc rest' blk))
    | .splat none => .unsupported "anonymous splat in super"
    | .kwargs _ => .unsupported "keyword arguments to super"
    | .fwd => .unsupported "... forwarding to super"
    | _ => .next (withKont m (.eval e) (.superArgK acc rest' blk))

/-- All args in → resolve the pending block and dispatch. A literal block is
    reified here (capturing the caller frame); `proc`/`lambda`/`Proc.new` with
    a block capture rather than call; a `&e` block-pass evaluates `e` last
    (eval order) then coerces. -/
def finishSend (m : Machine) (recv : Value) (implicit : Bool) (mname : String)
    (args : List Value) (pblk : PendingBlk) (kw : List (Value × Value) := []) : StepResult :=
  match pblk with
  | .passExpr e => .next (withKont m (.eval e) (.blkCoerceK recv implicit mname args kw))
  | .lit ps ls body =>
    let mkLam := implicit && mname == "lambda"
    let (v, m) := reifyBlock m ps ls body mkLam
    if implicit && (mname == "lambda" || mname == "proc") then
      .next (withCtl m (.value v))
    else if mname == "new" && (match recv with | .ref k => k == Boot.procId | _ => false) then
      .next (withCtl m (.value v))
    else if mname == "new" then
      -- Class#new with a block (initialize block / Hash default proc) — the
      -- block affects behaviour and we don't model it, so gate rather than
      -- silently drop it.
      .unsupported "Class#new with a block"
    else invoke m recv implicit mname args (some v) kw
  | .passAnon => invoke m recv implicit mname args m.currentFrame.blk kw
  | .none => invoke m recv implicit mname args none kw

/-- Evaluate the pending call-site `kwargs` entries (values left to right,
    `**h` splats expanded), then dispatch. Duplicate keys keep first position,
    last value (as hash literals do [V]). -/
def startKwargs (m : Machine) (recv : Value) (implicit : Bool) (mname : String)
    (posArgs : List Value) (kwacc : List (Value × Value)) (entries : List KwEntry)
    (pblk : PendingBlk) : StepResult :=
  match entries with
  | [] => finishSend m recv implicit mname posArgs pblk kwacc
  | .pair k valE :: rest =>
    .next (withKont m (.eval valE) (.kwPairK k rest kwacc recv implicit mname posArgs pblk))
  | .splat e :: rest =>
    .next (withKont m (.eval e) (.kwSplatK rest kwacc recv implicit mname posArgs pblk))

/-- Add a `(Symbol, Value)` keyword pair, keeping first position / last value. -/
def kwAdd (kwacc : List (Value × Value)) (key val : Value) : List (Value × Value) :=
  match kwacc.findIdx? (fun p => p.1.identEq key) with
  | some i => kwacc.set i (key, val)
  | none => kwacc ++ [(key, val)]

/-- Read the hidden `...`-forwarding bundle (`*__fwd_rest, **__fwd_kw,
    &__fwd_blk`) bound by a `(...)`-forwarding method: the positional args, the
    keyword pairs, and the block (no evaluation — a direct local read). -/
def forwardBundle (m : Machine) : List Value × List (Value × Value) × Option Value :=
  let restVals := match m.getLocal fwdRest with
    | .ref o => match (m.heap.get o).payload with | .arr xs => xs.toList | _ => []
    | _ => []
  let kw := match m.getLocal fwdKw with
    | .ref o => match (m.heap.get o).payload with | .hsh ps => ps.toList | _ => []
    | _ => []
  let blk := match m.getLocal fwdBlk with | .nil => none | v => some v
  (restVals, kw, blk)

/-- Evaluate the next pending argument, or dispatch if none remain. A trailing
    `kwargs` marker switches to keyword evaluation; a `fwd` marker (`g(...)`)
    expands the enclosing method's forwarding bundle. -/
def startArgs (m : Machine) (recv : Value) (implicit : Bool) (mname : String)
    (acc : List Value) (rest : List Expr) (pblk : PendingBlk) : StepResult :=
  match rest with
  | [] => finishSend m recv implicit mname acc pblk
  | e :: rest' =>
    match e with
    | .splat (some e) =>
      .next (withKont m (.eval e) (.argsSplatK recv implicit mname acc rest' pblk))
    | .splat none => .unsupported "anonymous splat forwarding"
    | .kwargs entries => startKwargs m recv implicit mname acc [] entries pblk
    | .fwd =>
      -- `...` is always last; expand the forwarding bundle and dispatch. The
      -- block rides in the bundle (no explicit block with `...`), so `pblk` is
      -- `.none` here and `invoke` is called directly.
      let (restVals, kw, blk) := forwardBundle m
      invoke m recv implicit mname (acc ++ restVals) blk kw
    | _ => .next (withKont m (.eval e) (.argsK recv implicit mname acc rest' pblk))

/-- Call the enclosing method's block with `args` (artifact 04 §2 YIELD). A
    `break` inside the yielded block returns from that method. -/
def doYield (m : Machine) (args : List Value) : StepResult :=
  match m.currentFrame.blk with
  | none => .next (raiseErr m Boot.localJumpErrorId "no block given (yield)")
  | some (.ref o) =>
    match (m.heap.get o).payload with
    | .proc cl => callClosure m cl args (some (methodFrameOf m))
    | _ => .stuck "method block is not a Proc"
  | some _ => .stuck "method block is not a Proc"

/-- Evaluate `yield` args left to right, then yield. -/
def startYield (m : Machine) (acc : List Value) (rest : List Expr) : StepResult :=
  match rest with
  | [] => doYield m acc
  | e :: rest' =>
    match e with
    | .splat (some e) => .next (withKont m (.eval e) (.yieldSplatK acc rest'))
    | .splat none => .unsupported "anonymous splat in yield"
    | .kwargs _ => .unsupported "keyword arguments to yield"
    | .fwd => .unsupported "... forwarding to yield"
    | _ => .next (withKont m (.eval e) (.yieldArgK acc rest'))

/-- Evaluate the next pending array-literal element, or allocate. -/
def continueArray (m : Machine) (acc : List Value) (rest : List Expr) : StepResult :=
  match rest with
  | [] =>
    let (av, m) := Builtins.allocArr m acc.toArray
    .next (withCtl m (.value av))
  | e :: rest' =>
    match e with
    | .splat (some e) => .next (withKont m (.eval e) (.arrSplatK acc rest'))
    | .splat none => .unsupported "anonymous splat in array literal"
    | _ => .next (withKont m (.eval e) (.arrK acc rest'))

/-- Bind one `for` element to the loop targets in the *enclosing* frame (the
    leak, artifact 04 [V]). A single target takes the whole element; multiple
    targets destructure it array-wise (an `Array` positionally, a scalar into
    the first target with the rest `nil` — massign semantics [V]). Only local
    targets are modeled; a non-local target returns `none` → gate. -/
def forBind (m : Machine) (targets : List (TargetKind × String))
    (elem : Value) : Option Machine :=
  if !targets.all (fun (k, _) => k == .lvar) then none
  else match targets with
    | [(_, name)] => some (m.setLocal name elem)
    | _ =>
      let vals := match elem with
        | .ref o => match (m.heap.get o).payload with
            | .arr xs => xs.toList
            | _ => [elem]
        | _ => [elem]
      some ((targets.zipIdx).foldl
        (fun m (t, i) => m.setLocal t.2 (vals.getD i .nil)) m)

/-- Advance a `for` loop: bind the next element and run the body, or finish with
    the collection value when exhausted (`for` evaluates to its collection [V]). -/
def forStep (m : Machine) (targets : List (TargetKind × String)) (body : Expr)
    (rest : List Value) (coll : Value) : StepResult :=
  match rest with
  | [] => .next (withCtl m (.value coll))
  | elem :: tail =>
    match forBind m targets elem with
    | none => .unsupported "for with a non-local loop target"
    | some m => .next (withKont m (.eval body) (.forBodyK targets body tail coll))

/-- Deliver a value to the top continuation. -/
def applyKont (m : Machine) (v : Value) : StepResult :=
  match m.kont with
  | [] => .done v m
  | k :: rest =>
    let m := { m with kont := rest }
    match k with
    | .seqK es =>
      match es with
      | [] => .next (withCtl m (.value v))
      | e :: rest' => .next (withKont m (.eval e) (.seqK rest'))
    | .asgnK kind x =>
      match kind with
      | .lvar => .next (withCtl (m.setLocal x v) (.value v))
      | .gvar => .next (withCtl (m.setGlobal x v) (.value v))
      | .ivar =>
        match m.currentFrame.self with
        | .ref o =>
          if (m.heap.get o).frozen then
            match Builtins.inspectP m (.ref o) with
            | .ok r => .next (raiseErr m Boot.frozenErrorId
                s!"can't modify frozen {className m.heap (m.heap.get o).klass}: {r}")
            | .error e => .unsupported e
          else .next (withCtl (bindIvar m x v) (.value v))
        | selfV =>
          -- immediates are frozen: @x= with Integer self → FrozenError [V]
          match Builtins.inspectP m selfV with
          | .ok r => .next (raiseErr m Boot.frozenErrorId
              s!"can't modify frozen {className m.heap (classOf m.heap selfV)}: {r}")
          | .error e => .unsupported e
      | .cvar => .unsupported "class variables"
    | .casgnK n =>
      .next (withCtl
        { m with heap := constSetIn m.heap m.currentFrame.defmod n v } (.value v))
    | .classDefK name body =>
      -- v is the resolved superclass: it must be a non-module Class object [V]
      match v with
      | .ref k =>
        match m.heap.classPayload? k with
        | some c =>
          if c.isModule then
            .next (raiseErr m Boot.typeErrorId
              s!"superclass must be an instance of Class (given an instance of {className m.heap (classOf m.heap v)})")
          else enterClassBody m name false (some k) body
        | none =>
          .next (raiseErr m Boot.typeErrorId
            s!"superclass must be an instance of Class (given an instance of {className m.heap (classOf m.heap v)})")
      | .nil | .bool _ =>
        -- CRuby phrases these as "given nil"/"given false" — gate rather than
        -- emit the "an instance of …" form.
        .unsupported "superclass is nil/true/false"
      | _ =>
        .next (raiseErr m Boot.typeErrorId
          s!"superclass must be an instance of Class (given an instance of {className m.heap (classOf m.heap v)})")
    | .newK inst =>
      -- `initialize` returned; its value is discarded, `new` yields the instance
      .next (withCtl m (.value inst))
    | .includeK recv =>
      -- `included` hook returned; its value is discarded, `include` yields recv
      .next (withCtl m (.value recv))
    | .defsK name params body =>
      -- `def RECV.name`: install on RECV's eigenclass (v = the evaluated RECV)
      match v with
      | .ref o =>
        let (e, m) := eigenclassOf m o
        -- `def self.m` in a module keeps that module's lexical cref for constant
        -- lookup even though its dispatch owner is the eigenclass (artifact 03).
        let md : MethodDef := { params, body, owner := e, cref := m.currentFrame.cref }
        let m := { m with heap := defineMethod m.heap e name md }
        let m := if reprSensitive.contains name then { m with reprPure := false } else m
        .next (withCtl m (.value (.sym name)))
      | _ =>
        -- singleton def on an immediate (`def 1.m`) — TypeError; message-gate
        .unsupported "singleton def on an immediate"
    | .sclassK body =>
      -- `class << OBJ`: run body with self/cref = OBJ's eigenclass
      match v with
      | .ref o =>
        let (e, m) := eigenclassOf m o
        let frame : Frame := { self := .ref e, defmod := e, kind := .classBody, cref := e :: m.currentFrame.cref }
        let fid := m.frames.size
        let m := { m with frames := m.frames.push frame, stack := fid :: m.stack }
        .next (withKont m (.eval body) (.frameK fid))
      | _ => .unsupported "singleton class of an immediate"
    | .cpathK name =>
      -- v is the evaluated base `A`; resolve constant `name` in its namespace.
      match cpathContainer m v with
      | .error sr => sr
      | .ok o =>
        match constLookupFrom m.heap o name with
        | some cv => .next (withCtl m (.value cv))
        | none =>
          -- CRuby invokes `const_missing` before raising; if the base defines it
          -- (a singleton method), gate rather than emit a spurious NameError.
          let hasCM := match (m.heap.get o).eigen with
            | some e => (methodOn m.heap e "const_missing").isSome
            | none => false
          if hasCM then .unsupported "const_missing hook"
          else .next (raiseErr m Boot.nameErrorId
            s!"uninitialized constant {className m.heap o}::{name}")
    | .cpathAsgnK name rhs =>
      -- v is base `A`; evaluate `rhs`, then assign (base then rhs order [V]).
      match cpathContainer m v with
      | .error sr => sr
      | .ok o => .next (withKont m (.eval rhs) (.cpathAsgnValK name o))
    | .cpathAsgnValK name base =>
      -- v is the rhs; write it into base's namespace; assignment yields rhs [V].
      .next (withCtl { m with heap := constSetIn m.heap base name v } (.value v))
    | .scopedClassDefK name isMod body =>
      -- v is base `A`; open (or create) `name` inside it.
      match cpathContainer m v with
      | .error sr => sr
      | .ok o => enterScopedClassBody m o name isMod body
    | .ifK t e =>
      if v.truthy then .next (withCtl m (.eval t))
      else
        match e with
        | some e => .next (withCtl m (.eval e))
        | none => .next (withCtl m (.value .nil))  -- fall-through if → nil [V]
    | .whileCondK c body =>
      if v.truthy then .next (withKont m (.eval body) (.whileBodyK c body))
      else .next (withCtl m (.value .nil))
    | .whileBodyK c body =>
      .next (withKont m (.eval c) (.whileCondK c body))
    | .forStartK targets body =>
      -- v is the collection: iterate an Array natively (the model gates
      -- Array#each, so `for` cannot desugar to it). Others gate.
      match v with
      | .ref o =>
        match (m.heap.get o).payload with
        | .arr xs => forStep m targets body xs.toList v
        | _ => .unsupported "for over a non-Array collection"
      | _ => .unsupported "for over a non-Array collection"
    | .forBodyK targets body rest coll =>
      forStep m targets body rest coll
    | .iterK cl brk rest kind acc retVal =>
      -- v is the block's result for the current element; fold it, then continue.
      let acc := match kind with
        | .ignore => acc
        | .collect => acc ++ [v]
        | .fold => [v]
      iterStep m cl brk rest kind acc retVal
    | .recvK mname args pblk implicit =>
      startArgs m v implicit mname [] args pblk
    | .argsK recv implicit mname acc rest pblk =>
      startArgs m recv implicit mname (acc ++ [v]) rest pblk
    | .argsSplatK recv implicit mname acc rest pblk =>
      match spread m v with
      | .ok vs => startArgs m recv implicit mname (acc ++ vs) rest pblk
      | .error e => .unsupported e
    | .blkCoerceK recv implicit mname acc kw =>
      match coerceToProc m v with
      | .ok (blkV, m) => invoke m recv implicit mname acc blkV kw
      | .error e => .unsupported e
    | .kwPairK key rest kwacc recv implicit mname posArgs pblk =>
      startKwargs m recv implicit mname posArgs (kwAdd kwacc (.sym key) v) rest pblk
    | .kwSplatK rest kwacc recv implicit mname posArgs pblk =>
      match v with
      | .ref o =>
        match (m.heap.get o).payload with
        | .hsh pairs =>
          let kwacc := pairs.foldl (fun acc (p : Value × Value) => kwAdd acc p.1 p.2) kwacc
          startKwargs m recv implicit mname posArgs kwacc rest pblk
        | _ => .unsupported "** of a non-Hash"
      | _ => .unsupported "** of a non-Hash"
    | .superArgK acc rest blk => startSuperArgs m (acc ++ [v]) rest blk
    | .superSplatK acc rest blk =>
      match spread m v with
      | .ok vs => startSuperArgs m (acc ++ vs) rest blk
      | .error e => .unsupported e
    | .yieldArgK acc rest => startYield m (acc ++ [v]) rest
    | .yieldSplatK acc rest =>
      match spread m v with
      | .ok vs => startYield m (acc ++ vs) rest
      | .error e => .unsupported e
    | .arrK acc rest => continueArray m (acc ++ [v]) rest
    | .arrSplatK acc rest =>
      match spread m v with
      | .ok vs => continueArray m (acc ++ vs) rest
      | .error e => .unsupported e
    | .hshKeyK acc vExpr rest =>
      .next (withKont m (.eval vExpr) (.hshValK acc v rest))
    | .hshValK acc key rest =>
      -- duplicate keys keep first position, last value [V]
      let acc := match acc.findIdx? (fun (k', _) => valueEql m.heap k' key) with
        | some i => acc.set i (acc[i]!.1, v)
        | none => acc ++ [(key, v)]
      match rest with
      | [] =>
        let (hv, m) := Builtins.allocHsh m acc.toArray
        .next (withCtl m (.value hv))
      | (kE, vE) :: rest' =>
        .next (withKont m (.eval kE) (.hshKeyK acc vE rest'))
    | .jumpValK kind =>
      match kind with
      | .retK => doReturn m v
      | .brkK => .next (withCtl m (.jump (.brkJ v)))
      | .nxtK => .next (withCtl m (.jump (.nxtJ v)))
    | .optDefK name rest post body =>
      -- v is the default value for `name`; bind it, then the next default, or
      -- (all defaults done) install post/rest/block and run the body.
      let m := m.setLocal name v
      match rest with
      | [] =>
        let m := post.foldl (fun m (nv : String × Value) => m.setLocal nv.1 nv.2) m
        .next (withCtl m (.eval body))
      | (n0, d0) :: more => .next (withKont m (.eval d0) (.optDefK n0 more post body))
    | .frameK _ =>
      -- normal completion of a method body: pop the activation
      .next (withCtl { m with stack := m.stack.tail } (.value v))
    | .blkFrameK _ _ _ =>
      -- normal completion of a block body: pop the block frame
      .next (withCtl { m with stack := m.stack.tail } (.value v))
    | .beginBodyK node =>
      match node.els with
      | some e => .next (withKont m (.eval e) (.elseK node))
      | none => .next (finishRegion m node.ens (.val v))
    | .rescMatchK node exc pend ref handler rest =>
      -- v is a candidate exception-class value
      match v with
      | .ref k =>
        if (m.heap.classPayload? k).isSome then
          if isA m.heap exc k then .next (enterHandler m node exc ref handler)
          else
            match pend with
            | e :: es => .next (withKont m (.eval e)
                (.rescMatchK node exc es ref handler rest))
            | [] => .next (nextClause m node exc rest)
        else
          .next (raiseErr m Boot.typeErrorId
            "class or module required for rescue clause")
      | _ =>
        .next (raiseErr m Boot.typeErrorId
          "class or module required for rescue clause")
    | .rescueK node saved =>
      -- handler completed normally; $! restores [V]
      .next (finishRegion { m with currentExc := saved } node.ens (.val v))
    | .elseK node =>
      .next (finishRegion m node.ens (.val v))
    | .ensureK pending restore =>
      -- ensure's value is discarded; resume what was pending
      let m := match restore with
        | some old => { m with currentExc := old }
        | none => m
      match pending with
      | .val v' => .next (withCtl m (.value v'))
      | .jmp j => .next (withCtl m (.jump j))

/-- Propagate an in-flight jump one kont at a time (artifact 04 §3–6:
    markers consume matching jumps; begin regions interpose rescues/ensures;
    everything else pops). -/
def unwind (m : Machine) (j : Jump) : StepResult :=
  match m.kont with
  | [] =>
    match j with
    | .raiseJ exc => .uncaught exc m
    | .retJ _ _ =>
      -- a non-lambda block `return` whose home method already exited [V]
      .next (raiseErr m Boot.localJumpErrorId "unexpected return")
    | _ => .stuck "jump escaped the program (break/next/retry at toplevel)"
  | k :: rest =>
    let m := { m with kont := rest }
    match k with
    | .whileCondK c body | .whileBodyK c body =>
      match j with
      | .brkJ v => .next (withCtl m (.value v))
      | .nxtJ _ => .next (withKont m (.eval c) (.whileCondK c body))
      | .redoJ => .next (withKont m (.eval body) (.whileBodyK c body))  -- re-run body, skip cond [V]
      | _ => .next (withCtl m (.jump j))
    | .forStartK .. =>
      -- a jump raised while evaluating the collection is not the loop's: pass on
      .next (withCtl m (.jump j))
    | .forBodyK targets body rest coll =>
      match j with
      | .brkJ v => .next (withCtl m (.value v))           -- break value is for's value [V]
      | .nxtJ _ => forStep m targets body rest coll        -- next → next element
      | .redoJ =>                                          -- re-run body for the same element [V]
        .next (withKont m (.eval body) (.forBodyK targets body rest coll))
      | _ => .next (withCtl m (.jump j))
    | .frameK fid =>
      match j with
      | .retJ v target =>
        if target == fid then
          .next (withCtl { m with stack := m.stack.tail } (.value v))
        else  -- return targets an outer method: pop and keep unwinding
          .next (withCtl { m with stack := m.stack.tail } (.jump j))
      | .raiseJ _ => .next (withCtl { m with stack := m.stack.tail } (.jump j))
      | .brkJ _ | .nxtJ _ => .unsupported "break/next crossing a method boundary"
      | .retryJ => .unsupported "retry crossing a method boundary"
      | .redoJ => .unsupported "redo crossing a method boundary"
    | .blkFrameK fid lam brk =>
      match j with
      | .nxtJ v =>
        -- `next` ends this block invocation with value v (artifact 04 §4)
        .next (withCtl { m with stack := m.stack.tail } (.value v))
      | .brkJ v =>
        if lam then  -- `break` in a lambda returns from the lambda
          .next (withCtl { m with stack := m.stack.tail } (.value v))
        else match brk with
          | some t =>  -- return v from the method the block was passed to
            .next (withCtl { m with stack := m.stack.tail } (.jump (.retJ v t)))
          | none =>
            .next (raiseErr { m with stack := m.stack.tail }
              Boot.localJumpErrorId "break from proc-closure")
      | .retJ v target =>
        if lam && target == fid then  -- lambda's own return
          .next (withCtl { m with stack := m.stack.tail } (.value v))
        else  -- non-lambda return heads to its home method: pop and propagate
          .next (withCtl { m with stack := m.stack.tail } (.jump j))
      | .raiseJ _ => .next (withCtl { m with stack := m.stack.tail } (.jump j))
      | .retryJ => .unsupported "retry crossing a block boundary"
      -- `redo` re-runs the block body, but blkFrameK does not carry the body
      -- expr (block invocation is driven by callClosure) → gate.
      | .redoJ => .unsupported "redo in a block"
    | .beginBodyK node =>
      match j with
      | .raiseJ exc =>
        if node.rescues.isEmpty then
          .next (finishRegion m node.ens (.jmp j))
        else
          .next (nextClause m node exc node.rescues)
      | _ => .next (finishRegion m node.ens (.jmp j))
    | .rescMatchK node _ _ _ _ _ =>
      -- a clause-class expression itself raised/jumped: it supersedes, but
      -- the region's ensure still runs (artifact 04 §5)
      .next (finishRegion m node.ens (.jmp j))
    | .rescueK node saved =>
      match j with
      | .retryJ =>
        -- restart the begin body; ensure does NOT run on retry [V]
        .next (withKont { m with currentExc := saved }
          (.eval node.body) (.beginBodyK node))
      | _ =>
        .next (finishRegion { m with currentExc := saved } node.ens (.jmp j))
    | .elseK node =>
      .next (finishRegion m node.ens (.jmp j))
    | .ensureK _ restore =>
      -- a jump out of an ensure supersedes whatever was pending [V]
      let m := match restore with
        | some old => { m with currentExc := old }
        | none => m
      .next (withCtl m (.jump j))
    | _ => .next (withCtl m (.jump j))

/-- The `NameError` `undef`/`alias` raise when the target method is not defined
    on the current definee (artifact 02). CRuby names the definee `class 'C'` /
    `module 'M'`; an eigenclass definee has an address-dependent name we cannot
    reproduce byte-exactly → gate. A method CRuby *does* define on the chain but
    the model doesn't (`Kernel#binding`, …) gates Unsupported rather than raising
    a spurious `NameError` — the same fidelity split dispatch uses. -/
def undefAliasMiss (m : Machine) (name : String) : StepResult :=
  match crubyShadow m.heap (ancestors m.heap m.currentFrame.defmod) name with
  | some cname => .unsupported s!"undef/alias of unmodeled method {cname}#{name}"
  | none =>
  match m.heap.classPayload? m.currentFrame.defmod with
  | some c =>
    if c.name.startsWith "#<" then
      .unsupported "undef/alias of a missing method in a singleton class"
    else
      let kind := if c.isModule then "module" else "class"
      .next (raiseErr m Boot.nameErrorId
        s!"undefined method '{name}' for {kind} '{c.name}'")
  | none => .unsupported "undef/alias outside a class/module body"

/-- `undef n₁, n₂, …` (artifact 02): install a tombstone per name on the current
    definee, left to right. Each name must currently resolve (including
    inherited, excluding an existing tombstone) else `NameError` [V]. -/
def undefNames (m : Machine) (defmod : ObjId) : List String → StepResult
  | [] => .next (withCtl m (.value .nil))  -- `undef` evaluates to nil [V]
  | n :: rest =>
    match methodOn m.heap defmod n with
    | some (_, md) =>
      if md.undefined then undefAliasMiss m n
      else undefNames { m with heap := undefMethod m.heap defmod n } defmod rest
    | none => undefAliasMiss m n

/-- Evaluate one expression head. -/
def evalExpr (m : Machine) (e : Expr) : StepResult :=
  match e with
  | .int n => .next (withCtl m (.value (.int n)))
  | .flt x => .next (withCtl m (.value (.flt x)))
  | .str s =>
    -- string literals allocate a fresh unfrozen String [V]
    let (v, m) := Builtins.allocStr m s
    .next (withCtl m (.value v))
  | .sym s => .next (withCtl m (.value (.sym s)))
  | .tru => .next (withCtl m (.value (.bool true)))
  | .fls => .next (withCtl m (.value (.bool false)))
  | .nil => .next (withCtl m (.value .nil))
  | .self' => .next (withCtl m (.value m.currentFrame.self))
  | .var kind x =>
    match kind with
    | .lvar => .next (withCtl m (.value (m.getLocal x)))
    | .gvar => .next (withCtl m (.value (m.getGlobal x)))
    | .ivar =>
      match m.currentFrame.self with
      | .ref o =>
        let v := ((m.heap.get o).ivars.find? (·.1 == x)).map (·.2) |>.getD .nil
        .next (withCtl m (.value v))
      | _ => .next (withCtl m (.value .nil))  -- unset ivar on immediate self → nil
    | .cvar => .unsupported "class variables"
  | .vasgn kind x rhs =>
    match kind with
    | .cvar => .unsupported "class variables"
    | _ => .next (withKont m (.eval rhs) (.asgnK kind x))
  | .const n =>
    -- artifact 03 §4: lexical phase (each cref scope's OWN consts, innermost
    -- first), then inheritance phase (ancestors of the innermost class/defmod).
    let lexical := m.currentFrame.cref.firstM (fun c => constOwn m.heap c n)
    match lexical.orElse (fun _ => constLookupFrom m.heap m.currentFrame.defmod n) with
    | some v => .next (withCtl m (.value v))
    | none =>
      -- same fidelity split as methods: a constant CRuby has but we don't
      -- model gates as Unsupported; a genuine miss is a real NameError
      if crubyToplevelConstants.contains n then
        .unsupported s!"unmodeled constant {n}"
      else
        .next (raiseErr m Boot.nameErrorId s!"uninitialized constant {n}")
  | .casgn n rhs => .next (withKont m (.eval rhs) (.casgnK n))
  | .cpath base name =>
    match base with
    | none =>
      -- `::name` — absolute toplevel (Object namespace)
      match constLookup m.heap name with
      | some v => .next (withCtl m (.value v))
      | none =>
        if crubyToplevelConstants.contains name then .unsupported s!"unmodeled constant {name}"
        else .next (raiseErr m Boot.nameErrorId s!"uninitialized constant {name}")
    | some baseExpr => .next (withKont m (.eval baseExpr) (.cpathK name))
  | .cpathAsgn base name rhs =>
    -- eval order: base then rhs [V]. `::name = rhs` sets on Object.
    match base with
    | none => .next (withKont m (.eval rhs) (.cpathAsgnValK name Boot.objectId))
    | some baseExpr => .next (withKont m (.eval baseExpr) (.cpathAsgnK name rhs))
  | .send recv mname args blk =>
    let pblk : PendingBlk := match blk with
      | none => .none
      | some (.block ps ls body) => .lit ps ls body
      | some (.blockpass (some e)) => .passExpr e
      | some (.blockpass none) => .passAnon
      | some _ => .none  -- desugar guarantees blk ∈ {block, blockpass}; unreachable
    match recv with
    | some r => .next (withKont m (.eval r) (.recvK mname args pblk false))
    | none => startArgs m m.currentFrame.self true mname [] args pblk
  | .block .. => .stuck "bare block node outside send"
  | .kwargs .. => .stuck "bare kwargs node outside call position"
  | .fwd => .stuck "bare fwd (...) node outside call position"
  | .yield' args => startYield m [] args
  | .blockpass .. => .stuck "bare blockpass node outside send"
  | .if' c t e => .next (withKont m (.eval c) (.ifK t e))
  | .while' c body => .next (withKont m (.eval c) (.whileCondK c body))
  | .dowhile body cond =>
    -- run body once, then behave as `while cond`: `whileBodyK` already
    -- sequences "after body → eval cond (whileCondK) → loop", and `unwind`
    -- already routes break/next through it [V].
    .next (withKont m (.eval body) (.whileBodyK cond body))
  | .for' targets coll body =>
    .next (withKont m (.eval coll) (.forStartK targets body))
  | .def' name params body =>
    let defmod := m.currentFrame.defmod
    let md : MethodDef := { params, body, owner := defmod, cref := m.currentFrame.cref }
    let m := { m with heap := defineMethod m.heap defmod name md }
    let m := if reprSensitive.contains name then { m with reprPure := false } else m
    .next (withCtl m (.value (.sym name)))
  | .undef names => undefNames m m.currentFrame.defmod names
  | .alias' newN oldN =>
    -- `alias` captures the current definition of `oldN` (walking ancestors) and
    -- installs an independent copy under `newN` on the current definee; a later
    -- redefinition of `oldN` does not affect `newN` [V]. A tombstone or a
    -- genuine miss raises `NameError`. Returns nil.
    let defmod := m.currentFrame.defmod
    match methodOn m.heap defmod oldN with
    | some (_, md) =>
      if md.undefined then undefAliasMiss m oldN
      else
        let m := { m with heap := defineMethod m.heap defmod newN md }
        let m := if reprSensitive.contains newN then { m with reprPure := false } else m
        .next (withCtl m (.value .nil))
    | none => undefAliasMiss m oldN
  | .array elems => continueArray m [] elems
  | .hash pairs =>
    match pairs with
    | [] =>
      let (v, m) := Builtins.allocHsh m #[]
      .next (withCtl m (.value v))
    | (kE, vE) :: rest =>
      .next (withKont m (.eval kE) (.hshKeyK [] vE rest))
  | .splat _ => .unsupported "splat outside call/array position"
  | .ret e =>
    -- only meaningful inside a method (the desugar gates toplevel return)
    match e with
    | some e => .next (withKont m (.eval e) (.jumpValK .retK))
    | none => doReturn m .nil
  | .brk e =>
    match e with
    | some e => .next (withKont m (.eval e) (.jumpValK .brkK))
    | none => .next (withCtl m (.jump (.brkJ .nil)))
  | .nxt e =>
    match e with
    | some e => .next (withKont m (.eval e) (.jumpValK .nxtK))
    | none => .next (withCtl m (.jump (.nxtJ .nil)))
  | .retry' => .next (withCtl m (.jump .retryJ))
  | .redo' => .next (withCtl m (.jump .redoJ))
  | .begin' body rescues els ens =>
    -- gate rescue targets we can't bind yet
    if rescues.any (fun (_, ref, _) => match ref with
        | some (.cvar, _) => true | _ => false) then
      .unsupported "class-variable rescue target"
    else
      let node : BeginNode := { body, rescues, els, ens }
      .next (withKont m (.eval body) (.beginBodyK node))
  | .class' name sup body =>
    match sup with
    | some supExpr => .next (withKont m (.eval supExpr) (.classDefK name body))
    | none => enterClassBody m name false none body
  | .module' name body => enterClassBody m name true none body
  | .scopedClass base name body =>
    match base with
    | some baseExpr => .next (withKont m (.eval baseExpr) (.scopedClassDefK name false body))
    | none => .unsupported "absolute-scoped class definition (::Name)"
  | .scopedModule base name body =>
    match base with
    | some baseExpr => .next (withKont m (.eval baseExpr) (.scopedClassDefK name true body))
    | none => .unsupported "absolute-scoped module definition (::Name)"
  | .sclass obj body => .next (withKont m (.eval obj) (.sclassK body))
  | .defs recv name params body =>
    .next (withKont m (.eval recv) (.defsK name params body))
  | .super' args blk =>
    -- explicit `super(args)`; forward the method's block unless a literal one
    -- is given here (block-pass on super is beyond L2b)
    match blk with
    | none => startSuperArgs m [] args (methodBlk m)
    | some (.block ps ls body) =>
      let (v, m) := reifyBlock m ps ls body false
      startSuperArgs m [] args (some v)
    | some _ => .unsupported "super with a block-pass / anonymous block"
  | .zsuper blk =>
    -- bare `super`: forward the current param values + the method's block
    match blk with
    | none =>
      match zsuperArgs m with
      | some args => doSuper m args (methodBlk m)
      | none => .unsupported "zsuper param reconstruction (unsupported param shape)"
    | some _ => .unsupported "zsuper with an explicit block"
  | .seq es =>
    match es with
    | [] => .next (withCtl m (.value .nil))
    | [e] => .next (withCtl m (.eval e))
    | e :: rest => .next (withKont m (.eval e) (.seqK rest))

/-- One small step. -/
def stepFn (m : Machine) : StepResult :=
  match m.ctl with
  | .eval e => evalExpr m e
  | .value v => applyKont m v
  | .jump j => unwind m j

inductive RunResult where
  | value (v : Value) (m : Machine)
  | uncaught (exc : Value) (m : Machine)
  | unsupported (reason : String) (m : Machine)
  | outOfFuel (m : Machine)
  | stuck (msg : String) (m : Machine)

/-- Iterate `stepFn` under fuel. `outOfFuel` is distinguished from `stuck`
    from day one (sketch §5: keep co-divergence checking possible). -/
def run (fuel : Nat) (m : Machine) : RunResult :=
  match fuel with
  | 0 => .outOfFuel m
  | fuel + 1 =>
    match stepFn m with
    | .next m' => run fuel m'
    | .done v m' => .value v m'
    | .uncaught exc m' => .uncaught exc m'
    | .unsupported r => .unsupported r m
    | .stuck msg => .stuck msg m

end Interp

end RubyCore
