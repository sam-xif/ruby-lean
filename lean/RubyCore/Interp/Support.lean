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
    everything else "an instance of C" — **except** an object that has an
    eigenclass, which CRuby renders as the object itself, by `rb_any_to_s`:
    `def o.hi; end; o.zz` says `undefined method 'zz' for #<Foo:0x…>`, not
    `… for an instance of Foo` (L124). The test is only "does a singleton class
    exist" — `extend` and a bare `o.singleton_class` trigger it as much as a
    `def o.x` — and it ignores a user `inspect`/`to_s` and any ivars. A *class*
    receiver keeps "class C" even with singleton methods of its own [V]. -/
def receiverDesc (h : Heap) (v : Value) : String :=
  match v with
  | .nil => "nil"
  | .bool b => toString b
  | .ref o =>
    if o == Boot.mainId then "main"
    else match (h.get o).payload with
      | .cls c => (if c.isModule then "module " else "class ") ++ className h o
      | _ =>
        match (h.get o).eigen with
        | some _ => anyToS h o
        | Option.none => s!"an instance of {className h (h.get o).klass}"
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
    | .range lo hi excl =>
      -- `[*a..b]` / `m(*a..b)`: expand an integer range to its elements (CRuby
      -- calls Range#to_a). Non-integer / endless ranges aren't enumerable here → gate.
      match lo, hi with
      | .int a, .int b =>
        let last := if excl then b - 1 else b
        if last < a then .ok []
        else .ok ((List.range (last - a + 1).toNat).map (fun i => Value.int (a + Int.ofNat i)))
      | _, _ => .error "splat of a non-integer Range"
    | _ =>
      -- CRuby splats a non-Array via `to_a` if it responds; a *user* `to_a`
      -- is a side-effecting dispatch a pure spread can't run → gate. A user
      -- `method_missing` can serve that `to_a` too (`rb_check_funcall`), and
      -- until L133 that case did not gate: `[0, *mm_obj]` wrapped the object
      -- and the `method_missing` never ran, which is a wrong answer rather than
      -- a refusal. Splat is not a builtin, so there is no twin to defer to —
      -- the honest move is the gate the `to_a` case already had.
      if (match lookup m.heap v "to_a" with
          | some (_, md) => md.builtin.isNone
          | none => false)
         || (match lookup m.heap v "method_missing" with
             | some (_, md) => md.builtin.isNone
             | none => false) then
        .error "splat via user to_a (dispatch)"
      else .ok [v]
  | .nil => .ok []
  | _ => .ok [v]

/-- `spread`, but able to **allocate** — which a `MatchData` needs, since its
    `to_a` is the whole match plus every capture as fresh Strings.

    `_, version, revision = *path.match(REGEX)` is how `pkg_version.rb`
    destructures a match, and without this the splat wrapped the MatchData itself:
    the first target got the MatchData and every other bound to nil. That is a
    *wrong answer*, not a gate, because `[md]` is a perfectly good one-element
    spread and nothing downstream could tell (L113). -/
def spreadA (m : Machine) (v : Value) : Except String (List Value × Machine) :=
  match v with
  | .ref o =>
    match (m.heap.get o).payload with
    | .mdata subject caps _ =>
      let bin := (m.heap.get o).binary
      .ok (caps.toList.foldl (fun (acc, m) sp =>
        match sp with
        | some (a, b) =>
          let (sv, m) := Builtins.allocStrEnc m (Builtins.charSlice subject a b) bin
          (acc ++ [sv], m)
        | none => (acc ++ [Value.nil], m)) ([], m))
    | _ => (spread m v).map (fun vs => (vs, m))
  | _ => (spread m v).map (fun vs => (vs, m))

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

/-- The innermost active frame whose block *is* this proc — i.e. the method the
    block was passed to. `break` inside a proc called via `#call` returns from
    that method (and is a `LocalJumpError` once it has exited) [V], so this is
    the `brk` target for the `Proc#call` path (L66). -/
def blockOwner (m : Machine) (p : Value) : Option FrameId :=
  m.stack.find? fun fid =>
    match (m.frames.getD fid default).callBlk with
    | some b => b.identEq p
    | none => false

/-- Invoke a closure: push a block frame parented at `captured`, bind params
    (lenient for blocks/procs — pad nil, drop extras, auto-splat a single
    Array across ≥2 positionals; strict for lambdas), evaluate the body under
    a `blkFrameK` marker (artifact 04 §2). `brk` is the method a `break`
    returns from. -/
def callClosure (m : Machine) (cl : Closure) (args : List Value)
    (brk : Option FrameId) (selfOv : Option Value := none)
    (defmodOv : Option ObjId := none) : StepResult :=
  let sp? := classifySimple cl.params
  if sp?.isNone then
    .unsupported "unmodeled block param kind (optional/keyword/forwarding/destructuring)"
  else
  let sp := sp?.getD ⟨[], none, [], none⟩
  let pre := sp.pre; let rest? := sp.rest?; let post := sp.post
  let required := pre.length + post.length
  let autoSplat :=
    !cl.lam && args.length == 1 && (required ≥ 2 || (rest?.isSome && required ≥ 1))
  -- A block that auto-splats asks its single argument for `to_ary`
  -- (`rb_vm_callee_setup_block_arg` → `rb_check_array_type`), so a user `to_ary`
  -- — or a `method_missing` serving one — decides the binding, and a non-Array
  -- answer raises. Until L133 this arm only looked at the payload, so
  -- `[Pair.new].each { |x, y| … }` bound the object to `x` and nil to `y` where
  -- CRuby binds the two halves: a wrong answer, not a refusal. `callClosure` is
  -- not a builtin and has no twin to defer to, so the honest move is to gate.
  if autoSplat && (match args.head? with
                   | some a => (Builtins.arrPayload? m.heap a).isNone
                               && Builtins.mayDispatchToAry m.heap a
                   | none => false) then
    .unsupported "block auto-splat via user to_ary (dispatch)"
  else
  let args :=
    if autoSplat then
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
    -- `selfOv`/`defmodOv` are the `instance_eval`/`class_eval` rebinding (L64):
    -- everything else about the block frame (captured chain, home, cref, lam) is
    -- unchanged, so free variables, `return` and constant lookup keep the
    -- block's own semantics while `self` / the `def` target move.
    let frame : Frame :=
      { self := selfOv.getD capF.self, defmod := defmodOv.getD capF.defmod,
        blk := capF.blk,
        locals, kind := .block, captured := some cl.captured,
        home := cl.home, lam := cl.lam, cref := capF.cref }
    let fid := m.frames.size
    let m := { m with frames := m.frames.push frame, stack := fid :: m.stack }
    .next (withKont m (.eval cl.body) (.blkFrameK fid cl.lam brk cl args))

/-- `$1`…`$9`, `$&`, `` $` `` and `$'` are **views of `$~`**, not stored
    globals: CRuby derives them from the last `MatchData` on every read. Storing
    them instead would need every failed match to clear nine slots, and would
    still get `defined?($3)` wrong. Returns `none` for any other global name, so
    the ordinary path is untouched. (L101.) -/
def matchViewIdx? (x : String) : Option Nat :=
  if x.length == 2 then
    let c := x.get ⟨1⟩
    if c.isDigit && c != '0' then some (c.toNat - '0'.toNat)
    else if c == '&' then some 0
    else none
  else none

/-- Is `x` one of those views, rather than a stored global? **Purely syntactic** —
    the name decides, not the machine. Factored out and named so the metatheory's
    fragment predicate can exclude exactly these names and cannot drift from the
    rule `matchGlobal` implements: `Step.varGvar` said a gvar read is a plain
    `getGlobal`, which stopped being true when L101 put `matchGlobal` in front of
    it, and nothing noticed for 24 commits because `Proof/` is off the default
    build target (L119). -/
def isMatchView (x : String) : Bool :=
  (matchViewIdx? x).isSome || x == "$`" || x == "$'"

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
