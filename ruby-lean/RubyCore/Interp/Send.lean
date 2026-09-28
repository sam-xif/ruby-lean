import RubyCore.Interp.Copy
import RubyCore.Interp.Require
import RubyCore.Interp.Forwardable

/-!
Dispatch proper: `invoke`, `super`/`zsuper`, and the argument/keyword/block
evaluation entry points (`startArgs`, `startKwargs`, `finishSend`, `doYield`).

Split out of `RubyCore/Interp.lean` (L99) with no behaviour change. The helpers
in this machine are deliberately *not* mutually recursive — each performs one
transition — so the file cuts along that existing order and the import chain
records it.
-/

namespace RubyCore

namespace Interp

/-- All args evaluated → dispatch (artifact 02 §3 SEND-INVOKE). -/
def invoke (m : Machine) (recv : Value) (implicit : SendSite) (mname : String)
    (args : List Value) (blk : Option Value) (kw : List (Value × Value) := []) : StepResult :=
  -- `send`/`public_send`/`__send__`: re-dispatch the (symbol/string) first arg on
  -- `recv` with the rest. Only when unshadowed by a user `send` (rare) [V].
  if (mname == "send" || mname == "public_send" || mname == "__send__")
      && (lookup m.heap recv mname).isNone then
    match args with
    | nameArg :: rest =>
      match symOrStr m nameArg with
      | some m2 => invoke m recv (reflectiveSite mname) m2 rest blk kw
      | none => invokeDispatch m recv implicit mname args blk kw
    | [] => invokeDispatch m recv implicit mname args blk kw
  else
  match recv with
  | .ref o =>
    match (m.heap.get o).payload with
    | .hsh xs =>
      -- Hash default_proc (L42): on `h[k]` with a *missing* key, call the proc
      -- with `(h, k)` and use its result as the value of `h[k]` (the proc may also
      -- mutate `h`, e.g. `h[k] = …`). Only for a `prc` default; a present key or a
      -- `val`/absent default falls to the normal builtin dispatch.
      match mname, args, (m.heap.get o).hashDflt with
      | "[]", [key], some (.prc bo) =>
        if xs.any (fun (k, _) => valueEql m.heap k key) then
          invokeDispatch m recv implicit mname args blk kw
        else
          match (m.heap.get bo).payload with
          | .proc cl => callClosure m cl [recv, key] none
          | _ => invokeDispatch m recv implicit mname args blk kw
      | _, _, _ => invokeDispatch m recv implicit mname args blk kw
    | .cls _ =>
      -- `Math` module functions (`Math.sqrt`/`exp`/`log`): a real double transform,
      -- special-cased on the receiver id since they are singleton methods of the
      -- `Math` constant (no eigenclass machinery at boot). Args coerce Int→Float.
      if o == Boot.regexpId && (mname == "escape" || mname == "quote" || mname == "union") then
        -- `Regexp.escape`/`.union` are singleton methods of the `Regexp`
        -- constant, dispatched here for the same reason `Math.sqrt` is: the
        -- boot heap installs builtins as *instance* methods, and these are not
        -- (L106).
        match Builtins.run ("Regexp#" ++ mname) recv args m with
        | .ok v m => .next (withCtl m (.value v))
        | .err cls msg m => .next (raiseErr m cls msg)
        | .throwV tv m => .next (withCtl m (.jump (.raiseJ tv)))
        | .frozen recv m => raiseFrozen m recv
        | .unsupported r => .unsupported r
      else if o == Boot.mathId then
        let f? := fun (v : Value) => match v with
          | .int n => some (Float.ofInt n) | .flt x => some x | _ => none
        match mname, args with
        | "sqrt", [x] => match f? x with
          | some d => if d < 0 then .unsupported "Math.sqrt of negative (DomainError)"
                      else .next (withCtl m (.value (.flt d.sqrt)))
          | none => .unsupported "Math.sqrt non-numeric"
        | "exp", [x] => match f? x with
          | some d => .next (withCtl m (.value (.flt d.exp)))
          | none => .unsupported "Math.exp non-numeric"
        | "log", [x] => match f? x with
          | some d => if d ≤ 0 then .unsupported "Math.log of non-positive (DomainError)"
                      else .next (withCtl m (.value (.flt d.log)))
          | none => .unsupported "Math.log non-numeric"
        | "log", [x, b] => match f? x, f? b with
          | some d, some bb =>
            if d ≤ 0 || bb ≤ 0 then .unsupported "Math.log of non-positive"
            else .next (withCtl m (.value (.flt (d.log / bb.log))))
          | _, _ => .unsupported "Math.log non-numeric"
        | _, _ => invokeDispatch m recv implicit mname args blk kw
      else invokeDispatch m recv implicit mname args blk kw
    | _ => invokeDispatch m recv implicit mname args blk kw
  | _ => invokeDispatch m recv implicit mname args blk kw
termination_by args.length
decreasing_by
  -- the ONLY self-recursion is `send`/`public_send`/`__send__` unwrapping, which
  -- strips the (name) head arg: `args = nameArg :: rest`, so `rest.length` drops.
  simp_wf
where
  invokeDispatch (m : Machine) (recv : Value) (implicit : SendSite) (mname : String)
      (args : List Value) (blk : Option Value) (kw : List (Value × Value)) : StepResult :=
  let chain := ancestors m.heap (classOf m.heap recv)
  match lookup m.heap recv mname with
  | some (owner, md) =>
    if md.undefined then
      -- `undef` tombstone: the walk stopped here, dispatch as a miss.
      invokeMethodMissing m recv implicit mname args blk (kw := kw)
    else
    -- Dispatch fidelity: if CRuby defines `mname` on a class BETWEEN the
    -- receiver's class and our resolved owner, CRuby would dispatch there —
    -- we'd be running the wrong method. Gate. (Builtins are exempt only
    -- from their own owner downward.)
    -- Exception (L62): a **prelude**-defined method *is* our model of the CRuby
    -- builtin of that name, so the "between" class CRuby would dispatch to is
    -- exactly what the prelude implements (`Array#select` resolved to the
    -- prelude's `Enumerable#select`). Suppress the gate for prelude owners; the
    -- fidelity obligation moves to the prelude's body, where difftest checks it.
    let between := if md.fromPrelude then [] else chain.takeWhile (· != owner)
    match crubyResolvedShadow m.heap between mname md with
    | some cname => .unsupported s!"unmodeled builtin would shadow: {cname}#{mname}"
    | none =>
    -- Visibility (L71) is checked *after* the shadow gate: when CRuby would
    -- dispatch to a method we don't model, the honest answer is Unsupported, not
    -- a NoMethodError about *our* resolution (test_yjit_120 — a toplevel
    -- `def getbyte`, now private, shadowed by the real `String#getbyte`).
    match visError? m recv implicit md mname with
    | some _ =>
      invokeMethodMissing m recv implicit mname args blk
        (if md.visibility == .priv then .privateCall else .protectedCall) kw
    | none =>
      match md.builtin with
      | some bid =>
        if bid.startsWith "Main#" then
          let (args, m) := appendKwHash m args kw
          callMainMethod m recv bid args blk else
        if bid == "Object#inspect" then callObjectInspect m recv args kw else
        if bid == "Object#raise" || bid == "Object#fail" then callRaise m args kw else
        if bid == "Exception.exception" then callConstruct m recv args blk kw else
        if bid == "Exception#exception" then callExceptionCopy m recv args kw else
        if bid == "Exception#to_s" then callExceptionMessage m recv args kw else
        if bid == "UncaughtThrowError#to_s" then callUncaughtMessage m recv args kw else
        if nativeCloneBid bid then callNativeClone m recv args kw else
        if bid == "Object#initialize_clone" then callNativeInitializeClone m recv args kw else
        if bid == "String#initialize_copy" then callCoreCopy m Boot.stringId recv args kw else
        if bid == "Array#initialize_copy" then callCoreCopy m Boot.arrayId recv args kw else
        if bid == "Hash#initialize_copy" then callCoreCopy m Boot.hashId recv args kw else
        if bid == "Class#new" || bid == "Module#new" then callConstruct m recv args blk kw else
        if bid == "Class#allocate" then callAllocate m recv args kw else
        if bid == "Module#const_set" then callConstSet m recv args kw else
        if bid == "Class#initialize" then callClassInitialize m recv args blk kw else
        if bid == "Module#initialize" then callModuleInitialize m recv args blk kw else
        if ["String#initialize", "Array#initialize", "Hash#initialize", "Exception#initialize"].contains bid then
          callCoreInitialize m bid recv args blk kw else
        if bid == "Object#__forwardable_compile" then compileForwardable m args else
        if requireBid bid then callRequire m bid args kw else
        if enumBid bid then callEnumerator m bid recv args blk kw else
        if nativeIteratorBid bid then callNativeIterator m bid recv args blk kw else
        if procCallBid bid then callProcBuiltin m recv args kw else
        if arrayMapBid bid then callArrayMapBuiltin m recv mname args blk kw else
        if bid == "String#+" then callStringPlusBuiltin m recv args kw else
        -- Deferring to a prelude twin: when a builtin's answer would require a
        -- *dispatch* it cannot perform, it hands the call to a prelude method
        -- under a different name, which then recurses through ordinary dispatch.
        -- Two reasons today — repr purity (L116: the receiver, or something it
        -- contains, overrides `inspect`/`to_s`) and the coerce protocol (L123: a
        -- numeric operator whose argument may answer `coerce`). Keyed on the
        -- resolved bid, so nothing else pays for the check; and the twin's name
        -- shadows nothing, so no purity answer changes.
        -- Resolved directly rather than re-entered through dispatch: this *is*
        -- the dispatch path, and re-entering it with the same arguments is what
        -- the termination measure forbids.
        match Builtins.deferTwin? m.heap bid recv args with
        | some slow =>
          match methodOn m.heap (classOf m.heap recv) slow with
          | some (_, md2) => enterUserMethod m recv slow md2 args blk kw
          | none => .unsupported s!"prelude twin {slow} is missing from the prelude"
        | none =>
        -- A block changes what several builtins mean (L63). Our arms are
        -- blockless, so defer to a prelude definition of the same name higher in
        -- the chain (`Array#sort {}` → `Enumerable#sort`) rather than dropping
        -- the block on the floor; gate if there is none.
        if blk.isSome && Builtins.blockSensitiveBids.contains bid then
          match lookupAbove m.heap recv owner mname with
          | some (_, md2) =>
            if md2.builtin.isNone then enterUserMethod m recv mname md2 args blk kw
            else .unsupported s!"block passed to builtin {bid}"
          | none => .unsupported s!"block passed to builtin {bid}"
        else
        -- builtins have no keyword params in the model: keywords collapse to a
        -- trailing positional Hash (Ruby-3 [V]).
        let (args, m) := appendKwHash m args kw
        match Builtins.run bid recv args m with
        | .ok v m => .next (withCtl m (.value v))
        | .err cls msg m => .next (raiseErr m cls msg)
        | .throwV v m => .next (withCtl m (.jump (.raiseJ v)))
        | .frozen recv m => raiseFrozen m recv
        | .unsupported r => .unsupported r
      | none =>
        -- Native singleton shadows are checked in the chain before `owner`,
        -- just like instance shadows. A real user override at `owner` wins.
        enterUserMethod m recv mname md args blk kw
  | none =>
    dispatchMiss m recv implicit mname args blk kw

/-- The method `super` re-dispatches to: the first entry for `mname` strictly *after*
    `dm` on `k`'s ancestor chain. Named rather than inlined into `doSuper` (L212) so
    that the static invariant's `SuperOk` clause and the dispatch lemma can refer to
    the same function instead of to a copy of it — a copy is what made `rw` fail, and
    the fix belongs here rather than in a proof that has to reproduce the shape. -/
def superFound (h : Heap) (k dm : ObjId) (mname : String) : Option (ObjId × MethodDef) :=
  lookupInChain h (((ancestors h k).dropWhile (· != dm)).drop 1) mname

/-- Super-dispatch (artifact 02 §2): re-run the current method name starting
    *after* its `defmod` in `self`'s ancestor chain, keeping the same `self` and
    forwarding/passing `blk`. A miss invokes method_missing with the super-call
    reason; the native handler raises "super: no superclass method …" [V].
    `super` is evaluated in the enclosing method
    activation (`methodFrameOf`), so it works from inside a block too. -/
def doSuper (m : Machine) (args : List Value) (blk : Option Value)
    (kw : List (Value × Value) := []) : StepResult :=
  let f := m.frames.getD (methodFrameOf m) default
  if f.meth == "" then .unsupported "super outside a method"
  else
    let self := f.self
    let scope := f.superScope.getD (classOf m.heap self)
    let chain := (ancestors m.heap scope).dropWhile (· != f.methodOwner.getD f.defmod) |>.drop 1
    match superFound m.heap scope (f.methodOwner.getD f.defmod) f.meth with
    | some (owner, md) =>
      if md.undefined then
        invokeMethodMissing m self .implicit f.meth args blk .superCall kw
      else
      let between := if md.fromPrelude then [] else chain.takeWhile (· != owner)
      match crubyResolvedShadow m.heap between f.meth md with
      | some cname => .unsupported s!"unmodeled builtin would shadow super: {cname}#{f.meth}"
      | none =>
      match md.builtin with
      | some bid =>
        if bid.startsWith "Main#" then
          let (args, m) := appendKwHash m args kw
          callMainMethod m self bid args blk else
        if bid == "Object#inspect" then callObjectInspect m self args kw else
        if bid == "Object#raise" || bid == "Object#fail" then callRaise m args kw else
        if bid == "Exception.exception" then callConstruct m self args blk kw else
        if bid == "Exception#exception" then callExceptionCopy m self args kw else
        if bid == "Exception#to_s" then callExceptionMessage m self args kw else
        if bid == "UncaughtThrowError#to_s" then callUncaughtMessage m self args kw else
        if nativeCloneBid bid then callNativeClone m self args kw else
        if bid == "Object#initialize_clone" then callNativeInitializeClone m self args kw else
        if bid == "String#initialize_copy" then callCoreCopy m Boot.stringId self args kw else
        if bid == "Array#initialize_copy" then callCoreCopy m Boot.arrayId self args kw else
        if bid == "Hash#initialize_copy" then callCoreCopy m Boot.hashId self args kw else
        if bid == "Class#new" || bid == "Module#new" then callConstruct m self args blk kw else
        if bid == "Class#allocate" then callAllocate m self args kw else
        if bid == "Module#const_set" then callConstSet m self args kw else
        if bid == "Class#initialize" then callClassInitialize m self args blk kw else
        if bid == "Module#initialize" then callModuleInitialize m self args blk kw else
        if ["String#initialize", "Array#initialize", "Hash#initialize", "Exception#initialize"].contains bid then
          callCoreInitialize m bid self args blk kw else
        if bid == "Object#__forwardable_compile" then compileForwardable m args else
        if requireBid bid then callRequire m bid args kw else
        if enumBid bid then callEnumerator m bid self args blk kw else
        if nativeIteratorBid bid then callNativeIterator m bid self args blk kw else
        if procCallBid bid then callProcBuiltin m self args kw else
        if arrayMapBid bid then callArrayMapBuiltin m self f.meth args blk kw else
        if bid == "String#+" then callStringPlusBuiltin m self args kw else
        match Builtins.deferTwin? m.heap bid self args with
        | some slow =>
          match methodOn m.heap (classOf m.heap self) slow with
          | some (_, md2) => enterUserMethod m self slow md2 args blk kw
          | none => .unsupported s!"prelude twin {slow} is missing from the prelude"
        | none =>
        -- builtins take keywords as a trailing positional Hash (Ruby-3 [V])
        let (args, m) := appendKwHash m args kw
        match Builtins.run bid self args m with
        | .ok v m => .next (withCtl m (.value v))
        | .err cls msg m => .next (raiseErr m cls msg)
        | .throwV v m => .next (withCtl m (.jump (.raiseJ v)))
        | .frozen recv m => raiseFrozen m recv
        | .unsupported r => .unsupported r
      | none =>
        let md := { md with superScope := md.superScope.orElse (fun _ => f.superScope) }
        enterUserMethod m self f.meth md args blk kw
    | none =>
      match crubyShadow m.heap chain f.meth with
      | some cname => .unsupported s!"unmodeled super method {cname}#{f.meth}"
      | none =>
        invokeMethodMissing m self .implicit f.meth args blk .superCall kw

/-- Args that bare `super` forwards: the *current* values of the enclosing
    method's formal parameters — read from the method frame's locals, a splat
    param spreading its array, keyword params re-bundled as keywords (artifact 02
    §2) [V: `x=x+1; super` forwards the reassigned value]. `none` if the param
    shape is not reconstructible: a `define_method` body (no formals — CRuby
    raises, see L66) or destructuring params, whose synthetic slots are dropped
    after binding (L70). -/
def zsuperArgsOf (h : Heap) (f : Frame) : Option (List Value × List (Value × Value)) :=
  -- The running body's own params, carried on the frame (L108): looking them up
  -- by `f.meth` would find whatever *currently* answers that name, which for an
  -- aliased body is a different method.
  match (if f.meth.isEmpty then none else some f) with
  | some _ =>
    if f.runFromDM then none else
    match classifyFull f.runParams with
    | none => none
    | some fp =>
      if !fp.destrs.isEmpty then none else
      let readL : String → Value := fun n =>
        (f.locals.find? (·.1 == n)).map (·.2) |>.getD .nil
      let spreadRest : Option (List Value) := match fp.rest? with
        | none => some []
        | some rname =>
          match readL rname with
          | .ref o => match (h.get o).payload with
            | .arr xs => some xs.toList
            | _ => none
          | _ => none
      match spreadRest with
      | none => none
      | some restV =>
        let pos := fp.pre.map readL ++ fp.opt.map (fun p => readL p.1)
          ++ restV ++ fp.post.map readL
        let kwPairs := fp.keys.map (fun p => (Value.sym p.1, readL p.1))
        let kwRest : Option (List (Value × Value)) := match fp.kwrest? with
          | none => some []
          | some none => some []            -- anonymous `**`: nothing to read back
          | some (some kr) =>
            match readL kr with
            | .ref o => match (h.get o).payload with
              | .hsh ps => some ps.toList
              | _ => none
            | .nil => some []
            | _ => none
        match kwRest with
        | none => none
        | some kwr => some (pos, kwPairs ++ kwr)
  | none => none


/-- The `Machine` form, and the split is L214's: `StackCtx` is indexed by
    `(heap, frames, stack)` and has no `Machine` to hand, so the clause `zsuper` needs
    has to be statable about **one frame**. Same lesson as `superFound` at L212 — a
    definition the proof needs to name belongs in the code. -/
def zsuperArgs (m : Machine) : Option (List Value × List (Value × Value)) :=
  zsuperArgsOf m.heap (m.frames.getD (methodFrameOf m) default)

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

/-- Queued native calls use the same lookup and constructor protocol. -/
def invokeQueued (m : Machine) (recv : Value) (site : SendSite) (name : String)
    (args : List Value) (blk : Option Value) (kw : List (Value × Value)) : StepResult :=
  invoke m recv site name args blk kw

/-- All args in → resolve the pending block and dispatch. A literal block is
    reified here (capturing the caller frame); `proc`/`lambda`/`Proc.new` with
    a block capture rather than call; a `&e` block-pass evaluates `e` last
    (eval order) then coerces. -/
def finishSend (m : Machine) (recv : Value) (implicit : SendSite) (mname : String)
    (args : List Value) (pblk : PendingBlk) (kw : List (Value × Value) := []) : StepResult :=
  match pblk with
  | .passExpr e => .next (withKont m (.eval e) (.blkCoerceK recv implicit mname args kw))
  | .lit ps ls body =>
    -- `lambda`/`proc` are **`Kernel` methods**, so a user definition of either name
    -- *shadows* them: a toplevel `def lambda` is a private instance method on `Object`,
    -- and `Kernel` is included *in* `Object`, so `Object`'s own entry comes first in the
    -- ancestor walk and `lambda { 1 }` calls the user's method with the block as an
    -- ordinary block argument [V]. Same shape (and the same `builtin.isNone` test) as the
    -- `X.new { … }` case below, which already had to make this distinction.
    --
    -- Found by the semantic ladder (`Denote/Sem/`) (`found-issues.md` §A5): the special case ran
    -- *before any method lookup*, so the name was unshadowable here and the model returned
    -- a Proc where CRuby raised.
    let shadowed :=
      match methodOn m.heap (classOf m.heap recv) mname with
      | some (_, md) => md.builtin.isNone && !md.undefined
      | none => false
    let mkLam := implicit == .implicit && mname == "lambda" && !shadowed
    let (v, m) := reifyCallBlock m ps ls body mkLam
    if implicit == .implicit && (mname == "lambda" || mname == "proc") && !shadowed then
      .next (withCtl m (.value v))
    else invoke m recv implicit mname args (some v) kw
  | .passAnon => invoke m recv implicit mname args m.currentFrame.blk kw
  | .none => invoke m recv implicit mname args none kw

/-- Evaluate the pending call-site `kwargs` entries (values left to right,
    `**h` splats expanded), then dispatch. Duplicate keys keep first position,
    last value (as hash literals do [V]). -/
def startKwargs (m : Machine) (recv : Value) (implicit : SendSite) (mname : String)
    (posArgs : List Value) (kwacc : List (Value × Value)) (entries : List KwEntry)
    (pblk : PendingBlk) : StepResult :=
  match entries with
  | [] => finishSend m recv implicit mname posArgs pblk kwacc
  | .pair k valE :: rest =>
    .next (withKont m (.eval valE) (.kwPairK k rest kwacc recv implicit mname posArgs pblk))
  | .dyn keyE valE :: rest =>
    -- Key first, then value: `f(k => v)` evaluates left to right like a hash
    -- literal [V].
    .next (withKont m (.eval keyE) (.kwDynKeyK valE rest kwacc recv implicit mname posArgs pblk))
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
def startArgs (m : Machine) (recv : Value) (implicit : SendSite) (mname : String)
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

/-- For invokes each as an ordinary explicit send. Its hidden callback keeps
    the literal-call break boundary and shares the enclosing local environment. -/
def startFor (m : Machine) (targets : List (TargetKind × String)) (body : Expr)
    (multiple : Bool) (collection : Value) : StepResult :=
  let params := if multiple then [Param.rest none] else [Param.req "<for argument>"]
  let (block, m) := reifyCallBlock m params [] body false
  let m := match block with
    | .ref o => match (m.heap.get o).payload with
      | .proc cl => { m with heap := m.heap.set o { m.heap.get o with
          payload := .proc { cl with forTargets := some targets, forMultiple := multiple } } }
      | _ => m
    | _ => m
  invoke m collection .explicit "each" [] (some block)

/-- Class variables use lexical nesting, skipping singleton-class scopes.
    No enclosing ordinary class/module means an access-from-toplevel error;
    defined? alone can still ask whether Object has the variable. -/
def cvarScope (m : Machine) : Option ObjId :=
  m.currentFrame.cref.find? fun k =>
    (m.heap.classPayload? k).any (fun cp => cp.attached.isNone)

/-- Does `mname` resolve on `recv` for `defined?` purposes: `some true` = yes
    ("method"), `some false` = genuinely not defined (nil), `none` = CRuby has it
    but we don't model it (gate — the L5 fidelity split; `defined?` must not
    answer nil for a method that really exists). `method_missing` is deliberately
    *not* consulted: CRuby's `defined?` doesn't either [V]. -/
def definedMethod? (m : Machine) (recv : Value) (mname : String)
    (site : SendSite := .implicit) : Option Bool :=
  -- CRuby routes an *explicit-receiver* `defined?` through `respond_to?`, so a
  -- user override of it (or of `respond_to_missing?`) is observable — and can even
  -- have side effects (test_yjit_023). We cannot dispatch from here → gate.
  if ["respond_to?", "respond_to_missing?"].any (fun n =>
      match lookup m.heap recv n with
      | some (_, md) => md.builtin.isNone
      | none => false) then none
  else
  match methodEntryInChain m.heap (ancestors m.heap (classOf m.heap recv)) mname with
  | some (_, md) =>
    -- visibility counts: `defined?(obj.private_m)` is nil [V] (L71)
    if md.undefined then some false
    else some (visError? m recv site md mname).isNone
  | none =>
    if (crubyShadow m.heap (ancestors m.heap (classOf m.heap recv)) mname).isSome then none
    else some false

end Interp

end RubyCore
