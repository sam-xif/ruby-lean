import RubyCore.Interp.Reflect

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

/-- All args evaluated → dispatch (artifact 02 §3 SEND-INVOKE). A Proc
    receiver called via call/()/[]/yield runs its closure directly (a builtin
    cannot push a frame). -/
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
    | .proc cl =>
      if mname == "call" || mname == "()" || mname == "[]" || mname == "yield" then
        if kw.isEmpty then callClosure m cl args (blockOwner m recv)
        else .unsupported "keyword arguments to a Proc call"
      else invokeDispatch m recv implicit mname args blk kw
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
    | .cls c =>
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
      else invokeMaybeNew m recv o c implicit mname args blk kw
    | _ => invokeDispatch m recv implicit mname args blk kw
  | _ => invokeDispatch m recv implicit mname args blk kw
termination_by args.length
decreasing_by
  -- the ONLY self-recursion is `send`/`public_send`/`__send__` unwrapping, which
  -- strips the (name) head arg: `args = nameArg :: rest`, so `rest.length` drops.
  simp_wf
where
  invokeMaybeNew (m : Machine) (recv : Value) (o : ObjId) (c : ClassPayload)
      (implicit : SendSite) (mname : String) (args : List Value) (blk : Option Value)
      (kw : List (Value × Value)) : StepResult :=
      -- `Class#new` on a class with a user `initialize` must allocate then run
      -- `initialize` (a frame the builtin cannot push); yield the instance via
      -- `newK`. Special-payload subclasses (String/Array/Exception/…) need
      -- allocation we don't model → gate. No user init ⇒ fall to the builtin.
      -- A **user `self.new`** wins over this interception: it is an ordinary
      -- singleton method and CRuby dispatches to it, not to `Class#new`.
      -- `T::Helpers#abstract!` installs exactly that (the abstract class must
      -- refuse to instantiate, L105), and without this check the interception
      -- allocated an instance and never consulted it.
      let userNew := match (m.heap.get o).eigen with
        | some e => match methodOn m.heap e "new" with
          | some (_, md) => md.builtin.isNone && !md.undefined
          | none => false
        | none => false
      if mname == "new" && !c.isModule && !userNew then
        match userInit? m.heap o with
        | some md =>
          -- Allocate, then run the user `initialize` (a frame the builtin cannot
          -- push). For a subclass of String/Array/Hash/Exception the instance
          -- starts with that class's *empty* payload, so `super` inside
          -- `initialize` can fill it (L70); a Proc/Range/Random subclass has no
          -- such allocator and still gates.
          match Builtins.allocatableCore m.heap o, (ancestors m.heap o).any
              (fun a => Builtins.payloadCoreClasses.contains a || a == Boot.exceptionId) with
          | none, true => .unsupported "Class#new with user initialize on a special-payload subclass"
          | core?, _ =>
            let payload := match core? with
              | some core => Builtins.emptyCorePayload core
              | none => Payload.none
            let (io, h) := m.heap.alloc { klass := o, payload }
            let inst := Value.ref io
            let m := { m with heap := h, kont := .newK inst :: m.kont }
            enterUserMethod m inst "initialize" md args blk kw
        | none => invokeDispatch m recv implicit mname args blk kw
      else invokeDispatch m recv implicit mname args blk kw
  invokeDispatch (m : Machine) (recv : Value) (implicit : SendSite) (mname : String)
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
    -- Exception (L62): a **prelude**-defined method *is* our model of the CRuby
    -- builtin of that name, so the "between" class CRuby would dispatch to is
    -- exactly what the prelude implements (`Array#select` resolved to the
    -- prelude's `Enumerable#select`). Suppress the gate for prelude owners; the
    -- fidelity obligation moves to the prelude's body, where difftest checks it.
    let between := if md.fromPrelude then [] else chain.takeWhile (· != owner)
    match crubyShadow m.heap between mname with
    | some cname => .unsupported s!"unmodeled builtin would shadow: {cname}#{mname}"
    | none =>
    -- Visibility (L71) is checked *after* the shadow gate: when CRuby would
    -- dispatch to a method we don't model, the honest answer is Unsupported, not
    -- a NoMethodError about *our* resolution (test_yjit_120 — a toplevel
    -- `def getbyte`, now private, shadowed by the real `String#getbyte`).
    match visError? m recv implicit md mname with
    | some sr => sr
    | none =>
      match md.builtin with
      | some bid =>
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
        -- `raise C` / `raise C, msg` where `C` defines a *user* `initialize`:
        -- CRuby builds the exception with `C.new(…)`, so the initializer (and any
        -- `super` into `Exception#initialize`) must run — a frame this builtin
        -- cannot push, so it is finished by a `raiseNewK` kont (L70). Keyed on the
        -- resolved *bid*, so no other dispatch pays for the check.
        if bid == "Object#raise" then
          match args with
          | (.ref k) :: rest =>
            match m.heap.classPayload? k, userInit? m.heap k with
            | some c, some md' =>
              if c.isModule || rest.length > 1 then
                match Builtins.run bid recv args m with
                | .ok v m => .next (withCtl m (.value v))
                | .err cls msg m => .next (raiseErr m cls msg)
                | .throwV v m => .next (withCtl m (.jump (.raiseJ v)))
                | .unsupported r => .unsupported r
              else
                let (io, h) := m.heap.alloc { klass := k, payload := .exc "" }
                let inst := Value.ref io
                let m := { m with heap := h, kont := .raiseNewK inst :: m.kont }
                enterUserMethod m inst "initialize" md' rest none
            | _, _ =>
              match Builtins.run bid recv args m with
              | .ok v m => .next (withCtl m (.value v))
              | .err cls msg m => .next (raiseErr m cls msg)
              | .throwV v m => .next (withCtl m (.jump (.raiseJ v)))
              | .unsupported r => .unsupported r
          | _ =>
            match Builtins.run bid recv args m with
            | .ok v m => .next (withCtl m (.value v))
            | .err cls msg m => .next (raiseErr m cls msg)
            | .throwV v m => .next (withCtl m (.jump (.raiseJ v)))
            | .unsupported r => .unsupported r
        else
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
        | .unsupported r => .unsupported r
      | none =>
        -- Same L62 exception as the instance path above: a **prelude**-defined
        -- singleton method *is* our model of the CRuby singleton of that name
        -- (`String.try_convert`, `Array.try_convert`, `Regexp.last_match`), so
        -- the gate must not fire on it. Without this the prelude cannot supply a
        -- class method at all, which is what pushed those three into `invoke` as
        -- hand-written special cases in the first place (L115).
        match (if md.fromPrelude then none else crubySingletonShadow m.heap recv mname) with
        | some cname => .unsupported s!"unmodeled singleton method {cname}.{mname}"
        | none =>
          -- a RubyCore-defined method: bind params + push the activation
          enterUserMethod m recv mname md args blk kw
  | none =>
    let (args, m) := appendKwHash m args kw
    dispatchMiss m recv implicit mname args blk

/-- The method `super` re-dispatches to: the first entry for `mname` strictly *after*
    `dm` on `k`'s ancestor chain. Named rather than inlined into `doSuper` (L212) so
    that the static invariant's `SuperOk` clause and the dispatch lemma can refer to
    the same function instead of to a copy of it — a copy is what made `rw` fail, and
    the fix belongs here rather than in a proof that has to reproduce the shape. -/
def superFound (h : Heap) (k dm : ObjId) (mname : String) : Option (ObjId × MethodDef) :=
  ((ancestors h k).dropWhile (· != dm) |>.drop 1).firstM fun c =>
    match h.classPayload? c with
    | some cp => (cp.methods.find? (·.1 == mname)).map (fun (_, md) => (c, md))
    | none => none

/-- Super-dispatch (artifact 02 §2): re-run the current method name starting
    *after* its `defmod` in `self`'s ancestor chain, keeping the same `self` and
    forwarding/passing `blk`. A miss raises `NoMethodError "super: no superclass
    method '{m}' for {recv}"` [V]. `super` is evaluated in the enclosing method
    activation (`methodFrameOf`), so it works from inside a block too. -/
def doSuper (m : Machine) (args : List Value) (blk : Option Value)
    (kw : List (Value × Value) := []) : StepResult :=
  let f := m.frames.getD (methodFrameOf m) default
  if f.meth == "" then .unsupported "super outside a method"
  else
    let self := f.self
    match superFound m.heap (classOf m.heap self) f.defmod f.meth with
    | some (_, md) =>
      match md.builtin with
      | some bid =>
        -- builtins take keywords as a trailing positional Hash (Ruby-3 [V])
        let (args, m) := appendKwHash m args kw
        match Builtins.run bid self args m with
        | .ok v m => .next (withCtl m (.value v))
        | .err cls msg m => .next (raiseErr m cls msg)
        | .throwV v m => .next (withCtl m (.jump (.raiseJ v)))
        | .unsupported r => .unsupported r
      | none => enterUserMethod m self f.meth md args blk kw
    | none =>
      .next (raiseErr m Boot.noMethodErrorId
        s!"super: no superclass method '{f.meth}' for {receiverDesc m.heap self}")

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

/-- All args in → resolve the pending block and dispatch. A literal block is
    reified here (capturing the caller frame); `proc`/`lambda`/`Proc.new` with
    a block capture rather than call; a `&e` block-pass evaluates `e` last
    (eval order) then coerces. -/
def finishSend (m : Machine) (recv : Value) (implicit : SendSite) (mname : String)
    (args : List Value) (pblk : PendingBlk) (kw : List (Value × Value) := []) : StepResult :=
  match pblk with
  | .passExpr e => .next (withKont m (.eval e) (.blkCoerceK recv implicit mname args kw))
  | .lit ps ls body =>
    let mkLam := implicit == .implicit && mname == "lambda"
    let (v, m) := reifyBlock m ps ls body mkLam
    if implicit == .implicit && (mname == "lambda" || mname == "proc") then
      .next (withCtl m (.value v))
    else if mname == "new" && (match recv with | .ref k => k == Boot.procId | _ => false) then
      .next (withCtl m (.value v))
    else if mname == "new" && args.isEmpty
        && (match recv with | .ref k => k == Boot.hashId | _ => false) then
      -- `Hash.new { |h,k| … }`: the block becomes the hash's default_proc (L42),
      -- consulted on a `[]` miss in `invoke`. `v` is the reified block (a Proc).
      match v with
      | .ref bo =>
        let (o, h) := m.heap.alloc
          { klass := Boot.hashId, payload := .hsh #[], hashDflt := some (.prc bo) }
        .next (withCtl { m with heap := h } (.value (.ref o)))
      | _ => .unsupported "Hash.new block not a proc"
    else if mname == "new"
        && (match recv with | .ref k => k == Boot.classId || k == Boot.moduleId | _ => false) then
      -- `Class.new { … }` / `Module.new { … }`: allocate the anonymous class, then
      -- run the block with `self`/the `def` target rebound to it — i.e. exactly
      -- `class_eval` (L72). The block also receives the class as its argument [V].
      match recv with
      | .ref k =>
        match Builtins.run (if k == Boot.classId then "Class#new" else "Module#new") recv args m with
        | .ok newV m =>
          match newV, procClosure? m v with
          | .ref newK, some cl =>
            -- the block's value is discarded; `Class.new` yields the class [V]
            let m := { m with kont := .newK newV :: m.kont }
            callClosure m cl [newV] none (some newV) (some newK)
          | _, _ => .unsupported "Class.new did not yield a class"
        | .err cls msg m => .next (raiseErr m cls msg)
        | .throwV tv m => .next (withCtl m (.jump (.raiseJ tv)))
        | .unsupported r => .unsupported r
      | _ => .unsupported "Class#new with a block"
    else if mname == "new" then
      -- `X.new { … }` for any other class. If the receiver has a **user**
      -- `self.new` (a singleton or inherited-singleton method), that method is
      -- what runs and the block is an ordinary block argument — the interception
      -- above must not steal it. `Struct.new(:a) { … }` in the prelude is exactly
      -- this shape (L105). Otherwise the block would be an `initialize` block,
      -- which is unmodeled, so gate.
      match recv with
      | .ref k =>
        match methodOn m.heap (classOf m.heap recv) "new" with
        | some (_, md) => if md.builtin.isNone then invoke m recv implicit mname args (some v) kw
                          else .unsupported "Class#new with a block"
        | none => .unsupported "Class#new with a block"
      | _ => .unsupported "Class#new with a block"
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

/-- The class/module a `@@x` in the current frame belongs to (artifact 03 §3):
    the innermost *lexical* class/module (cref head), falling back to `defmod`.
    `none` when there is no such scope (toplevel — CRuby warns and uses Object,
    but the desugar's toplevel `@@x` cases are rare) or when it is an eigenclass,
    whose class-variable scope CRuby resolves differently (L67). -/
def cvarScope (m : Machine) : Option ObjId :=
  let k := match m.currentFrame.cref with
    | c :: _ => c
    | [] => m.currentFrame.defmod
  -- An eigenclass body shares the *attached* class's class variables in CRuby
  -- (`class << self; @@f = 1; end` writes the class's `@@f` [V]); our cref head
  -- is the eigenclass itself, and we do not track the attachment → gate.
  if (className m.heap k).startsWith "#<" then none else some k

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
  match lookup m.heap recv mname with
  | some (_, md) =>
    -- visibility counts: `defined?(obj.private_m)` is nil [V] (L71)
    if md.undefined then some false
    else some (visError? m recv site md mname).isNone
  | none =>
    if (crubyShadow m.heap (ancestors m.heap (classOf m.heap recv)) mname).isSome then none
    else some false

end Interp

end RubyCore
