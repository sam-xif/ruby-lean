import RubyCore.Interp.Support

/-!
Method lookup and entry: the ancestor walk, entering a user method or a
class/module body, eigenclasses, visibility, `method_missing`, the
iterating-builtin bridge, and mixin hooks.

Split out of `RubyCore/Interp.lean` (L99) with no behaviour change. The helpers
in this machine are deliberately *not* mutually recursive — each performs one
transition — so the file cuts along that existing order and the import chain
records it.
-/

namespace RubyCore

namespace Interp

/-- Continue the `lookup` walk *strictly above* `owner` in `recv`'s ancestor
    chain. Used by the block fallback (L63): a blockless builtin shadowing a
    prelude definition of the same name defers to it when a block is passed. -/
def lookupAbove (h : Heap) (recv : Value) (owner : ObjId) (mname : String)
    : Option (ObjId × MethodDef) :=
  ((ancestors h (classOf h recv)).dropWhile (· != owner)).drop 1 |>.firstM fun k =>
    match h.classPayload? k with
    | some c => (c.methods.find? (·.1 == mname)).map (fun (_, md) => (k, md))
    | none => none

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
    -- Pre-declare every formal that is bound *later* (`localsB` after defaults,
    -- and the omitted defaults themselves) as nil in this frame, so the
    -- `setLocal` calls below resolve here rather than walking a `capturedFrame`
    -- chain into the enclosing scope and clobbering a same-named outer local
    -- (only reachable for `define_method` bodies, L64; harmless otherwise —
    -- an unbound local reads as nil either way).
    -- ...and, for the same reason, every name the *body* binds itself: a
    -- `define_method` block's block-locals (L125/C35). Ordinary `def`s carry an
    -- empty list here.
    let predeclared := localsB.map (fun b => (b.1, Value.nil)) ++
      (optOmitted ++ kwOmitted).map (fun d => (d.1, Value.nil)) ++
      md.declared.map (fun n => (n, Value.nil))
    -- `blk`: an ordinary method sees its caller's block. A `define_method` body
    -- is a *block*, so `block_given?`/`yield` inside it refer to the block of the
    -- scope it was defined in, not the call [V] (test_method_204) — while an
    -- explicit `&b` param still binds the *call*'s block (bound in `localsB`).
    let frameBlk := match md.capturedFrame with
      | some cf => (m.frames.getD cf default).blk
      | none => blk
    let frame : Frame :=
      { self := recv, locals := localsA ++ predeclared, defmod := md.owner,
        kind := .method, blk := frameBlk, callBlk := blk,
        meth := md.superName.getD mname,
        runParams := md.params, runFromDM := md.capturedFrame.isSome,
        cref := md.cref, captured := md.capturedFrame }
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

/-- Assigning an **anonymous** class/module (from `Class.new`) to a constant gives
    it that constant's name [V]: `S = Class.new; S.name == "S"` (L72). Applied by
    every constant-assignment path. -/
def nameIfAnonymous (h : Heap) (name : String) (v : Value) : Heap :=
  match v with
  | .ref o =>
    match h.classPayload? o with
    | some c => if c.name.isEmpty then h.setClassPayload o { c with name } else h
    | none => h
  | _ => h

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
      -- CRuby names an eigenclass after the object it is attached to, by
      -- `rb_any_to_s` — so a *class*'s metaclass is `#<Class:Foo>` but a plain
      -- object's is `#<Class:#<Foo:0x…>>`, not `#<Class:Object>` [V]. `className`
      -- answers "Object" for a non-class id, which is why this went through
      -- `anyToS` in L124. The name is fixed here, at creation; CRuby computes it
      -- on demand, which is observable in the one shape §Known wrong answers
      -- records (an anonymous class named *after* an instance's eigenclass exists).
      let ename := s!"#<Class:{anyToS m.heap o}>"
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

/-- Visibility enforcement at dispatch (artifact 02 §5, L71): only an `explicit`
    receiver is checked — an implicit send, a literal `self.m`, and `send`/
    `__send__` are all exempt. Protected passes when the *caller's* `self` is a
    kind of the method's owner. Messages are byte-exact [V]. -/
def visError? (m : Machine) (recv : Value) (site : SendSite) (md : MethodDef)
    (mname : String) : Option StepResult :=
  match site, md.visibility with
  | .explicit, .priv =>
    some (.next (raiseErr m Boot.noMethodErrorId
      s!"private method '{mname}' called for {receiverDesc m.heap recv}"))
  | .explicit, .prot =>
    if isA m.heap m.currentFrame.self md.owner then none
    else some (.next (raiseErr m Boot.noMethodErrorId
      s!"protected method '{mname}' called for {receiverDesc m.heap recv}"))
  | _, _ => none

/-- Default `method_missing` (artifact 02 §4). A **vcall** (bare identifier, now
    carried as its own `SendSite` — L75) misses with `NameError: undefined local
    variable or method`; every other site misses with `NoMethodError: undefined
    method`. Both messages are byte-exact [V].

    This previously gated: RubyCore conflated `foo` and `foo()`, so an
    implicit zero-arg miss could not be attributed and answered
    `.unsupported "vcall/fcall NameError ambiguity"`. The front end now marks
    vcalls, so the ambiguity is gone. -/
def missNoMethod (m : Machine) (recv : Value) (implicit : SendSite) (mname : String)
    (_args : List Value) : StepResult :=
  if implicit == .vcall then
    .next (raiseErr m Boot.nameErrorId
      s!"undefined local variable or method '{mname}' for {receiverDesc m.heap recv}")
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
      -- max_by/min_by: `acc` is `[bestElem, bestKey]` (or `[]` if the receiver was
      -- empty, in which case both return `nil`); the result is the winning element.
      | .maxBy | .minBy => (acc.headD .nil, m)
    .next (withCtl m (.value finalV))   -- `frameK brk` pops the iterator frame
  | a :: rest' =>
    let callArgs := match kind with | .fold => acc ++ a | _ => a
    -- `cur` = the element being yielded (for max_by/min_by, the value the winner
    -- is chosen from); the block's single arg, so `a.head`.
    let m := { m with kont := .iterK cl brk rest' kind acc retVal (a.headD .nil) :: m.kont }
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
          | "each_index" =>
            let idxs := (List.range xs.size).map (fun i => [Value.int (Int.ofNat i)])
            some (startIter m recv mname cl idxs .ignore [] recv)
          | "inject" | "reduce" =>
            -- block form only; `inject(:sym)` has no block ⇒ not reached here.
            match args with
            | [] => match xs.toList with
              | [] => some (.next (withCtl m (.value .nil)))   -- empty, no seed → nil
              | h :: t => some (startIter m recv mname cl (t.map (fun e => [e])) .fold [h] .nil)
            | [seed] => some (startIter m recv mname cl each1 .fold [seed] .nil)
            | _ => none
          | "max_by" | "min_by" =>
            -- yields each element; returns the element with the extreme block value.
            let kind := if mname == "max_by" then IterKind.maxBy else IterKind.minBy
            some (startIter m recv mname cl each1 kind [] .nil)
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
          | "max_by" | "min_by" =>
            -- yields each `[k, v]` pair; returns the pair with the extreme block
            -- value (e.g. `h.max_by { |_, v| v }.first`).
            let (elemArgs, m) := pairs.toList.foldl (fun (acc, m) (kv : Value × Value) =>
              let (pa, m) := Builtins.allocArr m #[kv.1, kv.2]; (acc ++ [[pa]], m)) ([], m)
            let kind := if mname == "max_by" then IterKind.maxBy else IterKind.minBy
            some (startIter m recv mname cl elemArgs kind [] .nil)
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
  -- Kernel, Enumerable and Comparable are now *really* in the ancestor chain
  -- (L62/L65: Kernel is included into Object, the prelude includes Enumerable
  -- into Array/Hash/Range and Comparable into Numeric/String/Symbol), so
  -- ordinary `lookup` resolves them and consulting them here would *re-add*
  -- methods an `undef_method` had removed (test_yjit_266). What remains is the
  -- classes whose real CRuby mixins the model still does not splice in.
  if cls == Boot.symbolId then ["Comparable"] else []

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
  | "prepend", .ref o, [.ref mo] =>
    -- `prepend M` (L65): like `include`, but M lands *below* the receiver in the
    -- ancestor chain, so M's methods override the class's own and `super` inside
    -- them reaches the overridden definition.
    match m.heap.classPayload? o, m.heap.classPayload? mo with
    | some c, some _ =>
      match moduleHook m mo "prepended" with
      | some _ => some (.unsupported "prepend with a `prepended` hook")
      | none =>
        let c' := { c with prepends := c.prepends ++ [mo] }
        let m := { m with heap := m.heap.setClassPayload o c' }
        some (.next (withCtl m (.value recv)))
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
      let vis := m.currentFrame.defVis
      let getter : MethodDef :=
        { params := [], body := .var .ivar iv, owner := cls,
          fromPrelude := m.preludeMode, visibility := vis }
      let setter : MethodDef :=
        { params := [.req "__v"], body := .vasgn .ivar iv (.var .lvar "__v"), owner := cls,
          fromPrelude := m.preludeMode, visibility := vis }
      let m := if mname != "attr_writer" then { m with heap := defineMethod m.heap cls s getter } else m
      let m := if mname != "attr_reader" then { m with heap := defineMethod m.heap cls (s ++ "=") setter } else m
      let names := names
        ++ (if mname != "attr_writer" then [Value.sym s] else [])
        ++ (if mname != "attr_reader" then [Value.sym (s ++ "=")] else [])
      (m, names)
    | _ => (m, names)) (m, [])

end Interp

end RubyCore
