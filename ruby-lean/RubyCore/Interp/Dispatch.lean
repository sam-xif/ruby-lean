import RubyCore.Interp.Enumerator

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
  lookupInChain h (((ancestors h (classOf h recv)).dropWhile (· != owner)).drop 1) mname

/-- First module in `ancestors k` defining `m` directly, with its owner — like
    `lookup` but keyed on a class ObjId rather than a receiver value (used to
    inspect a class before any instance of it exists, e.g. for `initialize`). -/
def methodOn (h : Heap) (k : ObjId) (mname : String) : Option (ObjId × MethodDef) :=
  lookupInChain h (ancestors h k) mname

/-- Enter a RubyCore-defined method activation: bind params (required + rest +
    post; block-capture `&blk`), push the method frame, evaluate the body under
    a `frameK` boundary (artifact 02 §3). Factored out of dispatch so `Class#new`
    can reuse it for `initialize`. Arity failures raise `ArgumentError` [V]. -/
def enterUserMethod (m : Machine) (recv : Value) (mname : String) (md : MethodDef)
    (args : List Value) (blk : Option Value) (kw : List (Value × Value) := []) : StepResult :=
  let fp? := classifyFull md.params
  if fp?.isNone then
    .unsupported "non-canonical method parameter shape"
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
    -- Capture raw destructuring slots now, but expand only after all defaults.
    -- Names inside them are nil during defaults, including define_method captures.
    let pending := fp.destrs.map fun (sn, subs) =>
      (Param.destr subs, (((localsA ++ localsB).find? (·.1 == sn)).map (·.2)).getD .nil)
    let destrNames := fp.destrs.flatMap fun (_, subs) => destructureNames subs (destrDepth subs + 1)
    let notSynth : (String × Value) → Bool := fun b => !(fp.destrs.any (·.1 == b.1))
    let localsA := localsA.filter notSynth
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
    let predeclared := destrNames.map (fun n => (n, Value.nil)) ++ localsB.map (fun b => (b.1, Value.nil)) ++
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
      { self := recv, locals := localsA ++ predeclared,
        localAlias := if md.forTargets.isSome then md.capturedFrame else none,
        defmod := md.definee.getD md.owner, methodOwner := some md.owner,
        definitionFrame := md.definitionFrame,
        kind := .method, blk := frameBlk, callBlk := blk,
        meth := md.superName.getD mname, superScope := md.superScope,
        runParams := md.params, runFromDM := md.fromBlock,
        cref := md.cref, captured := md.capturedFrame, libraryOrigin := md.fromPrelude }
    let fid := m.frames.size
    let m := { m with frames := m.frames.push frame, stack := fid :: m.stack }
    let boundary := if md.fromBlock then Kont.dmFrameK fid md.body else .frameK fid
    let m := { m with kont := boundary :: m.kont }
    let m := if pending.isEmpty then m else { m with kont := .paramBindK pending md.body :: m.kont }
    -- Defaults complete by delivering a value to the pending binding phase.
    let body := if pending.isEmpty then md.body else Expr.nil
    if let some targets := md.forTargets then
      startForBindings m targets md.forMultiple args md.body else
    -- positional-opt defaults first, then keyword defaults (Ruby order [V]).
    match optOmitted ++ kwOmitted with
    | [] =>
      let m := localsB.foldl (fun m (nv : String × Value) => m.setLocal nv.1 nv.2) m
      .next (withCtl m (.eval body))
    | (n0, d0) :: more =>
      .next (withKont m (.eval d0) (.optDefK n0 more localsB body))

/-- Permanently name a namespace and its still-temporary descendants (L295).
    Ancestor back-edges stop after the ancestor has acquired its name. Multiple
    paths to a descendant depend on CRuby's process-local symbol-table order;
    the model does not yet carry that order and must not select an arbitrary path.
    Names are internal metadata: frozen descendants are renamed without hooks. -/
def setNamespacePath (h : Heap) (root : ObjId) (name : String) : Except String Heap := do
  let (h, _) ← go (h.objs.size + 1) h root name [] []
  return h
where
  go : Nat → Heap → ObjId → String → List ObjId → List ObjId → Except String (Heap × List ObjId)
    | 0, _, _, _, _, _ => .error "namespace naming exhausted heap-depth bound"
    | fuel + 1, h, o, name, ancestors, seen => do
      if ancestors.contains o then return (h, seen)
      if seen.contains o then
        throw "permanent namespace naming with multiple paths needs CRuby symbol-table order"
      match h.classPayload? o with
      | none => return (h, seen)
      | some c =>
        if !c.name.isEmpty && c.namePermanent then return (h, seen)
        let h := h.setClassPayload o { c with name, namePermanent := true }
        c.consts.foldlM (init := (h, o :: seen)) fun (h, seen) (n, v) => do
          if !validConstantName n then return (h, seen)
          match v with
          | .ref child => go fuel h child (name ++ "::" ++ n) (o :: ancestors) seen
          | _ => return (h, seen)

/-- Constant binding gives a namespace either its first temporary path or a
    permanent path, recursively realizing descendants in the latter case.
    Use the parent's native class path, including the address of an anonymous
    eigenclass, independently of its attached-object display and Ruby overrides. -/
def nameConstant (h : Heap) (target : ObjId) (name : String) (v : Value) : Except String Heap :=
  match v with
  | .ref o =>
    match h.classPayload? o with
    | some c =>
      if !c.name.isEmpty && c.namePermanent then .ok h else
      if target == Boot.objectId then setNamespacePath h o name else
      let qual := classPath h target ++ "::" ++ name
      let permanent := (h.classPayload? target).any fun p => !p.name.isEmpty && p.namePermanent
      if permanent then setNamespacePath h o qual else
      if c.name.isEmpty then .ok (h.setClassPayload o { c with name := qual, namePermanent := false })
      else .ok h
    | none => .ok h
  | _ => .ok h

/-- A constant is already bound when its ordinary callback executes (L292).
    Only core boot suppresses the callback; runtime library loads do not. -/
def callConstAdded (m : Machine) (target : ObjId) (name : String) : StepResult :=
  if m.preludeMode then .next { m with ctl := .value .nil } else
  .next { m with ctl := .send (.ref target) .reflective "const_added" [.sym name] none [] }

def assignConstant (m : Machine) (target : ObjId) (name : String) (value : Value) : StepResult :=
  if (m.heap.get target).frozen then raiseFrozen m (.ref target) else
  let h := constSetIn m.heap target name value
  match nameConstant h target name value with
  | .error why => .unsupported why
  | .ok h => callConstAdded { m with heap := h, kont := .newK value :: m.kont } target name

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
          -- top of the metaclass chain: a module's own metaclass superclasses
          -- `Module` (CRuby: `M.singleton_class.superclass == Module`), a
          -- class's superclasses `Class`.
          | none => ((if c.isModule then obj.klass else Boot.classId), m)
        | _ => (obj.klass, m)
      -- Keep the attachment, not a snapshot of its name: an anonymous class
      -- can acquire a constant name after this singleton class was created.
      let (e, h) := m.heap.alloc
        { klass := Boot.classId, frozen := obj.frozen,
          payload := .cls { superclass := some supr, name := "", attached := some o } }
      let h := h.set o { h.get o with eigen := some e }
      (e, { m with heap := h })

/-- Optional libraries generally have smaller source bodies; callbacks can
    observe omitted declarations. Forwardable matches the upstream method order
    (L282), while its other hook protocols remain outside this fragment. -/
def libraryBodyGate (m : Machine) (k : ObjId) : Option String :=
  if !m.currentFrame.libraryOrigin || m.preludeMode || m.loadingFeatures.isEmpty then none else
  let exactMethods := m.loadingFeatures.head? == some "forwardable"
  if (m.heap.get k).frozen && !exactMethods then some "require into a frozen namespace needs the complete library body" else
  let hooks := if exactMethods then ["const_added", "inherited", "included", "extended", "prepended"] else
    ["method_added", "singleton_method_added", "const_added", "inherited", "included", "extended", "prepended"]
  let targets := k :: ((m.heap.classPayload? k).bind (·.superclass)).toList
  if targets.any (fun target =>
      hooks.any
        (fun hook => (lookup m.heap (.ref target) hook).any
          (fun (_, md) => md.builtin.isNone && !md.undefined && !md.fromPrelude))) then
    some "require with user definition hooks needs the complete library body"
  else none

def classNameTypeError (m : Machine) (klass : ObjId) (lead tail : String) : StepResult :=
  .next { m with ctl := .send (.ref klass) .reflective "to_s" [] none [], kont := .classNameErrorK klass lead tail :: m.kont }

/-- Inheritance validates native class identity, not overridable predicates.
    Class.new rejects an uninitialized parent; a named class statement permits
    it and retains the parent's unavailable allocator/index (CRuby 4.0.5). -/
def inheritableClass (m : Machine) (value : Value) (requireInitialized : Bool) :
    Except StepResult ObjId := do
  let bad := .error (classNameTypeError m (realClassOf m.heap value)
    "superclass must be an instance of Class (given an instance of " ")")
  match value with
  | .ref k => match m.heap.classPayload? k with
    | some cp =>
      if cp.isModule then bad
      else if cp.attached.isSome then
        .error (.next (raiseErr m Boot.typeErrorId "can't make subclass of singleton class"))
      else if k == Boot.classId then
        .error (.next (raiseErr m Boot.typeErrorId "can't make subclass of Class"))
      else if requireInitialized && !cp.initialized then
        .error (.next (raiseErr m Boot.typeErrorId "can't inherit uninitialized class"))
      else .ok k
    | none => bad
  | _ => bad

def pushClassFrame (m : Machine) (k : ObjId) (libraryName : String)
    (body : Expr) : StepResult :=
  match libraryBodyGate m k with
  | some reason => .unsupported reason
  | none =>
  let m := if m.preludeMode || m.currentFrame.libraryOrigin then
    match m.heap.classPayload? k with
    | some cp => { m with heap := m.heap.setClassPayload k { cp with libraryNamespace := some libraryName } }
    | none => m
    else m
  let frame : Frame :=
    { self := .ref k, defmod := k, kind := .classBody, cref := k :: m.currentFrame.cref, libraryOrigin := m.currentFrame.libraryOrigin }
  let fid := m.frames.size
  let m := { m with frames := m.frames.push frame, stack := fid :: m.stack }
  .next (withKont m (.eval body) (.frameK fid))

def inheritClassBody (m : Machine) (k : ObjId) (superclass : Option ObjId)
    (libraryName : String) (body : Expr) : StepResult :=
  match superclass with
  | none => pushClassFrame m k libraryName body
  | some parent =>
    .next { m with ctl := .send (.ref parent) .reflective "inherited" [.ref k] none [], kont := .classBodyK k libraryName body :: m.kont }

/-- Open (or create) a class/module named `name` and run its `body` in a fresh
    class-body frame with `self` = `defmod` = the class object (artifact 01 §5).
    Reopening checks class/module agreement and, for `class`, superclass match
    [V]. `sup?` is the resolved superclass (classes default to Object). -/
def enterClassBody (m : Machine) (name : String) (isMod : Bool)
    (sup? : Option ObjId) (body : Expr) : StepResult :=
  let kindWord := if isMod then "module" else "class"
  let libraryName := if m.lexicalNamespace == Boot.objectId then name else
    s!"{(libraryNamespace m.heap m.lexicalNamespace).getD (className m.heap m.lexicalNamespace)}::{name}"
  let pushFrame (m : Machine) (k : ObjId) := pushClassFrame m k libraryName body
  -- Reopen detection looks up `name` in the *current innermost namespace only*
  -- (`defmod`), NOT a flat toplevel lookup and NOT the full lexical cref chain.
  -- So `module B` inside a reopened `module A` finds the existing `A::B` (A's own
  -- constant) and reuses that object instead of allocating a duplicate and
  -- clobbering `A::B`. Crucially it is *not* the cref-walk used for constant
  -- *reads*: `class Foo` nested in `M` must create `M::Foo`, it does NOT reopen a
  -- lexically-visible `::Foo` (verified against CRuby). At the toplevel `defmod`
  -- is `Object`, so this coincides with the old flat lookup.
  match constOwn m.heap m.lexicalNamespace name with
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
    if (m.heap.get m.lexicalNamespace).frozen then raiseFrozen m (.ref m.lexicalNamespace) else
    let superclass := if isMod then none else some (sup?.getD Boot.objectId)
    -- A nested definition (`module B` inside `A`) takes the qualified constant
    -- path `A::B` as its `name` (CRuby derives the name from where the constant
    -- is bound); a toplevel definition (`defmod` = Object) keeps the bare name.
    let defmod := m.lexicalNamespace
    let obj : Object :=
      { klass := (if isMod then Boot.moduleId else Boot.classId), payload := .cls { superclass, name := "", isModule := isMod, ancestryReady := superclass.all (fun s => (m.heap.classPayload? s).all (·.ancestryReady)), allocatorUnavailable := superclass.any (fun s => (m.heap.classPayload? s).any (·.allocatorUnavailable)) } }
    let (k, h) := m.heap.alloc obj
    -- register the class name in the *enclosing* namespace (Object at toplevel)
    let h := constSetIn h m.lexicalNamespace name (.ref k)
    match nameConstant h defmod name (.ref k) with
    | .error why => .unsupported why
    | .ok h =>
      -- Eagerly realize the metaclass chain so inherited class methods resolve
      -- (`B < A` ⇒ `B`'s metaclass superclasses `A`'s) before any `def self.`.
      let (_, m) := eigenclassOf { m with heap := h } k
      callConstAdded { m with kont := .constClassK k superclass libraryName body :: m.kont } defmod name

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
  let libraryName := s!"{(libraryNamespace m.heap container).getD (className m.heap container)}::{name}"
  let pushFrame (m : Machine) (k : ObjId) := pushClassFrame m k libraryName body
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
    if (m.heap.get container).frozen then raiseFrozen m (.ref container) else
    let superclass := if isMod then none else some Boot.objectId
    let obj : Object :=
      { klass := (if isMod then Boot.moduleId else Boot.classId),
        payload := .cls { superclass, name := "", isModule := isMod } }
    let (k, h) := m.heap.alloc obj
    let h := constSetIn h container name (.ref k)
    match nameConstant h container name (.ref k) with
    | .error why => .unsupported why
    | .ok h =>
      let (_, m) := eigenclassOf { m with heap := h } k
      callConstAdded { m with kont := .constClassK k superclass libraryName body :: m.kont } container name

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
  match kind with
  | .scan o revision subject pattern options index last binary =>
    if (m.heap.get o).revision != revision then
      .unsupported "String#scan receiver mutation during a suspended block" else
    match (if index > subject.length then Builtins.Found.miss else
        Builtins.runSearch pattern options subject index) with
    | .gate reason => .unsupported reason
    | .miss => .next (withCtl (Builtins.setMatchGlobals m last) (.value retVal))
    | .hit a b caps names =>
      let (md, m) := Builtins.allocMData m subject caps names binary
      let m := Builtins.setMatchGlobals m (some md)
      let spans := if caps.size <= 1 then caps.toList.take 1 else caps.toList.drop 1
      let (parts, m) := spans.foldl (fun (acc, m) span => match span with
        | none => (acc ++ [Value.nil], m)
        | some (x, y) => let (v, m) := Builtins.allocStrEnc m (Builtins.charSlice subject x y) binary
                        (acc ++ [v], m)) ([], m)
      let (item, m) := if caps.size <= 1 then (parts.headD .nil, m)
        else Builtins.allocArr m parts.toArray
      let kind := IterKind.scan o revision subject pattern options (if a == b then b + 1 else b) (some md) binary
      callClosure { m with kont := .iterK cl brk [] kind [] retVal item :: m.kont } cl [item] (some brk)
  | .times limit index =>
    if index < limit then
      let v := Value.int index
      let m := { m with kont := .iterK cl brk [] (.times limit (index + 1)) [] retVal v :: m.kont }
      callClosure m cl [v] (some brk)
    else .next (withCtl m (.value retVal))
  | .arrayEach o index =>
    -- Array#each rereads both length and element after every yield (L273).
    -- Snapshotting skipped appends and yielded removed/replaced elements.
    match (m.heap.get o).payload with
    | .arr xs =>
      if hi : index < xs.size then
        let v := xs[index]
        let m := { m with kont := .iterK cl brk [] (.arrayEach o (index + 1)) [] retVal v :: m.kont }
        callClosure m cl [v] (some brk)
      else .next (withCtl m (.value retVal))
    | _ => .unsupported "Array#each receiver lost its Array payload"
  | .arrayMap o index =>
    -- Array#map/collect use a live native cursor, independent of `each` (L274).
    match (m.heap.get o).payload with
    | .arr xs =>
      if hi : index < xs.size then
        let v := xs[index]
        let m := { m with kont := .iterK cl brk [] (.arrayMap o (index + 1)) acc retVal v :: m.kont }
        callClosure m cl [v] (some brk)
      else
        let (a, m) := Builtins.allocArr m acc.toArray
        .next (withCtl m (.value a))
    | _ => .unsupported "Array#map receiver lost its Array payload"
  | .arrayIndex o index =>
    match (m.heap.get o).payload with
    | .arr xs =>
      if index < xs.size then
        let v := Value.int index
        callClosure { m with kont := .iterK cl brk [] (.arrayIndex o (index + 1)) [] retVal v :: m.kont } cl [v] (some brk)
      else .next (withCtl m (.value retVal))
    | _ => .unsupported "Array#each_index receiver lost its Array payload"
  | .hashEach o keys index mode =>
    match (m.heap.get o).payload with
    | .hsh xs =>
      -- Deleted keys disappear; replacements of an existing value are visible.
      -- A shared lock forbids insertion while the callback is live/suspended.
      match (keys.drop index).zipIdx.find? (fun (key, _) => xs.any (fun (k, _) => k.identEq key)) with
      | none => .next (withCtl m (.value retVal))
      | some (key, offset) =>
        let value := ((xs.find? (fun (k, _) => k.identEq key)).map Prod.snd).getD .nil
        let (v, m) := if mode == 1 then (key, m) else if mode == 2 then (value, m)
          else Builtins.allocArr m #[key, value]
        callClosure { m with hashIterationLocks := o :: m.hashIterationLocks, kont := .iterK cl brk [] (.hashEach o keys (index + offset + 1) mode) [] retVal v :: m.kont } cl [v] (some brk)
    | _ => .unsupported "Hash iterator receiver lost its Hash payload"
  | _ =>
  match rest with
  | [] =>
    let (finalV, m) := match kind with
      | .ignore | .arrayEach .. | .arrayMap .. | .arrayIndex .. | .hashEach .. | .times .. | .scan .. => (retVal, m)
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
  -- **`cref` is the caller's** (L256), and it is a *fidelity* fix with a proof
  -- consumer. This activation is the `break` target and **no code evaluates in it** —
  -- the loop is driven by the `iterK` continuation and every expression runs in a block
  -- frame above — so the field was left at `[]` and nothing read it: every `cref` read in
  -- the interpreter is `m.currentFrame.cref` (during eval *in* that frame), `md.cref`, or
  -- `capF.cref` (the frame a closure captured, which is the caller, not this one).
  --
  -- What made it worth fixing is the static invariant: `StackCtx`'s fifth clause is
  -- *`Object` is on the frame's lexical constant scope* (L189), it is positional, and an
  -- empty `cref` refuses it — see `implementation-notes.md` L255 for the alternative that
  -- was priced and rejected (a second `FrameCtx` channel, whose consumers would have
  -- needed the fact threaded through 18 `KontOk` constructors). CRuby's iterator
  -- activation inherits the caller's cref, so this is also the more faithful frame.
  let frame : Frame :=
    { self := recv, defmod := classOf m.heap recv, kind := .method, meth := mname,
      cref := m.currentFrame.cref, matchXparent := mname == "scan" }
  let fid := m.frames.size
  let m := { m with frames := m.frames.push frame, stack := fid :: m.stack }
  let m := { m with kont := .frameK fid :: m.kont }
  iterStep m cl fid elemArgs kind initAcc retVal

def arrayMapBid (bid : String) : Bool :=
  bid == "Array#map" || bid == "Array#collect"

/-- Resolve Array's own map/collect through ordinary lookup (L274). Unlike
Enumerable#map, these methods never dispatch `each`, `length` or `[]`. Aliases
and super retain native behavior; arity is checked even without a block. -/
def callArrayMapBuiltin (m : Machine) (recv : Value) (mname : String)
    (args : List Value) (blk : Option Value) (kw : List (Value × Value)) : StepResult :=
  let n := args.length + if kw.isEmpty then 0 else 1
  if n != 0 then
    .next (raiseErr m Boot.argumentErrorId s!"wrong number of arguments (given {n}, expected 0)")
  else
    match recv, blk with
    | .ref o, some (.ref bo) =>
      match (m.heap.get o).payload, (m.heap.get bo).payload with
      | .arr _, .proc cl => startIter m recv mname cl [] (.arrayMap o 0) [] .nil
      | _, _ => .unsupported "Array#map builtin without Array/Proc payloads"
    | _, none => enumMake m recv mname [] .receiverLength
    | _, _ => .unsupported "Array#map invalid block"

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
          | "each" => some (startIter m recv mname cl [] (.arrayEach o 0) [] recv)
          | "each_with_index" =>
            let ei := xs.toList.zipIdx.map (fun (e, i) => [e, Value.int (Int.ofNat i)])
            some (startIter m recv mname cl ei .ignore [] recv)
          | "each_index" =>
            some (startIter m recv mname cl [] (.arrayIndex o 0) [] recv)
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
          | "each" | "each_pair" | "each_key" | "each_value" =>
            let mode := if mname == "each_key" then 1 else if mname == "each_value" then 2 else 0
            some (startIter m recv mname cl [] (.hashEach o (pairs.toList.map Prod.fst) 0 mode) [] recv)
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
          some (startIter m recv mname cl [] (.times n.toNat 0) [] recv)
        | _ => none
      | _ => none
    | _ => none
  | _ => none

def nativeIteratorBid (bid : String) : Bool :=
  ["String#scan", "Integer#times", "Array#each", "Array#each_index", "Hash#each", "Hash#each_pair",
    "Hash#each_key", "Hash#each_value"].contains bid

def callNativeIterator (m : Machine) (bid : String) (recv : Value) (args : List Value)
    (blk : Option Value) (kw : List (Value × Value)) : StepResult :=
  let n := args.length + if kw.isEmpty then 0 else 1
  if bid == "String#scan" then
    if n != 1 then enumArity m n "1" else
    match recv, blk with
    | .ref o, some (.ref p) =>
      match (m.heap.get o).payload, (m.heap.get p).payload with
      | .str subject, .proc cl =>
        if Builtins.unrepresentableByteStr m.heap recv then
          .unsupported "String#scan on a high-byte binary String" else
        let pattern := args.headD .nil
        let re := Builtins.regexpParts? m.heap pattern <|>
          ((Builtins.strPayload? m.heap pattern).map fun s => (Builtins.escapeSource s, 0))
        match re with
        | none => .unsupported "String#scan pattern conversion"
        | some (source, flags) => startIter m recv "scan" cl []
            (.scan o (m.heap.get o).revision subject source flags 0 none (m.heap.get o).binary) [] recv
      | _, _ => .unsupported "String#scan payload"
    | _, _ => match Builtins.run bid recv args m with
      | .ok v m => .next (withCtl m (.value v))
      | .err k msg m => .next (raiseErr m k msg)
      | .throwV v m => .next (withCtl m (.jump (.raiseJ v)))
      | .frozen v m => raiseFrozen m v
      | .unsupported r => .unsupported r
  else
  if n != 0 then enumArity m n "0" else
  let name := (bid.splitOn "#").getLast!
  if blk.isNone then
    let size := match recv with
      | .int n => EnumSize.fixed (.int (max n 0))
      | _ => .receiverLength
    enumMake m recv name [] size
  else (tryIterator m recv name [] blk).getD (.unsupported "native iterator payload")

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
  let eligible := if mname == "extend" then isA m.heap recv Boot.objectId else
    if mname == "include" || mname == "prepend" then
      match recv with | .ref o => (m.heap.classPayload? o).isSome | _ => false
    else false
  if !eligible then none else
  if args.isEmpty then some (.next (raiseErr m Boot.argumentErrorId
    "wrong number of arguments (given 0, expected 1+)")) else
  if args.length == 1 && !(match args.headD .nil with
      | .ref o => (m.heap.classPayload? o).any (·.isModule)
      | _ => false) then
    some (.next (raiseErr m Boot.typeErrorId
      s!"wrong argument type {Builtins.coerceName m.heap (args.headD .nil)} (expected Module)")) else
  match mname, recv, args with
  | "include", .ref o, [.ref mo] =>
    match m.heap.classPayload? o, m.heap.classPayload? mo with
    | some c, some _ =>
      if let some receiver := frozenMethodReceiver? m.heap o then some (raiseFrozen m receiver) else
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
      if let some receiver := frozenMethodReceiver? m.heap o then some (raiseFrozen m receiver) else
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
      if (m.heap.get o).frozen then some (raiseFrozen m recv) else
      -- `extend` = include the module into the receiver's eigenclass; the
      -- `extended` hook is unmodeled → gate if present.
      match moduleHook m mo "extended" with
      | some _ => some (.unsupported "extend with an `extended` hook")
      | none =>
        let (e, m) := eigenclassOf m o
        match m.heap.classPayload? e with
        | some ec =>
          if let some receiver := frozenMethodReceiver? m.heap e then some (raiseFrozen m receiver) else
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
          fromPrelude := m.preludeMode || m.currentFrame.libraryOrigin, visibility := vis }
      let setter : MethodDef :=
        { params := [.req "__v"], body := .vasgn .ivar iv (.var .lvar "__v"), owner := cls,
          fromPrelude := m.preludeMode || m.currentFrame.libraryOrigin, visibility := vis }
      let m := if mname != "attr_writer" then { m with heap := defineMethod m.heap cls s getter } else m
      let m := if mname != "attr_reader" then { m with heap := defineMethod m.heap cls (s ++ "=") setter } else m
      let names := names
        ++ (if mname != "attr_writer" then [Value.sym s] else [])
        ++ (if mname != "attr_reader" then [Value.sym (s ++ "=")] else [])
      (m, names)
    | _ => (m, names)) (m, [])

end Interp

end RubyCore
