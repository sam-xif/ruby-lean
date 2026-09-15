import RubyCore.Interp.Dispatch

/-!
The reflective metaprogramming core (`define_method`, `*_eval`, `prepend`,
`alias_method`, `singleton_class`, ivar/const reflection, `Class.new`) plus
the lookup-miss classifier.

Split out of `RubyCore/Interp.lean` (L99) with no behaviour change. The helpers
in this machine are deliberately *not* mutually recursive — each performs one
transition — so the file cuts along that existing order and the import chain
records it.
-/

namespace RubyCore

namespace Interp

/-- Does this expression define a method directly (a `def`/`def self.`)? Used to
    decide whether an `instance_eval` on an *immediate* receiver is admissible:
    only a body that defines a singleton method needs the eigenclass it cannot
    have (L72). Conservative: a `def` anywhere inside counts. -/
partial def definesMethod : Expr → Bool
  | .def' .. | .defs .. => true
  | .seq es => es.any definesMethod
  | .if' c t e => definesMethod c || definesMethod t || (e.map definesMethod).getD false
  | .while' c b | .dowhile b c => definesMethod c || definesMethod b
  | .begin' b rs els ens =>
    definesMethod b || rs.any (fun r => definesMethod r.2.2)
      || (els.map definesMethod).getD false || (ens.map definesMethod).getD false
  | .send _ _ args blk => args.any definesMethod || (blk.map definesMethod).getD false
  | .block _ _ b => definesMethod b
  | _ => false


/-- **Is this body closed over locals?** (L272/J33) — a conservative whitelist:
    `true` only when no evaluation step of the body (or of any nested param-less,
    local-less block inside it) can read *or* write a local variable, so the
    activation's `captured` chain is never consulted and erasing it is
    unobservable. Anything suspicious — an lvar read/write anywhere (even one a
    nested binder would shadow), `defined?`, `super`/`zsuper`/`...`-forwarding,
    definition heads, blocks with params or block-locals — answers `false`, which
    merely *keeps* the capture (no behaviour change). Fueled per the L73
    kernel-reduction discipline; `sizeOf` bounds the recursion. -/
def localFreeB : Nat → Expr → Bool
  | 0, _ => false
  | n + 1, e =>
    match e with
    | .int _ | .flt _ | .str _ | .sym _ | .tru | .fls | .nil | .self' => true
    | .var .lvar _ => false
    | .var _ _ => true
    | .vasgn .lvar _ _ => false
    | .vasgn _ _ rhs => localFreeB n rhs
    | .const _ => true
    | .casgn _ rhs => localFreeB n rhs
    | .seq es => es.all (localFreeB n)
    | .if' c t e =>
      localFreeB n c && localFreeB n t &&
      (match e with | some e' => localFreeB n e' | none => true)
    | .while' c b => localFreeB n c && localFreeB n b
    | .dowhile b c => localFreeB n c && localFreeB n b
    | .send r mname args blk =>
      -- frame-sensitive callees: `block_given?` &c consult the activation's
      -- linkage, which the erasure changes (caught by the tier-0 ratchet on
      -- `test_method_204`) — refuse them, and anything else that reads the
      -- frame rather than the receiver.
      !(["block_given?", "binding", "local_variables", "iterator?"].contains mname) &&
      (match r with | some r' => localFreeB n r' | none => true) &&
      args.all (localFreeB n) &&
      (match blk with | some b => localFreeB n b | none => true)
    | .vcall mname =>
      !(["block_given?", "binding", "local_variables", "iterator?"].contains mname)
    | .block ps ls b => ps.isEmpty && ls.isEmpty && localFreeB n b
    | .blockpass (some b) => localFreeB n b
    | .blockpass none => false
    | .array es => es.all (localFreeB n)
    | .hash prs => prs.all (fun p => localFreeB n p.1 && localFreeB n p.2)
    | .ret e => (match e with | some e' => localFreeB n e' | none => true)
    | .brk e => (match e with | some e' => localFreeB n e' | none => true)
    | .nxt e => (match e with | some e' => localFreeB n e' | none => true)
    | _ => false

/-- The closure a Proc value carries, if any. -/
def procClosure? (m : Machine) (v : Value) : Option Closure :=
  match v with
  | .ref o => match (m.heap.get o).payload with | .proc cl => some cl | _ => none
  | _ => none

/-- The `public`/`private`/`protected`/`module_function` walk over the requested names:
    `none` if one of them is an unmodeled builtin (which is a gate, not a raise). -/
def visNames (m : Machine) (o target : ObjId) (vis : Visibility) (modFun : Bool)
    (names : List String) : Option Machine :=
  names.foldl (fun (acc : Option Machine) (n : String) =>
    acc.bind fun m =>
      match methodOn m.heap target n with
      | some (_, md) =>
        if md.builtin.isSome && !md.fromPrelude then none   -- unmodeled builtin → gate
        else
          let m := { m with heap := defineMethod m.heap target n { md with visibility := vis } }
          -- `module_function :m` also defines `m` as a singleton method [V]
          if modFun then
            -- the singleton copy is *owned by the eigenclass*, so `super`
            -- inside it continues from there (Module → Object) [V]
            let (e, m) := eigenclassOf m o
            let copy := { md with visibility := .pub, owner := e }
            some { m with heap := defineMethod m.heap e n copy }
          else some m
      | none => none) (some m)

/-- The walk's decision, machine-free — see `removeOk` for why that matters. -/
def visOk (m : Machine) (o target : ObjId) (vis : Visibility) (modFun : Bool)
    (names : List String) : Bool := (visNames m o target vis modFun names).isSome

/-- The machine the walk produces. -/
def visRun (m : Machine) (o target : ObjId) (vis : Visibility) (modFun : Bool)
    (names : List String) : Machine := (visNames m o target vis modFun names).getD m

/-- The `remove_method`/`undef_method` walk over the requested names: `none` if any name is
    not this class's own definition (an `undef` tombstone does not count). -/
def removeNames (m : Machine) (o : ObjId) (undef : Bool) (names : List String) :
    Option Machine :=
  names.foldl (fun (acc : Option Machine) (n : String) =>
    acc.bind fun m =>
      match m.heap.classPayload? o with
      | some c =>
        if undef then
          some { m with heap := undefMethod m.heap o n }
        else match c.methods.find? (·.1 == n) with
          | some (_, md) =>
            -- an `undef` tombstone is *not* a definition here [V]
            if md.undefined then none
            else
              let c' := { c with methods := c.methods.filter (·.1 != n) }
              some { m with heap := m.heap.setClassPayload o c' }
          | none => none
      | none => none) (some m)

/-- Did the walk succeed? **A `Bool`, and that is the point**: the caller used to `match` on
    the `Option Machine` directly, and a scrutinee that carries a machine is what makes the
    continuation-framing proof fail — under a push the two sides' scrutinees differ by an
    `Option.map`, so `split` pairs a `none` arm of one with a `some` arm of the other. A
    machine-free decision plus a separate machine keeps them in step
    (`Proof/KontFrameReflect.lean`; same shape as `dmTarget?`/`dmTargetM`). -/
def removeOk (m : Machine) (o : ObjId) (undef : Bool) (names : List String) : Bool :=
  (removeNames m o undef names).isSome

/-- The machine the walk produces — the original one if it failed, which is what the error
    path uses anyway. -/
def removeRun (m : Machine) (o : ObjId) (undef : Bool) (names : List String) : Machine :=
  (removeNames m o undef names).getD m

/-- The closure a block argument carries. Named for the same reason as `hasCatcher`: as the
    inline `blk.bind (procClosure? m)` it was, the framing rewrite fires *inside* the `Option`
    match on one side only, simp renormalises that side's matcher, and `split` then pairs the
    two sides' arms wrongly. One head constant, one rewrite, both sides equal. -/
def blockClosure? (m : Machine) (blk : Option Value) : Option Closure :=
  blk.bind (procClosure? m)

/-- Is there a `catch` marker for `tag` on the continuation? Named (rather than the inline
    `let matched` it used to be) for the continuation-framing proof: this is the *one* read of
    the whole continuation in the reflective layer, so it is the one place framing is
    conditional — pushing a continuation that contains a `catchK` turns an
    `UncaughtThrowError` into a jump — and a named function is what lets that conditional
    rewrite fire under a `match` arm (`Proof/KontFrameReflect.lean`). -/
def hasCatcher (m : Machine) (tag : Value) : Bool :=
  m.kont.any fun k => match k with
    | .catchK t => t.identEq tag
    | _ => false

/-- The class (or eigenclass) `define_method`/`define_singleton_method` installs into.
    **Machine-free result, deliberately**: this used to be one `let target? : Option (ObjId ×
    Machine)`, and a matched value that *contains a machine* is what makes the
    continuation-framing proof fail — the pushed and unpushed copies of the scrutinee differ,
    `split` pairs a `none` arm of one with a `some` arm of the other, and the resulting
    impossible goals cannot be closed in place (`Proof/KontFrameReflect.lean`). Split into an
    id lookup and the machine it grows, both scrutinee-shaped, the arms line up. -/
def dmTarget? (m : Machine) (recv : Value) (singleton : Bool) : Option ObjId :=
  if singleton then
    match recv with
    | .ref o => some (eigenclassOf m o).1
    | _ => none
  else match recv with
    | .ref o => if (m.heap.classPayload? o).isSome then some o else none
    | _ => none

/-- The machine `dmTarget?` grows: `define_singleton_method` on a plain object allocates the
    eigenclass, everything else leaves the machine alone. -/
def dmTargetM (m : Machine) (recv : Value) (singleton : Bool) : Machine :=
  if singleton then
    match recv with
    | .ref o => (eigenclassOf m o).2
    | _ => m
  else m

def reflectDefineMethod (m : Machine) (recv : Value) (mname : String)
    (args : List Value) (blk : Option Value) : Option StepResult :=
    -- A method whose body is a *closure* (artifact 02 §1 + 04 §1): the body sees
    -- the defining scope's locals, but `self` is the receiver at call time and
    -- `return` returns from the method. `capturedFrame` on the MethodDef is what
    -- carries the first half; the frame kind (`.method`) the second.
    match args with
    | nameArg :: rest =>
      match symOrStr m nameArg with
      | none => none
      | some name =>
        -- body from the block, or from a Proc/lambda passed as the 2nd argument
        let cl? := match blk with
          | some bv => procClosure? m bv
          | none => match rest with | [pv] => procClosure? m pv | _ => none
        match cl? with
        | none => none   -- a `Method`/`UnboundMethod` argument: falls to the gate
        | some cl =>
            -- `cl.locals` (block-locals, explicit and parse-time-implicit alike)
            -- used to gate here. They belong on the MethodDef instead: the body
            -- must bind them in its *own* activation, or an assignment walks the
            -- `capturedFrame` chain and clobbers a same-named outer local — the
            -- L125 defect, one frame kind over (C35).
            let singleton := mname == "define_singleton_method"
            match dmTarget? m recv singleton with
            | none => none   -- non-Module receiver: CRuby's NoMethodError; gate below
            | some target =>
              let m := dmTargetM m recv singleton
              -- constants in the body resolve at the *definition* site [V]
              let cref := (m.frames.getD (cl.captured.getD 0) default).cref
              -- **J33: capture erasure for closed bodies.** A body that can
              -- never read or write a local (`localFreeB`) never consults the
              -- chain, so installing it chain-free is unobservable — and it is
              -- what lets the typing layer's user-conformance (whose heap-only
              -- vocabulary cannot validate frame pointers, `ResolvesUser`'s
              -- `capturedFrame = none` clause) cover `define_method`-generated
              -- methods. Open bodies keep the capture, byte-for-byte as before.
              let md : MethodDef :=
                { params := cl.params, body := cl.body, owner := target, cref,
                  capturedFrame :=
                    -- fuel bounds the *depth*; any body deeper than this keeps
                    -- its capture (the conservative direction)
                    if localFreeB 1000000 cl.body then none
                    else cl.captured,
                  declared := cl.locals,
                  fromPrelude := m.preludeMode }
              let m := { m with heap := defineMethod m.heap target name md }
              some (.next (withCtl m (.value (.sym name))))
    | [] => none

def reflectEval (m : Machine) (recv : Value) (mname : String)
    (args : List Value) (blk : Option Value) : Option StepResult :=
    -- Block forms only (the string forms are permanently out of scope, artifact
    -- 00 §6, and the desugar gates them upstream). `class_eval` rebinds `self`
    -- *and* the `def` target to the module; `instance_eval` rebinds `self` to the
    -- receiver and the `def` target to its eigenclass (so `def` there defines a
    -- singleton method) [V]. The `_exec` forms pass the caller's args to the
    -- block; the `_eval` forms pass the receiver.
    match blockClosure? m blk with
    | none => none
    | some cl =>
      let isMod := mname == "class_eval" || mname == "module_eval"
        || mname == "class_exec" || mname == "module_exec"
      let isExec := mname == "instance_exec" || mname == "class_exec"
        || mname == "module_exec"
      let blkArgs := if isExec then args else [recv]
      match recv with
      | .ref o =>
        if isMod then
          if (m.heap.classPayload? o).isSome then
            some (callClosure m cl blkArgs none (some recv) (some o))
          else none   -- non-Module receiver: CRuby's NoMethodError; gate below
        else
          let (e, m) := eigenclassOf m o
          some (callClosure m cl blkArgs none (some recv) (some e))
      | _ =>
        if isMod then none
        -- An immediate has no eigenclass, so a `def` inside is CRuby's
        -- "can't define singleton" TypeError; anything else just needs `self`
        -- rebound, which is safe (L72).
        else if definesMethod cl.body then
          some (.unsupported s!"{mname} defining a method on an immediate")
        else some (callClosure m cl blkArgs none (some recv) (some (classOf m.heap recv)))

def reflectCatch (m : Machine) (_recv : Value) (_mname : String)
    (args : List Value) (blk : Option Value) : Option StepResult :=
    -- `catch(tag) { |t| … }` (artifact 04, L69): mark the stack with `catchK` and
    -- run the block with the tag as its argument. A tagless `catch` generates a
    -- fresh object as the tag, exactly as CRuby does.
    match blockClosure? m blk with
    | none => none
    | some cl =>
      match args with
      | [tag] =>
        let m := { m with kont := .catchK tag :: m.kont }
        some (callClosure m cl [tag] none)
      | [] =>
        let (o, hp) := m.heap.alloc { klass := Boot.objectId }
        let tag := Value.ref o
        let m := { m with heap := hp, kont := .catchK tag :: m.kont }
        some (callClosure m cl [tag] none)
      | _ => some (.unsupported "catch/arity")

def reflectThrow (m : Machine) (_recv : Value) (_mname : String)
    (args : List Value) (_blk : Option Value) : Option StepResult :=
    -- With no matching `catch` on the stack, CRuby raises `UncaughtThrowError`
    -- **at the throw site**, so an enclosing `rescue` sees it [V] — checked here
    -- rather than after unwinding, which would have discarded that rescue.
    let go := fun (tag : Value) (v : Value) =>
      if hasCatcher m tag then StepResult.next (withCtl m (.jump (.throwJ tag v)))
      else match Builtins.inspectP m tag with
        | .ok r => .next (raiseErr m Boot.uncaughtThrowErrorId s!"uncaught throw {r}")
        | .error e => .unsupported e
    match args with
    | [tag] => some (go tag .nil)
    | [tag, v] => some (go tag v)
    | _ => some (.unsupported "throw/arity")

def reflectVisibility (m : Machine) (recv : Value) (mname : String)
    (args : List Value) (_blk : Option Value) : Option StepResult :=
    -- artifact 02 §5 (L71). Bare form: set the class body's default visibility.
    -- With names: set those methods' visibility (and, for `module_function`, copy
    -- them to the eigenclass). Returns the names (or nil for the bare form) [V].
    let vis : Visibility := match mname with
      | "public" | "public_class_method" => .pub
      | "protected" => .prot
      | _ => .priv
    match recv with
    | .ref o0 =>
      -- at toplevel the receiver is `main`, and these operate on Object [V]
      let o := if (m.heap.classPayload? o0).isNone then Boot.objectId else o0
      let names := args.filterMap (symOrStr m)
      if names.length != args.length then none
      else if names.isEmpty then
        if mname == "private_class_method" || mname == "public_class_method" then none
        else if mname == "module_function" then
          some (.unsupported "bare module_function (sets a body-wide mode)")
        else
          -- bare `private`/`public`/`protected` in a class body
          let f := m.currentFrame
          let m := m.setCurrentFrame { f with defVis := vis }
          some (.next (withCtl m (.value .nil)))
      else
        -- the target class: the eigenclass for the `*_class_method` forms
        let classMeth := mname == "private_class_method" || mname == "public_class_method"
        let target := if classMeth then (eigenclassOf m o).1 else o
        let m := if classMeth then (eigenclassOf m o).2 else m
        if visOk m o target vis (mname == "module_function") names then
          let m := visRun m o target vis (mname == "module_function") names
          let (arr, m) := Builtins.allocArr m (names.map Value.sym).toArray
          -- a single name answers that name, several answer the array [V]
          match names with
          | [n] => some (.next (withCtl m (.value (.sym n))))
          | _ => some (.next (withCtl m (.value arr)))
        else some (.unsupported s!"{mname} of a method the model does not define")
    | _ => none

def reflectSingletonClass (m : Machine) (recv : Value) (_mname : String)
    (_args : List Value) (_blk : Option Value) : Option StepResult :=
    match recv with
    | .ref o => let (e, m) := eigenclassOf m o; some (.next (withCtl m (.value (.ref e))))
    | .nil | .bool _ =>
      -- nil/true/false answer their own class; immediates raise TypeError.
      some (.next (withCtl m (.value (.ref (classOf m.heap recv)))))
    | _ => some (.unsupported "singleton_class of an immediate (TypeError)")

def reflectIvarGet (m : Machine) (recv : Value) (mname : String)
    (args : List Value) (_blk : Option Value) : Option StepResult :=
    match args with
    | [nameArg] =>
      match symOrStr m nameArg with
      | none => none
      | some n =>
        if !n.startsWith "@" then
          some (.unsupported s!"{mname} with a non-ivar name (NameError message)")
        else
          let ivars := match recv with
            | .ref o => (m.heap.get o).ivars
            | _ => []           -- immediates have no ivars [V]
          let found := ivars.find? (·.1 == n)
          let v : Value := if mname == "instance_variable_get"
            then (found.map (·.2)).getD .nil else .bool found.isSome
          some (.next (withCtl m (.value v)))
    | _ => none

def reflectIvarSet (m : Machine) (recv : Value) (_mname : String)
    (args : List Value) (_blk : Option Value) : Option StepResult :=
    match recv, args with
    | .ref o, [nameArg, val] =>
      match symOrStr m nameArg with
      | none => none
      | some n =>
        if !n.startsWith "@" then
          some (.unsupported "instance_variable_set with a non-ivar name (NameError message)")
        else if (m.heap.get o).frozen then
          match Builtins.inspectP m recv with
          | .ok r => some (.next (raiseErr m Boot.frozenErrorId
              s!"can't modify frozen {className m.heap (m.heap.get o).klass}: {r}"))
          | .error e => some (.unsupported e)
        else
          let obj := m.heap.get o
          let obj := { obj with ivars := (n, val) :: obj.ivars.filter (·.1 != n) }
          some (.next (withCtl { m with heap := m.heap.set o obj } (.value val)))
    | _, _ => none

def reflectIvarNames (m : Machine) (recv : Value) (_mname : String)
    (_args : List Value) (_blk : Option Value) : Option StepResult :=
    -- definition order (our `ivars` list is newest-first, as `Repr` assumes)
    match recv with
    | .ref o =>
      let names := ((m.heap.get o).ivars.reverse).map (fun iv => Value.sym iv.1)
      let (arr, m) := Builtins.allocArr m names.toArray
      some (.next (withCtl m (.value arr)))
    | _ =>
      let (arr, m) := Builtins.allocArr m #[]
      some (.next (withCtl m (.value arr)))

def reflectConstGet (m : Machine) (recv : Value) (mname : String)
    (args : List Value) (_blk : Option Value) : Option StepResult :=
    match recv, args with
    | .ref o, nameArg :: _ =>
      match symOrStr m nameArg, m.heap.classPayload? o with
      | some n, some _ =>
        if n.contains ':' then some (.unsupported s!"{mname} with a scoped name")
        else
          match constLookupFrom m.heap o n with
          | some v =>
            some (.next (withCtl m
              (.value (if mname == "const_get" then v else .bool true))))
          | none =>
            if mname == "const_defined?" then
              -- a constant CRuby has but we don't model would answer a wrong
              -- `false` — same fidelity split as dispatch (L5).
              if crubyToplevelConstants.contains n && o == Boot.objectId then
                some (.unsupported s!"const_defined? of unmodeled constant {n}")
              else some (.next (withCtl m (.value (.bool false))))
            else
              some (.next (raiseErr m Boot.nameErrorId
                s!"uninitialized constant {className m.heap o}::{n}"))
      | _, _ => none
    | _, _ => none

def reflectConstSet (m : Machine) (recv : Value) (_mname : String)
    (args : List Value) (_blk : Option Value) : Option StepResult :=
    match recv, args with
    | .ref o, [nameArg, val] =>
      match symOrStr m nameArg, m.heap.classPayload? o with
      | some n, some _ =>
        some (.next (withCtl { m with heap := constSetIn m.heap o n val } (.value val)))
      | _, _ => none
    | _, _ => none

def reflectRemoveMethod (m : Machine) (recv : Value) (mname : String)
    (args : List Value) (_blk : Option Value) : Option StepResult :=
    -- `remove_method` deletes this class's own entry (an inherited definition
    -- becomes visible again); `undef_method` installs the tombstone (artifact 02).
    match recv with
    | .ref o =>
      match m.heap.classPayload? o with
      | some _ =>
        let names := args.filterMap (symOrStr m)
        if names.length != args.length then none
        else
          if removeOk m o (mname == "undef_method") names then
            some (.next (withCtl (removeRun m o (mname == "undef_method") names) (.value recv)))
          else

            -- CRuby: `NameError: method 'm' not defined in C` [V]; an eigenclass
            -- definee has an address-dependent name we cannot reproduce → gate.
            let dn := className m.heap o
            let missing := (args.filterMap (symOrStr m)).headD ""
            if dn.startsWith "#<" then
              some (.unsupported s!"{mname} of a method not defined in a singleton class")
            else if crubyClassDefines dn missing then
              -- CRuby *does* define it there (e.g. the private
              -- `BasicObject#method_missing`), so it would succeed and change
              -- later dispatch: the L5 fidelity split says gate, not raise.
              some (.unsupported s!"{mname} of unmodeled method {dn}#{missing}")
            else
              some (.next (raiseErr m Boot.nameErrorId
                s!"method '{missing}' not defined in {dn}"))
      | none => none
    | _ => none

def reflectAliasMethod (m : Machine) (recv : Value) (_mname : String)
    (args : List Value) (_blk : Option Value) : Option StepResult :=
    -- `alias` with dynamic names (artifact 02): copy the current definition, so a
    -- later redefinition of the original does not affect the alias [V].
    match recv, args with
    | .ref o, [newA, oldA] =>
      match symOrStr m newA, symOrStr m oldA, m.heap.classPayload? o with
      | some newN, some oldN, some _ =>
        match methodOn m.heap o oldN with
        | some (_, md) =>
          if md.undefined then some (.unsupported "alias_method of an undef'd method")
          else
            -- Keep the original name for `super` (L108) — but only when the
            -- alias lands on the module that *defines* the method. When it does
            -- not, CRuby resumes the search from the original definition's
            -- position in the chain, which this frame cannot express if that
            -- module appears twice (`bootstraptest/test_yjit_145`), so the
            -- cross-module case keeps the old behaviour rather than a new wrong
            -- one. Every use in the sorbet-runtime shim is same-module.
            let md := if md.owner == o then { md with superName := some (md.superName.getD oldN) }
                      else md
            let m := { m with heap := defineMethod m.heap o newN md }
            some (.next (withCtl m (.value (.sym newN))))
        | none => some (.unsupported s!"alias_method of unmodeled method {oldN}")
      | _, _, _ => none
    | _, _ => none

def reflectAttr (m : Machine) (recv : Value) (mname : String)
    (args : List Value) (_blk : Option Value) : Option StepResult :=
    match recv with
    | .ref o => match m.heap.classPayload? o with
      | some _ =>
        let (m, names) := defineAttr m o mname args
        let (arr, m) := Builtins.allocArr m names.toArray
        some (.next (withCtl m (.value arr)))
      | none => none
    | _ => none

def reflectMethodDefined (m : Machine) (recv : Value) (mname : String)
    (args : List Value) (_blk : Option Value) : Option StepResult :=
    match recv, args with
    | .ref o, [nameArg] =>
      match symOrStr m nameArg, m.heap.classPayload? o with
      | some name, some _ =>
        -- `method_defined?` covers public *and* protected; the three specific
        -- predicates ask for exactly one visibility [V].
        let visOk : Visibility → Bool := fun v => match mname with
          | "public_method_defined?" => v == .pub
          | "private_method_defined?" => v == .priv
          | "protected_method_defined?" => v == .prot
          | _ => v != .priv
        let found := (match methodOn m.heap o name with
            | some (_, md) => !md.undefined && visOk md.visibility
            | none => false)
          || (crubyShadow m.heap (ancestors m.heap o) name).isSome
          || mixinDefines m o name
        some (.next (withCtl m (.value (.bool found))))
      | _, _ => none
    | _, _ => none

def reflectRespondTo (m : Machine) (recv : Value) (_mname : String)
    (args : List Value) (_blk : Option Value) : Option StepResult :=
    match args with
    | nameArg :: rest =>
      let inclPrivate := match rest with
        | [v] => v.truthy
        | _ => false
      match symOrStr m nameArg with
      | some name =>
        -- private *and* protected answer false unless include_private [V]
        let found := (match lookup m.heap recv name with
            | some (_, md) => !md.undefined && (inclPrivate || md.visibility == .pub)
            | none => false)
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

/-- Class macros + reflection (artifact 02): `attr_*` (define accessors),
    `method_defined?` (instance-method presence on a class), `respond_to?`
    (method presence on a receiver — user or modeled/CRuby builtin),
    `define_method`/`define_singleton_method`/`alias_method` (L64). Only reached
    on a lookup miss, so a user override wins. -/
def tryReflect (m : Machine) (recv : Value) (mname : String)
    (args : List Value) (blk : Option Value) : Option StepResult :=
  match mname with
  | "define_method" | "define_singleton_method" => reflectDefineMethod m recv mname args blk
  | "class_eval" | "module_eval" | "class_exec" | "module_exec"
  | "instance_eval" | "instance_exec" => reflectEval m recv mname args blk
  | "catch" => reflectCatch m recv mname args blk
  | "throw" => reflectThrow m recv mname args blk
  | "public" | "private" | "protected" | "module_function"
  | "private_class_method" | "public_class_method" => reflectVisibility m recv mname args blk
  | "singleton_class" => reflectSingletonClass m recv mname args blk
  | "instance_variable_get" | "instance_variable_defined?" => reflectIvarGet m recv mname args blk
  | "instance_variable_set" => reflectIvarSet m recv mname args blk
  | "instance_variables" => reflectIvarNames m recv mname args blk
  | "const_defined?" | "const_get" => reflectConstGet m recv mname args blk
  | "const_set" => reflectConstSet m recv mname args blk
  | "remove_method" | "undef_method" => reflectRemoveMethod m recv mname args blk
  | "alias_method" => reflectAliasMethod m recv mname args blk
  | "attr_reader" | "attr_writer" | "attr_accessor" => reflectAttr m recv mname args blk
  | "method_defined?" | "public_method_defined?" | "private_method_defined?"
  | "protected_method_defined?" => reflectMethodDefined m recv mname args blk
  | "respond_to?" => reflectRespondTo m recv mname args blk
  | _ => none

/-- A lookup miss (no entry, or an `undef` tombstone): gate CRuby-shadowed
    names, else route to `method_missing` (user override) or the byte-exact
    `NoMethodError` (artifact 02 §4). Shared by the genuine-miss and
    tombstone-hit dispatch paths. -/
def dispatchMiss (m : Machine) (recv : Value) (implicit : SendSite) (mname : String)
    (args : List Value) (blk : Option Value) : StepResult :=
  match tryIterator m recv mname args blk with
  | some sr => sr
  | none =>
  match tryMixin m recv mname args with
  | some sr => sr
  | none =>
  match tryReflect m recv mname args blk with
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

/-- The site kind a `send`-family re-dispatch runs at: `send`/`__send__` bypass
    visibility, `public_send` does not [V]. A top-level `match` rather than an
    inline `ite`, so `invoke` stays reducible for the metatheory (L73). -/
def reflectiveSite : String → SendSite
  | "public_send" => .explicit
  | _ => .reflective

end Interp

end RubyCore
