import RubyCore.Interp.Reflect

/-! Native construction is selected by the resolved method, after lookup and
visibility. Allocation does not send `allocate`; initialization is an ordinary
private send, including undef/method_missing, aliases and block forwarding. -/
namespace RubyCore.Interp

def constructResult : BRes → StepResult
  | .ok v m => .next (withCtl m (.value v))
  | .err cls msg m => .next (raiseErr m cls msg)
  | .throwV v m => .next (withCtl m (.jump (.raiseJ v)))
  | .frozen recv m => raiseFrozen m recv
  | .unsupported reason => .unsupported reason

def initializeInstance (m : Machine) (inst : Value) (args : List Value)
    (blk : Option Value) (kw : List (Value × Value)) : StepResult :=
  .next { m with ctl := .send inst .reflective "initialize" args blk kw, kont := .newK inst :: m.kont }

/-- The remaining argument-dependent native allocators retain their existing
    implementation until their uninitialized payloads are modeled. -/
def legacyConstruct (m : Machine) (recv : Value) (klass : ObjId)
    (args : List Value) (blk : Option Value) (kw : List (Value × Value)) : StepResult :=
  if (methodOn m.heap klass "initialize").any (fun (_, md) =>
      md.undefined || md.builtin != some "BasicObject#initialize") then
    .unsupported "native constructor with a replaced initializer" else
  let (args, m) := appendKwHash m args kw
  match Builtins.newImpl m recv args with
  | .ok newV m =>
    if klass == Boot.classId || klass == Boot.moduleId then
      match newV, blk with
      | .ref newK, some b => match procClosure? m b with
        | some cl => callClosure { m with kont := .newK newV :: m.kont }
            cl [newV] none (some newV) (some newK)
        | none => .unsupported "class constructor block is not a Proc"
      | _, _ => .next (withCtl m (.value newV))
    else .next (withCtl m (.value newV))
  | result => constructResult result

def callConstruct (m : Machine) (recv : Value) (args : List Value)
    (blk : Option Value) (kw : List (Value × Value)) : StepResult :=
  match recv with
  | .ref klass => match m.heap.classPayload? klass with
    | none => .unsupported "new on a non-class"
    | some cp =>
      if cp.isModule then .unsupported "new on a module" else
      let chain := ancestors m.heap klass
      if chain.any ([Boot.enumeratorId, Boot.generatorId, Boot.yielderId].contains ·) then
        let (inst, m) := enumAllocate m klass
        initializeInstance m inst args blk kw
      else if chain.contains Boot.procId then
        match blk with
        | none => .next (raiseErr m Boot.argumentErrorId "tried to create Proc object without a block")
        | some (.ref o) => match (m.heap.get o).payload with
          | .proc cl =>
            let (inst, m) := if (m.heap.get o).klass == klass then (Value.ref o, m) else
              let (o, h) := m.heap.alloc { klass, payload := .proc cl }
              (Value.ref o, { m with heap := h })
            initializeInstance m inst args blk kw
          | _ => .unsupported "Proc constructor block is not a Proc"
        | some _ => .unsupported "Proc constructor block is not a Proc"
      else if [Boot.classId, Boot.moduleId, Boot.randomId, Boot.regexpId].contains klass then
        legacyConstruct m recv klass args blk kw
      else if chain.any ([Boot.classId, Boot.moduleId, Boot.randomId, Boot.regexpId,
          Boot.rangeId].contains ·) then
        .unsupported "constructor for an unmodeled native payload subclass"
      else if chain.any ([Boot.integerId, Boot.floatId, Boot.symbolId, Boot.rationalId,
          Boot.complexId, Boot.nilClassId, Boot.trueClassId, Boot.falseClassId].contains ·) then
        .next (raiseErr m Boot.typeErrorId s!"allocator undefined for {className m.heap klass}")
      else
        let payload := match Builtins.allocatableCore m.heap klass with
          | some core => if core == Boot.exceptionId then .exc (className m.heap klass)
              else Builtins.emptyCorePayload core
          | none => Payload.none
        let (o, h) := m.heap.alloc { klass, payload }
        initializeInstance { m with heap := h } (.ref o) args blk kw
  | _ => .unsupported "new on a non-class"

def callAllocate (m : Machine) (recv : Value) (args : List Value)
    (kw : List (Value × Value)) : StepResult :=
  let (args, m) := appendKwHash m args kw
  if !args.isEmpty then enumArity m args.length "0" else
  match recv with
  | .ref klass =>
    if (ancestors m.heap klass).any ([Boot.enumeratorId, Boot.generatorId, Boot.yielderId].contains ·) then
      let (v, m) := enumAllocate m klass
      .next (withCtl m (.value v))
    else constructResult (Builtins.run "Class#allocate" recv args m)
  | _ => constructResult (Builtins.run "Class#allocate" recv args m)

def arrayInitYield (m : Machine) (recv : ObjId) (block : Value) (index size : Nat) : StepResult :=
  if index >= size then .next (withCtl m (.value (.ref recv))) else
  match procClosure? m block with
  | some cl => callClosure { m with kont := .arrayInitK recv block index size :: m.kont }
      cl [.int index] none
  | none => .unsupported "Array initializer block is not a Proc"

def arrayInitNext (m : Machine) (recv : ObjId) (block : Value) (index size : Nat)
    (v : Value) : StepResult :=
  if (m.heap.get recv).frozen then raiseFrozen m (.ref recv) else
  match (m.heap.get recv).payload with
  | .arr xs =>
    let xs := if index < xs.size then xs else xs ++ Array.replicate (index + 1 - xs.size) .nil
    let h := m.heap.set recv { m.heap.get recv with payload := .arr (xs.set! index v) }
    arrayInitYield { m with heap := h } recv block (index + 1) size
  | _ => .unsupported "Array initializer receiver has no Array payload"

def callCoreInitialize (m : Machine) (bid : String) (recv : Value) (args : List Value)
    (blk : Option Value) (kw : List (Value × Value)) : StepResult :=
  let (args, m) := appendKwHash m args kw
  match recv, blk with
  | .ref o, some block =>
    if bid == "Hash#initialize" then
      if args.length > 1 then enumArity m args.length "0..1" else
      if (m.heap.get o).frozen then raiseFrozen m recv else
      if !args.isEmpty then enumArity m args.length "0" else
      let valid : Except StepResult Unit := do
        match procClosure? m block with
        | some cl =>
          if cl.lam then
            match classifySimple cl.params with
            | none => .error (.unsupported "Hash default lambda with complex parameters")
            | some ps =>
              let required := ps.pre.length + ps.post.length
              if required > 2 || (ps.rest?.isNone && required != 2) then
                .error (.next (raiseErr m Boot.typeErrorId s!"default_proc takes two arguments (2 for {required})"))
              else .ok ()
          else .ok ()
        | none => .error (.unsupported "Hash initializer block is not a Proc")
      match valid with
      | .error result => result
      | .ok _ =>
      match block with
      | .ref bo =>
        let h := m.heap.set o { m.heap.get o with hashDflt := some (.prc bo) }
        .next (withCtl { m with heap := h } (.value recv))
      | _ => .unsupported "Hash initializer block is not a Proc"
    else if bid == "Array#initialize" && !args.isEmpty then
      match args with
      | .int size :: rest =>
        if (m.heap.get o).frozen then raiseFrozen m recv else
        if rest.length > 1 then enumArity m args.length "0..2" else
        if size < 0 then .next (raiseErr m Boot.argumentErrorId "negative array size") else
        let h := m.heap.set o { m.heap.get o with payload := .arr #[] }
        arrayInitYield { m with heap := h } o block 0 size.toNat
      | _ => constructResult (Builtins.run bid recv args m)
    else constructResult (Builtins.run bid recv args m)
  | _, _ => constructResult (Builtins.run bid recv args m)

end RubyCore.Interp
