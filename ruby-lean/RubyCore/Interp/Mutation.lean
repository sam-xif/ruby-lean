import RubyCore.Interp.Dispatch

/-! Method-table writes commit individually, then call Ruby hooks.
    A callback can raise, freeze the target, or change the next method. -/
namespace RubyCore.Interp

def methodEditMiss (m : Machine) (target : ObjId) (name : String) (removeOnly : Bool)
    (checkNative := true) (fallbackObject := false) : StepResult :=
  let chain := (if removeOnly then [target] else ancestors m.heap target) ++
    (if fallbackObject && (m.heap.classPayload? target).any (·.isModule) then ancestors m.heap Boot.objectId else [])
  match (if checkNative then crubyShadow m.heap chain name else none) with
  | some owner => .unsupported s!"mutation of unmodeled method {owner}#{name}"
  | none =>
  match m.heap.classPayload? target with
  | none => .unsupported "method mutation outside a class/module"
  | some cp =>
    if cp.attached.isSome || cp.name.isEmpty then
      .unsupported "missing method mutation on an anonymous or singleton class" else
    let message := if removeOnly then s!"method '{name}' not defined in {cp.name}" else
      s!"undefined method '{name}' for {if cp.isModule then "module" else "class"} '{cp.name}'"
    .next (raiseErr m Boot.nameErrorId message)

/-- Queue ordinary dispatch, so private hooks, aliases, super, undef tombstones
    and method_missing follow the same rules as other Ruby calls. -/
def finishMethodEdit (m : Machine) (target : ObjId) (event name : String)
    (remaining : List MethodEdit) (result : Value) : StepResult :=
  let m := { m with kont := .methodEditsK remaining result :: m.kont }
  if m.preludeMode || event.isEmpty then .next { m with ctl := .value .nil } else
  let attached := (m.heap.classPayload? target).bind (·.attached)
  let receiver := attached.getD target
  let hook := (if attached.isSome then "singleton_method_" else "method_") ++ event
  .next { m with ctl := .send (.ref receiver) .reflective hook [.sym name] none [] }

/-- Alias and visibility macros on a module also consult Object. Undef/remove
    do not use this fallback. An explicit tombstone still stops the search. -/
def methodForMacro (m : Machine) (target : ObjId) (name : String) : Option (ObjId × MethodDef) :=
  (methodOn m.heap target name).orElse fun _ =>
    if (m.heap.classPayload? target).any (·.isModule) then methodOn m.heap Boot.objectId name else none

def methodEntryForMacro (m : Machine) (target : ObjId) (name : String) : Option (ObjId × MethodDef) :=
  (methodEntryInChain m.heap (ancestors m.heap target) name).orElse fun _ =>
    if (m.heap.classPayload? target).any (·.isModule) then
      methodEntryInChain m.heap (ancestors m.heap Boot.objectId) name else none

def normalizeDefinitionVisibility (h : Heap) (target : ObjId) (name : String) (md : MethodDef) : MethodDef :=
  if ["initialize", "initialize_copy", "initialize_dup", "initialize_clone"].contains name &&
      ((h.classPayload? target).bind (·.attached)).isNone then { md with visibility := .priv } else md

def runMethodEdits (m : Machine) (edits : List MethodEdit) (result : Value) : StepResult :=
  match edits with
  | [] => .next { m with ctl := .value result }
  | edit :: rest =>
    let target := match edit with
      | .define k .. | .aliasMethod k .. | .remove k .. | .visibility k .. | .moduleFunction k .. => k
    if let some receiver := frozenMethodReceiver? m.heap target then raiseFrozen m receiver else
    match edit with
    | .define _ name md =>
      let md := normalizeDefinitionVisibility m.heap target name md
      finishMethodEdit { m with heap := defineMethod m.heap target name md } target "added" name rest result
    | .aliasMethod _ name original =>
      match methodForMacro m target original with
      | some (_, md) =>
        if md.undefined then methodEditMiss m target original false false else
        let scope := md.superScope.orElse fun _ =>
          if (m.heap.classPayload? target).any (·.isModule) then none else some target
        let md := { md with superName := some (md.superName.getD original), superScope := scope }
        let md := normalizeDefinitionVisibility m.heap target name md
        finishMethodEdit { m with heap := defineMethod m.heap target name md } target "added" name rest result
      | none => methodEditMiss m target original false true true
    | .remove _ name undefine =>
      let found := if undefine then (methodEntryInChain m.heap (ancestors m.heap target) name).map Prod.snd else
        (m.heap.classPayload? target).bind fun cp => (cp.methods.find? (·.1 == name)).map Prod.snd
      match found with
      | some md =>
        if md.undefined then methodEditMiss m target name (!undefine) false else
        let h := if undefine then undefMethod m.heap target name else
          match m.heap.classPayload? target with
          | some cp => m.heap.setClassPayload target { cp with methods := cp.methods.filter (·.1 != name) }
          | none => m.heap
        finishMethodEdit { m with heap := h } target (if undefine then "undefined" else "removed") name rest result
      | none => methodEditMiss m target name (!undefine)
    | .visibility _ name vis =>
      match methodEntryForMacro m target name with
      | some (owner, md) =>
        if md.undefined then methodEditMiss m target name false false else
        if md.visibility == vis then finishMethodEdit m target "" name rest result else
        let md := { md with visibility := vis, visibilityOnly := md.visibilityOnly || owner != target }
        finishMethodEdit { m with heap := defineMethod m.heap target name md } target "" name rest result
      | none => methodEditMiss m target name false true true
    | .moduleFunction _ name =>
      match methodForMacro m target name with
      | some (owner, md) =>
        if md.undefined then methodEditMiss m target name false false else
        let m := if md.visibility == .priv then m else
          { m with heap := defineMethod m.heap target name { md with visibility := .priv, visibilityOnly := owner != target } }
        let (e, m) := eigenclassOf m target
        if let some receiver := frozenMethodReceiver? m.heap e then raiseFrozen m receiver else
        let md := { md with visibility := .pub, owner := e, superScope := none }
        finishMethodEdit { m with heap := defineMethod m.heap e name md } e "added" name rest result
      | none => methodEditMiss m target name false true true

end RubyCore.Interp
