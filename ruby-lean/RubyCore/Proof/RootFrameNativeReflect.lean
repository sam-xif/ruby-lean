import RubyCore.Proof.RootFrameNativeSupport

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 600000
namespace RubyCore.Proof.Root
open Builtins Interp

@[rootFrameLem] theorem methodForMacro_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (target : ObjId) (name : String) :
    methodForMacro (pushRootK K m) target name = methodForMacro m target name := by
  have hLock := hK.hashLockFree
  unfold methodForMacro
  root_native_walk K hK

@[rootFrameLem] theorem methodEntryForMacro_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (target : ObjId) (name : String) :
    methodEntryForMacro (pushRootK K m) target name = methodEntryForMacro m target name := by
  have hLock := hK.hashLockFree
  unfold methodEntryForMacro
  root_native_walk K hK

def methodEigenCopyView (m : Machine) (target : ObjId) (name : String)
    (md : MethodDef) (rest : List MethodEdit) (result : Value) : StepResult :=
  let (e, m) := eigenclassOf m target
  if let some receiver := frozenMethodReceiver? m.heap e then raiseFrozen m receiver else
  let md := { md with visibility := .pub, owner := e, superScope := none }
  finishMethodEdit { m with heap := defineMethod m.heap e name md } e "added" name rest result

@[rootFrameLem] theorem methodEigenCopyView_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (target : ObjId) (name : String) (md : MethodDef)
    (rest : List MethodEdit) (result : Value) :
    methodEigenCopyView (pushRootK K m) target name md rest result =
      rootFrameR K (methodEigenCopyView m target name md rest result) := by
  unfold methodEigenCopyView
  root_native_walk K hK

def methodEditsView (m : Machine) (edits : List MethodEdit) (result : Value) : StepResult :=
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
        methodEigenCopyView m target name md rest result
      | none => methodEditMiss m target name false true true

@[rootFrameLem] theorem runMethodEdits_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (edits : List MethodEdit) (result : Value) :
    runMethodEdits (pushRootK K m) edits result = rootFrameR K (runMethodEdits m edits result) := by
  have hLock := hK.hashLockFree
  change methodEditsView (pushRootK K m) edits result = rootFrameR K (methodEditsView m edits result)
  unfold methodEditsView
  root_native_walk K hK

theorem foldOptMachine_frame {α : Type} (K : List Kont)
    (f : Machine → α → Option Machine)
    (hf : ∀ m a, f (pushRootK K m) a = (f m a).map (pushRootK K)) :
    ∀ (xs : List α) (acc : Option Machine), xs.foldl (fun acc a => acc.bind (fun m => f m a)) (acc.map (pushRootK K)) =
      (xs.foldl (fun acc a => acc.bind (fun m => f m a)) acc).map (pushRootK K) := by
  intro xs
  induction xs with
  | nil => intro acc; rfl
  | cons a xs ih =>
    intro acc
    simp only [List.foldl_cons]
    cases acc with
    | none => exact ih none
    | some m => simp only [Option.map_some, Option.bind_some, hf]; exact ih _

def visEigenCopyView (m : Machine) (o : ObjId) (n : String) (md : MethodDef) : Option Machine :=
  let (e, m) := eigenclassOf m o
  some {m with heap := defineMethod m.heap e n {md with visibility := .pub, owner := e}}

@[rootFrameLem] theorem visEigenCopyView_frame (K : List Kont) (m : Machine)
    (o : ObjId) (n : String) (md : MethodDef) :
    visEigenCopyView (pushRootK K m) o n md =
      (visEigenCopyView m o n md).map (pushRootK K) := by
  unfold visEigenCopyView
  rw [eigenclassOf_frame]
  rfl

def visNameView (m : Machine) (o target : ObjId) (vis : Visibility) (modFun : Bool)
    (n : String) : Option Machine :=
  match methodOn m.heap target n with
  | some (_, md) =>
    if md.builtin.isSome && !md.fromPrelude &&
        !(procCallBid (md.builtin.getD "") || arrayMapBid (md.builtin.getD "") ||
          enumBid (md.builtin.getD "") || nativeIteratorBid (md.builtin.getD "") ||
          md.builtin == some "BasicObject#method_missing") then none else
    let m := {m with heap := defineMethod m.heap target n {md with visibility := vis}}
    if modFun then visEigenCopyView m o n md else some m
  | none => none

@[rootFrameLem] theorem visNameView_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (o target : ObjId) (vis : Visibility) (modFun : Bool) (n : String) :
    visNameView (pushRootK K m) o target vis modFun n =
      (visNameView m o target vis modFun n).map (pushRootK K) := by
  unfold visNameView
  root_native_walk K hK
  rename_i result owner md hlookup hbid
  exact visEigenCopyView_frame K
    {m with heap := defineMethod m.heap target n {md with visibility := vis}} o n md


@[rootFrameLem] theorem visNames_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (o target : ObjId) (vis : Visibility) (modFun : Bool)
    (names : List String) :
    visNames (pushRootK K m) o target vis modFun names = (visNames m o target vis modFun names).map (pushRootK K) := by
  have hLock := hK.hashLockFree
  change names.foldl (fun acc n => acc.bind (fun m => visNameView m o target vis modFun n))
      (some (pushRootK K m)) =
    (names.foldl (fun acc n => acc.bind (fun m => visNameView m o target vis modFun n)) (some m)).map (pushRootK K)
  exact foldOptMachine_frame K _ (fun m n => visNameView_frame K hK m o target vis modFun n) names (some m)

@[rootFrameLem] theorem visOk_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (o target : ObjId) (vis : Visibility) (modFun : Bool)
    (names : List String) :
    visOk (pushRootK K m) o target vis modFun names = visOk m o target vis modFun names := by
  have hLock := hK.hashLockFree
  unfold visOk
  simp (disch := assumption) only [rootFrameLem, Option.isSome_map]

@[rootFrameLem] theorem visRun_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (o target : ObjId) (vis : Visibility) (modFun : Bool)
    (names : List String) :
    visRun (pushRootK K m) o target vis modFun names = pushRootK K (visRun m o target vis modFun names) := by
  have hLock := hK.hashLockFree
  unfold visRun
  simp (disch := assumption) only [rootFrameLem, Option.getD_map]

@[rootFrameLem] theorem removeNames_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (o : ObjId) (undef : Bool) (names : List String) :
    removeNames (pushRootK K m) o undef names = (removeNames m o undef names).map (pushRootK K) := by
  have hLock := hK.hashLockFree
  unfold removeNames
  apply (foldOptMachine_frame K _ _ names (some m))
  intro m n
  root_native_walk K hK

@[rootFrameLem] theorem removeOk_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (o : ObjId) (undef : Bool) (names : List String) :
    removeOk (pushRootK K m) o undef names = removeOk m o undef names := by
  have hLock := hK.hashLockFree
  unfold removeOk
  simp (disch := assumption) only [rootFrameLem, Option.isSome_map]

@[rootFrameLem] theorem removeRun_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (o : ObjId) (undef : Bool) (names : List String) :
    removeRun (pushRootK K m) o undef names = pushRootK K (removeRun m o undef names) := by
  have hLock := hK.hashLockFree
  unfold removeRun
  simp (disch := assumption) only [rootFrameLem, Option.getD_map]

@[rootFrameLem] theorem dmTarget?_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (singleton : Bool) :
    dmTarget? (pushRootK K m) recv singleton = dmTarget? m recv singleton := by
  have hLock := hK.hashLockFree
  unfold dmTarget?
  root_native_walk K hK

@[rootFrameLem] theorem dmTargetM_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (singleton : Bool) :
    dmTargetM (pushRootK K m) recv singleton = pushRootK K (dmTargetM m recv singleton) := by
  have hLock := hK.hashLockFree
  unfold dmTargetM
  root_native_walk K hK

@[rootFrameLem] theorem reflectDefineMethod_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (mname : String)
    (args : List Value) (blk : Option Value) :
    reflectDefineMethod (pushRootK K m) recv mname args blk = (reflectDefineMethod m recv mname args blk).map (rootFrameR K) := by
  have hLock := hK.hashLockFree
  unfold reflectDefineMethod
  root_native_walk K hK

def visibilityEditsView (m : Machine) (o target : ObjId) (mname : String)
    (args : List Value) (names : List String) (vis : Visibility) : Option StepResult :=
  if mname == "module_function" && !(m.heap.classPayload? o).any (·.isModule) then
    some (.unsupported "module_function on a class") else
  let edits := names.map fun name =>
    if mname == "module_function" then MethodEdit.moduleFunction o name else .visibility target name vis
  let (arr, m) := Builtins.allocArr m args.toArray
  let result := if args.length == 1 then args.headD .nil else arr
  some (runMethodEdits m edits result)

@[rootFrameLem] theorem visibilityEditsView_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (o target : ObjId) (mname : String) (args : List Value)
    (names : List String) (vis : Visibility) :
    visibilityEditsView (pushRootK K m) o target mname args names vis =
      (visibilityEditsView m o target mname args names vis).map (rootFrameR K) := by
  unfold visibilityEditsView
  root_native_walk K hK

def reflectVisibilityView (m : Machine) (recv : Value) (mname : String)
    (args : List Value) : Option StepResult :=
  let vis : Visibility := match mname with
    | "public" | "public_class_method" => .pub
    | "protected" => .prot
    | _ => .priv
  match recv with
  | .ref o0 =>
    if (m.heap.classPayload? o0).isNone &&
        (o0 != Boot.mainId || !["public", "private"].contains mname) then none else
    let o := if (m.heap.classPayload? o0).isNone then Boot.objectId else o0
    let names := args.filterMap (symOrStr m)
    if names.length != args.length then none
    else if names.isEmpty then
      if mname == "private_class_method" || mname == "public_class_method" then none
      else if mname == "module_function" then
        some (.unsupported "bare module_function (sets a body-wide mode)")
      else some (.next (withCtl (m.setDefinitionVisibility vis) (.value .nil)))
    else
      let classMeth := mname == "private_class_method" || mname == "public_class_method"
      let target := if classMeth then (eigenclassOf m o).1 else o
      let m := if classMeth then (eigenclassOf m o).2 else m
      visibilityEditsView m o target mname args names vis
  | _ => none

@[rootFrameLem] theorem reflectVisibility_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (mname : String)
    (args : List Value) (_blk : Option Value) :
    reflectVisibility (pushRootK K m) recv mname args _blk = (reflectVisibility m recv mname args _blk).map (rootFrameR K) := by
  have hLock := hK.hashLockFree
  change reflectVisibilityView (pushRootK K m) recv mname args =
    (reflectVisibilityView m recv mname args).map (rootFrameR K)
  unfold reflectVisibilityView
  root_native_walk K hK

@[rootFrameLem] theorem reflectIvarSet_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (_mname : String)
    (args : List Value) (_blk : Option Value) :
    reflectIvarSet (pushRootK K m) recv _mname args _blk = (reflectIvarSet m recv _mname args _blk).map (rootFrameR K) := by
  have hLock := hK.hashLockFree
  unfold reflectIvarSet
  root_native_walk K hK

@[rootFrameLem] theorem finishConstantSet_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (target : ObjId) (value nameArg : Value) :
    finishConstantSet (pushRootK K m) target value nameArg = rootFrameR K (finishConstantSet m target value nameArg) := by
  have hLock := hK.hashLockFree
  unfold finishConstantSet
  root_native_walk K hK

@[rootFrameLem] theorem finishConstantNameError_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (source : Option Value) (value : Value) :
    finishConstantNameError (pushRootK K m) source value = rootFrameR K (finishConstantNameError m source value) := by
  have hLock := hK.hashLockFree
  unfold finishConstantNameError
  root_native_walk K hK

@[rootFrameLem] theorem callConstSet_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (args : List Value)
    (kw : List (Value × Value)) :
    callConstSet (pushRootK K m) recv args kw = rootFrameR K (callConstSet m recv args kw) := by
  have hLock := hK.hashLockFree
  unfold callConstSet
  root_native_walk K hK

@[rootFrameLem] theorem reflectRemoveMethod_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (mname : String)
    (args : List Value) (_blk : Option Value) :
    reflectRemoveMethod (pushRootK K m) recv mname args _blk = (reflectRemoveMethod m recv mname args _blk).map (rootFrameR K) := by
  have hLock := hK.hashLockFree
  unfold reflectRemoveMethod
  root_native_walk K hK

@[rootFrameLem] theorem reflectAliasMethod_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (_mname : String)
    (args : List Value) (_blk : Option Value) :
    reflectAliasMethod (pushRootK K m) recv _mname args _blk = (reflectAliasMethod m recv _mname args _blk).map (rootFrameR K) := by
  have hLock := hK.hashLockFree
  unfold reflectAliasMethod
  root_native_walk K hK

@[rootFrameLem] theorem reflectAttr_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (mname : String)
    (args : List Value) (_blk : Option Value) :
    reflectAttr (pushRootK K m) recv mname args _blk = (reflectAttr m recv mname args _blk).map (rootFrameR K) := by
  have hLock := hK.hashLockFree
  unfold reflectAttr
  root_native_walk K hK

@[rootFrameLem] theorem tryReflect_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (mname : String)
    (args : List Value) (blk : Option Value) :
    tryReflect (pushRootK K m) recv mname args blk = (tryReflect m recv mname args blk).map (rootFrameR K) := by
  have hLock := hK.hashLockFree
  rw [tryReflect.eq_def, tryReflect.eq_def]
  split <;> first | rfl | simp (disch := assumption) only [rootFrameLem]

@[rootFrameLem] theorem callMainMethod_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (bid : String)
    (args : List Value) (blk : Option Value) :
    callMainMethod (pushRootK K m) recv bid args blk = rootFrameR K (callMainMethod m recv bid args blk) := by
  have hLock := hK.hashLockFree
  unfold callMainMethod
  root_native_walk K hK

@[rootFrameLem] theorem invokeMethodMissing_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (implicit : SendSite) (mname : String)
    (args : List Value) (blk : Option Value)
    (reason : MissingReason := if implicit == .vcall then .vcall else .ordinary)
    (kw : List (Value × Value) := []) :
    invokeMethodMissing (pushRootK K m) recv implicit mname args blk reason kw = rootFrameR K (invokeMethodMissing m recv implicit mname args blk reason kw) := by
  have hLock := hK.hashLockFree
  unfold invokeMethodMissing
  rw [show ({ pushRootK K m with missingReason := reason } : Machine) =
    pushRootK K { m with missingReason := reason } from rfl]
  root_native_walk K hK

@[rootFrameLem] theorem dispatchMiss_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (implicit : SendSite) (mname : String)
    (args : List Value) (blk : Option Value) (kw : List (Value × Value) := []) :
    dispatchMiss (pushRootK K m) recv implicit mname args blk kw = rootFrameR K (dispatchMiss m recv implicit mname args blk kw) := by
  have hLock := hK.hashLockFree
  unfold dispatchMiss
  root_native_walk K hK


#print axioms RubyCore.Proof.Root.runMethodEdits_frame
#print axioms RubyCore.Proof.Root.reflectVisibility_frame
end RubyCore.Proof.Root
