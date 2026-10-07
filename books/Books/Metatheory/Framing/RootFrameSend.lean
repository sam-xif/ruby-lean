import Books.Metatheory.Framing.RootFrameNative

/-! Root-execution framing for method dispatch and argument evaluation. -/
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 400000
namespace RubyCore.Proof.Root
open Builtins Interp

@[rootFrameLem] theorem getLocal_frame (K : List Kont) (m : Machine) (x : String) :
    (pushRootK K m).getLocal x = m.getLocal x := by
  have hg : ∀ fuel fid, Machine.getLocal.go (pushRootK K m) x fid fuel = Machine.getLocal.go m x fid fuel := by
    intro fuel
    induction fuel with
    | zero => intro fid; rfl
    | succ fuel ih =>
      intro fid
      simp only [Machine.getLocal.go, rootFrameLem]
      split
      · rfl
      · split
        · exact ih _
        · rfl
  simp only [Machine.getLocal, rootFrameLem, hg]

@[rootFrameLem] theorem reifyCallBlock_frame (K : List Kont) (m : Machine)
    (ps : List Param) (ls : List String) (body : Expr) (lam : Bool) :
    reifyCallBlock (pushRootK K m) ps ls body lam =
      ((reifyCallBlock m ps ls body lam).1, pushRootK K (reifyCallBlock m ps ls body lam).2) := by
  unfold reifyCallBlock
  simp only [rootFrameLem]
  generalize reifyBlock m ps ls body lam = p
  cases he : p.2.activeEnumerator <;> simp [pushRootK, he]

/-- Proof-only dispatcher stages; the enclosing views are definitionally checked. -/
def dispatchBuiltinView (m : Machine) (recv : Value) (mname : String)
    (args : List Value) (blk : Option Value) (kw : List (Value × Value))
    (owner : ObjId) (bid : String) : StepResult :=
  if bid.startsWith "Main#" then
    let (args, m) := appendKwHash m args kw
    callMainMethod m recv bid args blk else
  if bid == "Object#inspect" then callObjectInspect m recv args kw else
  if bid == "Object#raise" || bid == "Object#fail" then callRaise m args kw else
  if bid == "Exception.exception" then callConstruct m recv args blk kw else
  if bid == "Exception#exception" then callExceptionCopy m recv args kw else
  if bid == "Exception#to_s" then callExceptionMessage m recv args kw else
  if bid == "UncaughtThrowError#to_s" then callUncaughtMessage m recv args kw else
  if nativeDupBid bid then callNativeDup m recv args kw else
  if bid == "Object#initialize_dup" then callNativeInitializeDup m recv args kw else
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
  match Builtins.deferTwin? m.heap bid recv args with
  | some slow =>
    match methodOn m.heap (classOf m.heap recv) slow with
    | some (_, md2) => enterUserMethod m recv slow md2 args blk kw
    | none => .unsupported s!"prelude twin {slow} is missing from the prelude"
  | none =>
  if blk.isSome && Builtins.blockSensitiveBids.contains bid then
    match lookupAbove m.heap recv owner mname with
    | some (_, md2) =>
      if md2.builtin.isNone then enterUserMethod m recv mname md2 args blk kw
      else .unsupported s!"block passed to builtin {bid}"
    | none => .unsupported s!"block passed to builtin {bid}"
  else
  let (args, m) := appendKwHash m args kw
  constructResult (Builtins.run bid recv args m)

@[rootFrameLem] theorem dispatchBuiltinView_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (mname : String) (args : List Value)
    (blk : Option Value) (kw : List (Value × Value)) (owner : ObjId) (bid : String) :
    dispatchBuiltinView (pushRootK K m) recv mname args blk kw owner bid =
      rootFrameR K (dispatchBuiltinView m recv mname args blk kw owner bid) := by
  have hLock := hK.hashLockFree
  unfold dispatchBuiltinView
  simp only [pushRootK_heap]
  repeat' (first
    | with_reducible rfl
    | root_unwrap
    | root_split
    | root_progress (simp (disch := assumption) only [rootFrameLem, Option.map_some, Option.map_none])
    | root_back K hK
    | root_progress (simp_all only [rootFrameLem]))

def invokeDispatchView (m : Machine) (recv : Value) (implicit : SendSite) (mname : String)
    (args : List Value) (blk : Option Value) (kw : List (Value × Value)) : StepResult :=
  let chain := ancestors m.heap (classOf m.heap recv)
  match lookup m.heap recv mname with
  | some (owner, md) =>
    if md.undefined then
      invokeMethodMissing m recv implicit mname args blk (kw := kw)
    else
    let between := if md.fromPrelude then [] else chain.takeWhile (· != owner)
    match crubyResolvedShadow m.heap between mname md with
    | some cname => .unsupported s!"unmodeled builtin would shadow: {cname}#{mname}"
    | none =>
    match visError? m recv implicit md mname with
    | some _ =>
      invokeMethodMissing m recv implicit mname args blk
        (if md.visibility == .priv then .privateCall else .protectedCall) kw
    | none =>
      match md.builtin with
      | some bid => dispatchBuiltinView m recv mname args blk kw owner bid
      | none =>
        enterUserMethod m recv mname md args blk kw
  | none =>
    dispatchMiss m recv implicit mname args blk kw

@[rootFrameLem] theorem invokeDispatch_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (implicit : SendSite) (mname : String)
    (args : List Value) (blk : Option Value) (kw : List (Value × Value)) :
    invoke.invokeDispatch (pushRootK K m) recv implicit mname args blk kw =
      rootFrameR K (invoke.invokeDispatch m recv implicit mname args blk kw) := by
  have hLock := hK.hashLockFree
  change invokeDispatchView (pushRootK K m) recv implicit mname args blk kw =
    rootFrameR K (invokeDispatchView m recv implicit mname args blk kw)
  unfold invokeDispatchView
  root_native_walk K hK

def invokeView (m : Machine) (recv : Value) (implicit : SendSite) (mname : String)
    (args : List Value) (blk : Option Value) (kw : List (Value × Value) := []) : StepResult :=
  if (mname == "send" || mname == "public_send" || mname == "__send__")
      && (lookup m.heap recv mname).isNone then
    match args with
    | nameArg :: rest =>
      match symOrStr m nameArg with
      | some m2 => invoke m recv (reflectiveSite mname) m2 rest blk kw
      | none => invoke.invokeDispatch m recv implicit mname args blk kw
    | [] => invoke.invokeDispatch m recv implicit mname args blk kw
  else
  match recv with
  | .ref o =>
    match (m.heap.get o).payload with
    | .hsh xs =>
      match mname, args, (m.heap.get o).hashDflt with
      | "[]", [key], some (.prc bo) =>
        if xs.any (fun (k, _) => valueEql m.heap k key) then
          invoke.invokeDispatch m recv implicit mname args blk kw
        else
          match (m.heap.get bo).payload with
          | .proc cl => callClosure m cl [recv, key] none
          | _ => invoke.invokeDispatch m recv implicit mname args blk kw
      | _, _, _ => invoke.invokeDispatch m recv implicit mname args blk kw
    | .cls _ =>
      if o == Boot.regexpId && (mname == "escape" || mname == "quote" || mname == "union") then
        constructResult (Builtins.run ("Regexp#" ++ mname) recv args m)
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
        | _, _ => invoke.invokeDispatch m recv implicit mname args blk kw
      else invoke.invokeDispatch m recv implicit mname args blk kw
    | _ => invoke.invokeDispatch m recv implicit mname args blk kw
  | _ => invoke.invokeDispatch m recv implicit mname args blk kw

@[rootFrameLem] theorem invoke_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (implicit : SendSite) (mname : String)
    (args : List Value) (blk : Option Value) (kw : List (Value × Value)) :
    invoke (pushRootK K m) recv implicit mname args blk kw =
      rootFrameR K (invoke m recv implicit mname args blk kw) := by
  have hLock := hK.hashLockFree
  induction args generalizing m recv implicit mname blk kw with
  | nil =>
    rw [invoke.eq_def, invoke.eq_def]
    change invokeView (pushRootK K m) recv implicit mname _ blk kw =
      rootFrameR K (invokeView m recv implicit mname _ blk kw)
    unfold invokeView
    root_native_walk K hK
  | cons a rest ih =>
    rw [invoke.eq_def, invoke.eq_def]
    change invokeView (pushRootK K m) recv implicit mname _ blk kw =
      rootFrameR K (invokeView m recv implicit mname _ blk kw)
    unfold invokeView
    simp (disch := assumption) only [rootFrameLem, ih]
    root_native_walk K hK

def superBuiltinView (m : Machine) (recv : Value) (mname : String)
    (args : List Value) (blk : Option Value) (kw : List (Value × Value)) (bid : String) : StepResult :=
  if bid.startsWith "Main#" then
    let (args, m) := appendKwHash m args kw
    callMainMethod m recv bid args blk else
  if bid == "Object#inspect" then callObjectInspect m recv args kw else
  if bid == "Object#raise" || bid == "Object#fail" then callRaise m args kw else
  if bid == "Exception.exception" then callConstruct m recv args blk kw else
  if bid == "Exception#exception" then callExceptionCopy m recv args kw else
  if bid == "Exception#to_s" then callExceptionMessage m recv args kw else
  if bid == "UncaughtThrowError#to_s" then callUncaughtMessage m recv args kw else
  if nativeDupBid bid then callNativeDup m recv args kw else
  if bid == "Object#initialize_dup" then callNativeInitializeDup m recv args kw else
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
  match Builtins.deferTwin? m.heap bid recv args with
  | some slow =>
    match methodOn m.heap (classOf m.heap recv) slow with
    | some (_, md2) => enterUserMethod m recv slow md2 args blk kw
    | none => .unsupported s!"prelude twin {slow} is missing from the prelude"
  | none =>
  let (args, m) := appendKwHash m args kw
  constructResult (Builtins.run bid recv args m)

@[rootFrameLem] theorem superBuiltinView_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (mname : String) (args : List Value)
    (blk : Option Value) (kw : List (Value × Value)) (bid : String) :
    superBuiltinView (pushRootK K m) recv mname args blk kw bid =
      rootFrameR K (superBuiltinView m recv mname args blk kw bid) := by
  have hLock := hK.hashLockFree
  unfold superBuiltinView
  simp only [pushRootK_heap]
  repeat' (first
    | with_reducible rfl
    | root_unwrap
    | root_split
    | root_progress (simp (disch := assumption) only [rootFrameLem, Option.map_some, Option.map_none])
    | root_back K hK
    | root_progress (simp_all only [rootFrameLem]))

def doSuperView (m : Machine) (args : List Value) (blk : Option Value)
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
      | some bid => superBuiltinView m self f.meth args blk kw bid
      | none =>
        let md := { md with superScope := md.superScope.orElse (fun _ => f.superScope) }
        enterUserMethod m self f.meth md args blk kw
    | none =>
      match crubyShadow m.heap chain f.meth with
      | some cname => .unsupported s!"unmodeled super method {cname}#{f.meth}"
      | none =>
        invokeMethodMissing m self .implicit f.meth args blk .superCall kw

@[rootFrameLem] theorem doSuper_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (args : List Value) (blk : Option Value)
    (kw : List (Value × Value)) :
    doSuper (pushRootK K m) args blk kw = rootFrameR K (doSuper m args blk kw) := by
  have hLock := hK.hashLockFree
  change doSuperView (pushRootK K m) args blk kw = rootFrameR K (doSuperView m args blk kw)
  unfold doSuperView
  root_native_walk K hK

@[rootFrameLem] theorem zsuperArgs_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) :
    zsuperArgs (pushRootK K m) = zsuperArgs m := by
  have hLock := hK.hashLockFree
  unfold zsuperArgs
  root_native_walk K hK

@[rootFrameLem] theorem methodBlk_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) :
    methodBlk (pushRootK K m) = methodBlk m := by
  have hLock := hK.hashLockFree
  unfold methodBlk
  root_native_walk K hK

@[rootFrameLem] theorem startSuperArgs_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (acc : List Value) (rest : List Expr)
    (blk : Option Value) :
    startSuperArgs (pushRootK K m) acc rest blk = rootFrameR K (startSuperArgs m acc rest blk) := by
  have hLock := hK.hashLockFree
  unfold startSuperArgs
  root_native_walk K hK

@[rootFrameLem] theorem invokeQueued_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (site : SendSite) (name : String)
    (args : List Value) (blk : Option Value) (kw : List (Value × Value)) :
    invokeQueued (pushRootK K m) recv site name args blk kw = rootFrameR K (invokeQueued m recv site name args blk kw) := by
  have hLock := hK.hashLockFree
  unfold invokeQueued
  root_native_walk K hK

@[rootFrameLem] theorem finishSend_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (implicit : SendSite) (mname : String)
    (args : List Value) (pblk : PendingBlk) (kw : List (Value × Value)) :
    finishSend (pushRootK K m) recv implicit mname args pblk kw = rootFrameR K (finishSend m recv implicit mname args pblk kw) := by
  have hLock := hK.hashLockFree
  unfold finishSend
  root_native_walk K hK

@[rootFrameLem] theorem startKwargs_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (implicit : SendSite) (mname : String)
    (posArgs : List Value) (kwacc : List (Value × Value)) (entries : List KwEntry)
    (pblk : PendingBlk) :
    startKwargs (pushRootK K m) recv implicit mname posArgs kwacc entries pblk = rootFrameR K (startKwargs m recv implicit mname posArgs kwacc entries pblk) := by
  have hLock := hK.hashLockFree
  unfold startKwargs
  root_native_walk K hK

@[rootFrameLem] theorem forwardBundle_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) :
    forwardBundle (pushRootK K m) = forwardBundle m := by
  have hLock := hK.hashLockFree
  unfold forwardBundle
  root_native_walk K hK

@[rootFrameLem] theorem startArgs_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (implicit : SendSite) (mname : String)
    (acc : List Value) (rest : List Expr) (pblk : PendingBlk) :
    startArgs (pushRootK K m) recv implicit mname acc rest pblk = rootFrameR K (startArgs m recv implicit mname acc rest pblk) := by
  have hLock := hK.hashLockFree
  unfold startArgs
  root_native_walk K hK

@[rootFrameLem] theorem startYield_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (acc : List Value) (rest : List Expr) :
    startYield (pushRootK K m) acc rest = rootFrameR K (startYield m acc rest) := by
  have hLock := hK.hashLockFree
  unfold startYield
  root_native_walk K hK

def forMachineView (m : Machine) (block : Value) (targets : List (TargetKind × String))
    (multiple : Bool) : Machine :=
  match block with
  | .ref o => match (m.heap.get o).payload with
    | .proc cl => {m with heap := m.heap.set o {m.heap.get o with
        payload := .proc {cl with forTargets := some targets, forMultiple := multiple}}}
    | _ => m
  | _ => m

@[rootFrameLem] theorem forMachineView_frame (K : List Kont) (m : Machine) (block : Value)
    (targets : List (TargetKind × String)) (multiple : Bool) :
    forMachineView (pushRootK K m) block targets multiple =
      pushRootK K (forMachineView m block targets multiple) := by
  unfold forMachineView
  simp only [pushRootK_heap]
  split <;> first | rfl | (split <;> rfl)

def startForView (m : Machine) (targets : List (TargetKind × String)) (body : Expr)
    (multiple : Bool) (collection : Value) : StepResult :=
  let params := if multiple then [Param.rest none] else [Param.req "<for argument>"]
  let (block, m) := reifyCallBlock m params [] body false
  invoke (forMachineView m block targets multiple) collection .explicit "each" [] (some block)

@[rootFrameLem] theorem startFor_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (targets : List (TargetKind × String)) (body : Expr)
    (multiple : Bool) (collection : Value) :
    startFor (pushRootK K m) targets body multiple collection = rootFrameR K (startFor m targets body multiple collection) := by
  have hLock := hK.hashLockFree
  change startForView (pushRootK K m) targets body multiple collection =
    rootFrameR K (startForView m targets body multiple collection)
  unfold startForView
  root_native_walk K hK

@[rootFrameLem] theorem cvarScope_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) :
    cvarScope (pushRootK K m) = cvarScope m := by
  have hLock := hK.hashLockFree
  unfold cvarScope
  root_native_walk K hK

@[rootFrameLem] theorem definedMethod?_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (mname : String)
    (site : SendSite := .implicit) :
    definedMethod? (pushRootK K m) recv mname site = definedMethod? m recv mname site := by
  have hLock := hK.hashLockFree
  unfold definedMethod?
  root_native_walk K hK
  simp only [Option.isNone_map]


#print axioms RubyCore.Proof.Root.invoke_frame
#print axioms RubyCore.Proof.Root.doSuper_frame
end RubyCore.Proof.Root
