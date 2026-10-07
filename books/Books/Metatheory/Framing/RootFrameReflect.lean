import Books.Metatheory.Framing.RootFrameProtocols

/-! Framing reflective and iterator entry points. -/
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace RubyCore.Proof.Root
open Builtins Interp

@[rootFrameLem] theorem blockClosure_frame (K : List Kont) (m : Machine) (v : Option Value) :
    blockClosure? (pushRootK K m) v = blockClosure? m v := rfl

@[rootFrameLem] theorem mixinDefines_frame (K : List Kont) (m : Machine) (k : ObjId) (name : String) :
    mixinDefines (pushRootK K m) k name = mixinDefines m k name := rfl

@[rootFrameLem] theorem raiseUncaughtThrow_frame (K : List Kont) (m : Machine) (tag v : Value) :
    raiseUncaughtThrow (pushRootK K m) tag v = pushRootK K (raiseUncaughtThrow m tag v) := by
  cases ha : m.activeEnumerator <;>
    simp [raiseUncaughtThrow, Builtins.allocStr, Builtins.allocStrEnc, pushRootK, ha]

@[rootFrameLem] theorem unmodeledNamespaceConstant_frame (K : List Kont) (m : Machine)
    (k : ObjId) (name : String) (inherit : Bool) :
    unmodeledNamespaceConstant (pushRootK K m) k name inherit =
      unmodeledNamespaceConstant m k name inherit := rfl

@[rootFrameLem] theorem libraryBodyGate_frame (K : List Kont) (m : Machine) (k : ObjId) :
    libraryBodyGate (pushRootK K m) k = libraryBodyGate m k := rfl

@[rootFrameLem] theorem hasCatcher_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (tag : Value) : hasCatcher (pushRootK K m) tag = hasCatcher m tag := by
  unfold hasCatcher
  apply any_rootFrame
  apply hK.any_false
  intro k hk
  cases k <;> simp_all [observedKont]

@[rootFrameLem] theorem reflectIvarGet_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (recv : Value) (mname : String) (args : List Value)
  (_blk : Option Value),
  Interp.reflectIvarGet (pushRootK K m) recv mname args _blk = (Interp.reflectIvarGet m recv mname args _blk).map (rootFrameR K) := by
  intros
  unfold RubyCore.Interp.reflectIvarGet
  root_walk K hK

@[rootFrameLem] theorem reflectIvarNames_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (recv : Value) (_mname : String) (_args : List Value)
  (_blk : Option Value),
  Interp.reflectIvarNames (pushRootK K m) recv _mname _args _blk = (Interp.reflectIvarNames m recv _mname _args _blk).map (rootFrameR K) := by
  intros
  unfold RubyCore.Interp.reflectIvarNames
  root_walk K hK

@[rootFrameLem] theorem reflectCatch_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (_recv : Value) (_mname : String) (args : List Value)
  (blk : Option Value),
  Interp.reflectCatch (pushRootK K m) _recv _mname args blk = (Interp.reflectCatch m _recv _mname args blk).map (rootFrameR K) := by
  intros
  unfold RubyCore.Interp.reflectCatch
  root_walk K hK

@[rootFrameLem] theorem reflectThrow_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (_recv : Value) (_mname : String) (args : List Value)
  (_blk : Option Value),
  Interp.reflectThrow (pushRootK K m) _recv _mname args _blk = (Interp.reflectThrow m _recv _mname args _blk).map (rootFrameR K) := by
  intros
  unfold RubyCore.Interp.reflectThrow
  root_walk K hK

@[rootFrameLem] theorem reflectMethodDefined_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (recv : Value) (mname : String) (args : List Value)
  (_blk : Option Value),
  Interp.reflectMethodDefined (pushRootK K m) recv mname args _blk = (Interp.reflectMethodDefined m recv mname args _blk).map (rootFrameR K) := by
  intros
  unfold RubyCore.Interp.reflectMethodDefined
  root_walk K hK

@[rootFrameLem] theorem reflectRespondTo_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (recv : Value) (_mname : String) (args : List Value)
  (_blk : Option Value),
  Interp.reflectRespondTo (pushRootK K m) recv _mname args _blk = (Interp.reflectRespondTo m recv _mname args _blk).map (rootFrameR K) := by
  intros
  unfold RubyCore.Interp.reflectRespondTo
  root_walk K hK

@[rootFrameLem] theorem reflectConstGet_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (recv : Value) (mname : String) (args : List Value)
  (_blk : Option Value),
  Interp.reflectConstGet (pushRootK K m) recv mname args _blk = (Interp.reflectConstGet m recv mname args _blk).map (rootFrameR K) := by
  intros
  unfold RubyCore.Interp.reflectConstGet
  root_walk K hK

@[rootFrameLem] theorem reflectSingletonClass_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (recv : Value) (_mname : String) (_args : List Value)
  (_blk : Option Value),
  Interp.reflectSingletonClass (pushRootK K m) recv _mname _args _blk = (Interp.reflectSingletonClass m recv _mname _args _blk).map (rootFrameR K) := by
  intros
  unfold RubyCore.Interp.reflectSingletonClass
  root_walk K hK

@[rootFrameLem] theorem reflectEval_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (recv : Value) (mname : String) (args : List Value)
  (blk : Option Value), Interp.reflectEval (pushRootK K m) recv mname args blk = (Interp.reflectEval m recv mname args blk).map (rootFrameR K) := by
  intros
  unfold RubyCore.Interp.reflectEval
  root_walk K hK

@[rootFrameLem] theorem doYield_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (args : List Value),
  Interp.doYield (pushRootK K m) args = rootFrameR K (Interp.doYield m args) := by
  intros
  unfold RubyCore.Interp.doYield
  root_walk K hK

@[rootFrameLem] theorem finishEnumerator_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (o : ObjId) (result : Value),
  Interp.finishEnumerator (pushRootK K m) o result = rootFrameR K (Interp.finishEnumerator m o result) := by
  intro m o result
  unfold RubyCore.Interp.finishEnumerator
  simp only [enumState_rootFrame, frameEnumState, Option.isNone_map, rootFrameLem]
  split
  · rfl
  · rw [← newStop_rootFrame K]
    congr 1
    cases ha : m.activeEnumerator <;> simp [pushRootK, allocStr, allocStrEnc, ha]

@[rootFrameLem] theorem iterStep_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (cl : Closure) (brk : FrameId) (rest : List (List Value))
  (kind : IterKind) (acc : List Value) (retVal : Value),
  Interp.iterStep (pushRootK K m) cl brk rest kind acc retVal = rootFrameR K (Interp.iterStep m cl brk rest kind acc retVal) := by
  intros
  unfold RubyCore.Interp.iterStep
  root_walk K hK
  all_goals (try (rw [foldPair_frame K]))
  all_goals (try (intro p m a; cases a <;> rfl))
  all_goals root_walk K hK

@[rootFrameLem] theorem finishMethodEdit_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (target : ObjId) (event name : String) (remaining : List MethodEdit)
  (result : Value),
  Interp.finishMethodEdit (pushRootK K m) target event name remaining result = rootFrameR K (Interp.finishMethodEdit m target event name remaining result) := by
  intros
  unfold RubyCore.Interp.finishMethodEdit
  root_walk K hK

@[rootFrameLem] theorem pushClassFrame_frame (K : List Kont) (hK : ContextFree K) :
    ∀ (m : Machine) (k : ObjId) (libraryName : String) (body : Expr),
  Interp.pushClassFrame (pushRootK K m) k libraryName body = rootFrameR K (Interp.pushClassFrame m k libraryName body) := by
  intros
  unfold RubyCore.Interp.pushClassFrame
  root_walk K hK

end RubyCore.Proof.Root
