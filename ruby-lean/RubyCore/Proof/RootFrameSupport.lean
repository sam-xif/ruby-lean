import RubyCore.Proof.RootFramePrimitives

/-! Root-execution framing for interpreter state helpers. -/
set_option autoImplicit false
set_option maxRecDepth 40000
namespace RubyCore.Proof.Root
open Builtins Interp

@[simp, rootFrameLem] theorem rootFrameR_next (K : List Kont) (m : Machine) :
    rootFrameR K (.next m) = .next (pushRootK K m) := rfl
@[simp, rootFrameLem] theorem rootFrameR_unsupported (K : List Kont) (r : String) :
    rootFrameR K (.unsupported r) = .unsupported r := rfl
@[simp, rootFrameLem] theorem rootFrameR_stuck (K : List Kont) (r : String) :
    rootFrameR K (.stuck r) = .stuck r := rfl

attribute [rootFrameLem] suspendEnumerator_rootFrame enumNext_rootFrame finishStop_rootFrame

@[simp, rootFrameLem] theorem withCtl_frame (K : List Kont) (m : Machine) (c : Ctl) :
    withCtl (pushRootK K m) c = pushRootK K (withCtl m c) := rfl

/-- **The one place `kont` is written in this layer, and it frames by `rfl`.** `withKont`
conses onto `m.kont`, and consing before appending is appending after consing. -/
@[simp, rootFrameLem] theorem withKont_frame (K : List Kont) (m : Machine) (c : Ctl) (k : Kont) :
    withKont (pushRootK K m) c k = pushRootK K (withKont m c k) := withKont_rootFrame K m c k

@[simp, rootFrameLem] theorem raiseErr_frame (K : List Kont) (m : Machine) (cls : ObjId) (msg : String) :
    raiseErr (pushRootK K m) cls msg = pushRootK K (raiseErr m cls msg) := by
  unfold raiseErr
  simp only [rootFrameLem]
  split
  · rfl
  · cases ha : m.activeEnumerator <;>
      simp [pushRootK, Builtins.allocStr, Builtins.allocStrEnc, ha]

@[simp, rootFrameLem] theorem localFrameId_frame (K : List Kont) (m : Machine) (fid : FrameId) :
    (pushRootK K m).localFrameId fid = m.localFrameId fid := by
  have hg : ∀ fuel fid, Machine.localFrameId.go (pushRootK K m) fid fuel =
      Machine.localFrameId.go m fid fuel := by
    intro fuel
    induction fuel with
    | zero => intro fid; rfl
    | succ n ih =>
      intro fid
      simp only [Machine.localFrameId.go, rootFrameLem]
      split <;> first | rfl | exact ih _
  exact hg _ _

@[simp, rootFrameLem] theorem setLocal_frame (K : List Kont) (m : Machine) (x : String) (v : Value) :
    (pushRootK K m).setLocal x v = pushRootK K (m.setLocal x v) := by
  have hgo : ∀ (fuel : Nat) (start fid : FrameId),
      Machine.setLocal.owner (pushRootK K m) x start fid fuel =
        Machine.setLocal.owner m x start fid fuel := by
    intro fuel
    induction fuel with
    | zero => intro start fid; rfl
    | succ n ih =>
      intro start fid
      simp only [Machine.setLocal.owner, rootFrameLem]
      split
      · rfl
      · split
        · exact ih _ _
        · rfl
  simp only [Machine.setLocal, rootFrameLem, hgo]
  rfl

@[simp, rootFrameLem] theorem setGlobal_frame (K : List Kont) (m : Machine) (x : String) (v : Value) :
    (pushRootK K m).setGlobal x v = pushRootK K (m.setGlobal x v) := by
  simp only [Machine.setGlobal, pushRootK_globals, setLastMatchValue_frame]
  split <;> rfl

@[simp, rootFrameLem] theorem bindIvar_frame (K : List Kont) (m : Machine) (x : String) (v : Value) :
    bindIvar (pushRootK K m) x v = pushRootK K (bindIvar m x v) := by
  simp only [bindIvar, pushRootK_currentFrame, pushRootK_heap]
  split <;> rfl

/-- `spread` and `getGlobal` read the heap and the globals list, both of which `pushRootK` pins. -/

@[simp, rootFrameLem] theorem getGlobal_frame (K : List Kont) (m : Machine) (x : String) :
    (pushRootK K m).getGlobal x = m.getGlobal x := by
  simp only [Machine.getGlobal, pushRootK_globals, pushRootK_currentExc, Machine.lastMatchValue,
    matchFrameId_frame, pushRootK_frames]

/-- The `MatchData` splat's fold: a **list** accumulator rather than an `Array` push, so it is
`capsFold_frame`'s twin one container over. -/
@[simp, rootFrameLem] theorem capsFoldList_frame (K : List Kont) (subj : String) (bin : Bool) :
    ∀ (l : List (Option (Nat × Nat))) (acc : List Value) (m : Machine),
      l.foldl (fun (x : List Value × Machine) (sp : Option (Nat × Nat)) =>
          match sp with
          | some (a, b) => (x.1 ++ [(allocStrEnc x.2 (charSlice subj a b) bin).1],
                            (allocStrEnc x.2 (charSlice subj a b) bin).2)
          | none => (x.1 ++ [Value.nil], x.2)) (acc, pushRootK K m) =
        ((l.foldl (fun (x : List Value × Machine) (sp : Option (Nat × Nat)) =>
            match sp with
            | some (a, b) => (x.1 ++ [(allocStrEnc x.2 (charSlice subj a b) bin).1],
                              (allocStrEnc x.2 (charSlice subj a b) bin).2)
            | none => (x.1 ++ [Value.nil], x.2)) (acc, m)).1,
          pushRootK K (l.foldl (fun (x : List Value × Machine) (sp : Option (Nat × Nat)) =>
            match sp with
            | some (a, b) => (x.1 ++ [(allocStrEnc x.2 (charSlice subj a b) bin).1],
                              (allocStrEnc x.2 (charSlice subj a b) bin).2)
            | none => (x.1 ++ [Value.nil], x.2)) (acc, m)).2)
  | [], _, _ => rfl
  | sp :: rest, acc, m => by
    cases sp with
    | none =>
      simp only [List.foldl_cons]
      exact capsFoldList_frame K subj bin rest (acc ++ [Value.nil]) m
    | some p =>
      simp only [List.foldl_cons, allocStrEnc_frame]
      exact capsFoldList_frame K subj bin rest _
        (allocStrEnc m (charSlice subj p.1 p.2) bin).2

/-- The same fold at `Array.foldl`, which is where `spreadA` actually reaches it (`simp`
normalises `caps.toList.foldl` to this). -/
@[simp, rootFrameLem] theorem capsFoldListArray_frame (K : List Kont) (subj : String) (bin : Bool)
    (xs : Array (Option (Nat × Nat))) (acc : List Value) (m : Machine) :
    Array.foldl (fun (x : List Value × Machine) (sp : Option (Nat × Nat)) =>
        match sp with
        | some (a, b) => (x.1 ++ [(allocStrEnc x.2 (charSlice subj a b) bin).1],
                          (allocStrEnc x.2 (charSlice subj a b) bin).2)
        | none => (x.1 ++ [Value.nil], x.2)) (acc, pushRootK K m) xs =
      ((Array.foldl (fun (x : List Value × Machine) (sp : Option (Nat × Nat)) =>
          match sp with
          | some (a, b) => (x.1 ++ [(allocStrEnc x.2 (charSlice subj a b) bin).1],
                            (allocStrEnc x.2 (charSlice subj a b) bin).2)
          | none => (x.1 ++ [Value.nil], x.2)) (acc, m) xs).1,
        pushRootK K (Array.foldl (fun (x : List Value × Machine) (sp : Option (Nat × Nat)) =>
          match sp with
          | some (a, b) => (x.1 ++ [(allocStrEnc x.2 (charSlice subj a b) bin).1],
                            (allocStrEnc x.2 (charSlice subj a b) bin).2)
          | none => (x.1 ++ [Value.nil], x.2)) (acc, m) xs).2) := by
  simp only [← Array.foldl_toList]
  exact capsFoldList_frame K subj bin xs.toList acc m

@[simp, rootFrameLem] theorem methodFrameOf_frame (K : List Kont) (m : Machine) :
    methodFrameOf (pushRootK K m) = methodFrameOf m := rfl

@[simp, rootFrameLem] theorem returnTarget_frame (K : List Kont) (m : Machine) :
    returnTarget (pushRootK K m) = returnTarget m := rfl

@[simp, rootFrameLem] theorem blockOwner_frame (K : List Kont) (m : Machine) (p : Value) :
    blockOwner (pushRootK K m) p = blockOwner m p := rfl

@[simp, rootFrameLem] theorem doReturn_frame (K : List Kont) (m : Machine) (v : Value) :
    doReturn (pushRootK K m) v = rootFrameR K (doReturn m v) := by
  simp only [doReturn, returnTarget_frame, pushRootK_stack]
  split <;> simp only [rootFrameLem]

@[simp, rootFrameLem] theorem reifyBlock_frame (K : List Kont) (m : Machine) (ps : List Param)
    (ls : List String) (body : Expr) (lam : Bool) :
    reifyBlock (pushRootK K m) ps ls body lam =
      ((reifyBlock m ps ls body lam).1, pushRootK K (reifyBlock m ps ls body lam).2) := rfl

@[simp, rootFrameLem] theorem finishRegion_frame (K : List Kont) (m : Machine) (ens : Option Expr)
    (pending : Pending) :
    finishRegion (pushRootK K m) ens pending = pushRootK K (finishRegion m ens pending) := by
  rw [finishRegion.eq_def, finishRegion.eq_def]
  root_arms
  all_goals (cases ha : m.activeEnumerator <;> simp [pushRootK, withKont, ha])

/-- **`enterHandler`, and the one shape `simp` cannot match.** The body writes the exception
into `currentExc` and *then* writes the reference, so the machine reaching `setLocal` is a
nested record update — which Lean collapses into one flat literal whose `currentExc` field is
`some exc` rather than `?m.currentExc`. `simp` cannot unify that against `pushRootK K ?m` (it
would have to invent the structure field-wise), so the four writing arms get a `show` that
spells the pushed machine out and the framing lemmas fire on it. Recorded because it is the
shape that will recur at every helper that writes twice. -/
@[simp, rootFrameLem] theorem enterHandler_frame (K : List Kont) (m : Machine) (node : BeginNode)
    (exc : Value) (ref : Option (TargetKind × String)) (handler : Expr) :
    enterHandler (pushRootK K m) node exc ref handler =
      pushRootK K (enterHandler m node exc ref handler) := by
  cases ref with
  | none => exact withKont_frame K { m with currentExc := some exc } _ _
  | some p =>
    obtain ⟨tk, x⟩ := p
    cases tk with
    | lvar =>
      change withKont ((pushRootK K { m with currentExc := some exc }).setLocal x exc) _ _ = _
      rw [setLocal_frame, withKont_frame]
      rfl
    | gvar =>
      change withKont ((pushRootK K { m with currentExc := some exc }).setGlobal x exc) _ _ = _
      rw [setGlobal_frame, withKont_frame]
      rfl
    | ivar =>
      change withKont (bindIvar (pushRootK K { m with currentExc := some exc }) x exc) _ _ = _
      rw [bindIvar_frame, withKont_frame]
      rfl
    | const => cases ha : m.activeEnumerator <;> simp [enterHandler, pushRootK, ha]
    | cvar => exact withKont_frame K { m with currentExc := some exc } _ _

@[simp, rootFrameLem] theorem appendKwHash_frame (K : List Kont) (m : Machine) (args : List Value)
    (kw : List (Value × Value)) :
    appendKwHash (pushRootK K m) args kw =
      ((appendKwHash m args kw).1, pushRootK K (appendKwHash m args kw).2) := by
  simp only [appendKwHash, pushRootK_heap]
  split <;> rfl


@[simp, rootFrameLem] theorem matchGlobal_frame (K : List Kont) (m : Machine) (x : String) :
    matchGlobal (pushRootK K m) x = (matchGlobal m x).map (fun p => (p.1, pushRootK K p.2)) := by
  rw [matchGlobal.eq_def, matchGlobal.eq_def]
  root_arms
  -- the `$\`` / `$'` / numbered-group arms: `Option.map` has to be pushed through the `if`s
  -- and the index match before the two sides are syntactically one
  all_goals (simp only [apply_ite (Option.map (fun p : Value × Machine => (p.1, pushRootK K p.2)))]
             <;> root_arms)

@[rootFrameLem] theorem eigenclassOf_go_frame (K : List Kont) :
    ∀ (fuel : Nat) (m : Machine) (o : ObjId),
      eigenclassOf.go (pushRootK K m) o fuel =
        ((eigenclassOf.go m o fuel).1, pushRootK K (eigenclassOf.go m o fuel).2)
  | 0, _, _ => rfl
  | fuel + 1, m, o => by
    rw [eigenclassOf.go, eigenclassOf.go]
    root_simp
    (repeat' first
      | rfl
      | (simp only [rootFrameLem, eigenclassOf_go_frame K fuel]; done)
      | rw [eigenclassOf_go_frame K fuel]
      | split) <;> root_simp

@[simp, rootFrameLem] theorem eigenclassOf_frame (K : List Kont) (m : Machine) (o : ObjId) :
    eigenclassOf (pushRootK K m) o = ((eigenclassOf m o).1, pushRootK K (eigenclassOf m o).2) := by
  exact eigenclassOf_go_frame K _ m o

@[simp, rootFrameLem] theorem symOrStr_frame (K : List Kont) (m : Machine) (v : Value) :
    symOrStr (pushRootK K m) v = symOrStr m v := rfl

@[simp, rootFrameLem] theorem mixinShadow_frame (K : List Kont) (m : Machine) (recv : Value)
    (mname : String) : mixinShadow (pushRootK K m) recv mname = mixinShadow m recv mname := rfl

@[simp, rootFrameLem] theorem moduleHook_frame (K : List Kont) (m : Machine) (mo : ObjId)
    (name : String) : moduleHook (pushRootK K m) mo name = moduleHook m mo name := rfl

@[simp, rootFrameLem] theorem missNoMethod_frame (K : List Kont) (m : Machine) (recv : Value)
    (site : SendSite) (mname : String) (args : List Value) :
    missNoMethod (pushRootK K m) recv site mname args =
      rootFrameR K (missNoMethod m recv site mname args) := by
  simp only [missNoMethod, rootFrameLem]
  split <;> rfl

@[simp, rootFrameLem] theorem visError?_frame (K : List Kont) (m : Machine) (recv : Value)
    (site : SendSite) (md : MethodDef) (mname : String) :
    visError? (pushRootK K m) recv site md mname =
      (visError? m recv site md mname).map (rootFrameR K) := by
  rw [visError?.eq_def, visError?.eq_def]
  root_simp
  root_arms

@[simp, rootFrameLem] theorem cpathContainer_frame (K : List Kont) (m : Machine) (base : Value) :
    cpathContainer (pushRootK K m) base =
      (cpathContainer m base).mapError (rootFrameR K) := by
  rw [cpathContainer.eq_def, cpathContainer.eq_def]
  root_simp
  root_arms

@[simp, rootFrameLem] theorem defineAttr_frame (K : List Kont) (m : Machine) (cls : ObjId)
    (mname : String) (args : List Value) :
    defineAttr (pushRootK K m) cls mname args =
      (pushRootK K (defineAttr m cls mname args).1, (defineAttr m cls mname args).2) := by
  rw [defineAttr.eq_def, defineAttr.eq_def]
  root_simp
  -- one fold, machine in the *first* component this time
  rw [foldPairFst_frame K]
  all_goals (try root_simp)
  all_goals (try (intro m₂ p a
                  cases a <;> ((repeat' first | rfl | split) <;> root_simp)))


end RubyCore.Proof.Root
