import RubyCore.Interp

/-! A continuation frame follows the root execution when an Enumerator saves
it. Fiber executions have their own continuation and must not acquire the
root's tail. The active-stack-only action is refuted in DriftControls. -/
namespace RubyCore.Proof

def frameExecution (K : List Kont) (e : Execution) : Execution :=
  { e with kont := if e.activeEnumerator.isNone then e.kont ++ K else e.kont }

def frameEnumState (K : List Kont) (s : EnumState) : EnumState :=
  { s with
    caller := s.caller.map (frameExecution K)
    suspended := s.suspended.map (frameExecution K) }

def pushRootK (K : List Kont) (m : Machine) : Machine :=
  { m with
    kont := if m.activeEnumerator.isNone then m.kont ++ K else m.kont
    enumerators := m.enumerators.map (fun (o, s) => (o, frameEnumState K s)) }

def rootFrameR (K : List Kont) : StepResult → StepResult
  | .next m => .next (pushRootK K m)
  | r => r

def holdsHash (o : ObjId) : Kont → Bool
  | .iterK _ _ _ (.hashEach h ..) _ _ _ => h == o
  | _ => false

/-- An appended context must not introduce a native Hash-iteration lock. -/
def HashLockFree (K : List Kont) : Prop := ∀ o, K.any (holdsHash o) = false

theorem hashIterationActive_rootFrame (K : List Kont) (hK : HashLockFree K)
    (m : Machine) (o : ObjId) :
    (pushRootK K m).hashIterationActive o = m.hashIterationActive o := by
  have hex (e : Execution) : (frameExecution K e).kont.any (holdsHash o) =
      e.kont.any (holdsHash o) := by
    simp only [frameExecution]
    split <;> simp [List.any_append, hK o]
  have hkont : (if m.activeEnumerator.isNone then m.kont ++ K else m.kont).any (holdsHash o) =
      m.kont.any (holdsHash o) := by
    split <;> simp [List.any_append, hK o]
  change (m.abandonedHashIterations.contains o ||
      (pushRootK K m).kont.any (holdsHash o) ||
      (pushRootK K m).enumerators.any (fun (_, s) =>
        s.suspended.any (fun e => e.kont.any (holdsHash o)) ||
        s.caller.any (fun e => e.kont.any (holdsHash o)))) =
    (m.abandonedHashIterations.contains o || m.kont.any (holdsHash o) ||
      m.enumerators.any (fun (_, s) =>
        s.suspended.any (fun e => e.kont.any (holdsHash o)) ||
        s.caller.any (fun e => e.kont.any (holdsHash o))))
  simp only [pushRootK, hkont, List.any_map, frameEnumState, Option.any_map, Function.comp_def, hex]

theorem pushRootK_quiescent (K : List Kont) (m : Machine)
    (ha : m.activeEnumerator = none) (he : m.enumerators = []) :
    pushRootK K m = { m with kont := m.kont ++ K } := by
  simp [pushRootK, ha, he]

@[simp] theorem frameEnumState_default (K : List Kont) :
    frameEnumState K {} = ({} : EnumState) := rfl

theorem executionOf_rootFrame (K : List Kont) (m : Machine) :
    Interp.executionOf (pushRootK K m) = frameExecution K (Interp.executionOf m) := rfl

theorem restoreExecution_rootFrame (K : List Kont) (m : Machine) (e : Execution) :
    Interp.restoreExecution (pushRootK K m) (frameExecution K e) =
      pushRootK K (Interp.restoreExecution m e) := rfl

private theorem find_state_map (K : List Kont) (o : ObjId) (ss : List (ObjId × EnumState)) :
    (ss.map (fun (j, s) => (j, frameEnumState K s))).find? (·.1 == o) =
      (ss.find? (·.1 == o)).map (fun (j, s) => (j, frameEnumState K s)) := by
  induction ss with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.find?_cons]
    split <;> simp_all

theorem enumState_rootFrame (K : List Kont) (m : Machine) (o : ObjId) :
    Interp.enumState (pushRootK K m) o = frameEnumState K (Interp.enumState m o) := by
  simp only [Interp.enumState, pushRootK, find_state_map]
  cases m.enumerators.find? (·.1 == o) <;> rfl

theorem setEnumState_rootFrame (K : List Kont) (m : Machine) (o : ObjId) (s : EnumState) :
    Interp.setEnumState (pushRootK K m) o (frameEnumState K s) =
      pushRootK K (Interp.setEnumState m o s) := by
  simp only [Interp.setEnumState, pushRootK, List.map_cons, List.filter_map, Function.comp_def]

theorem withKont_rootFrame (K : List Kont) (m : Machine) (c : Ctl) (k : Kont) :
    Interp.withKont (pushRootK K m) c k = pushRootK K (Interp.withKont m c k) := by
  cases ha : m.activeEnumerator <;> simp [Interp.withKont, pushRootK, ha]

theorem newStop_rootFrame (K : List Kont) (m : Machine) (o : Option ObjId)
    (result message : Value) :
    Interp.newStop (pushRootK K m) o result message =
      rootFrameR K (Interp.newStop m o result message) := by
  cases ha : m.activeEnumerator <;> simp [Interp.newStop, pushRootK, rootFrameR, ha]

theorem enumPack_rootFrame (K : List Kont) (m : Machine) (args : List Value) (values : Bool) :
    Interp.enumPack (pushRootK K m) args values =
      ((Interp.enumPack m args values).1, pushRootK K (Interp.enumPack m args values).2) := by
  cases values <;> cases args with
  | nil => rfl
  | cons v rest => cases rest <;> rfl

@[simp] theorem pushRootK_frames (K : List Kont) (m : Machine) :
    (pushRootK K m).frames = m.frames := rfl
@[simp] theorem pushRootK_stack (K : List Kont) (m : Machine) :
    (pushRootK K m).stack = m.stack := rfl

theorem matchFrameOwner_rootFrame (K : List Kont) (m : Machine) :
    ∀ (fuel : Nat) (fid : FrameId),
      Machine.matchFrameOwner (pushRootK K m) fid fuel = Machine.matchFrameOwner m fid fuel := by
  intro fuel
  induction fuel with
  | zero => intro fid; rfl
  | succ n ih =>
    intro fid
    simp only [Machine.matchFrameOwner, pushRootK_frames]
    split
    · exact ih _
    · rfl

theorem matchFrameId_go_rootFrame (K : List Kont) (m : Machine) :
    ∀ (fuel : Nat) (l : List FrameId),
      Machine.matchFrameId.go (pushRootK K m) l fuel = Machine.matchFrameId.go m l fuel := by
  intro fuel
  induction fuel with
  | zero => intro l; cases l <;> rfl
  | succ n ih =>
    intro l
    cases l with
    | nil => rfl
    | cons fid rest =>
      simp only [Machine.matchFrameId.go, pushRootK_frames]
      split
      · split
        · rfl
        · exact ih _
      · split
        · split
          · exact matchFrameOwner_rootFrame K m n _
          · exact ih _
        · rfl

theorem matchFrameId_rootFrame (K : List Kont) (m : Machine) :
    (pushRootK K m).matchFrameId = m.matchFrameId := by
  simp only [Machine.matchFrameId, pushRootK_stack]
  exact matchFrameId_go_rootFrame K m _ _

theorem enumStop_rootFrame (K : List Kont) (m : Machine) (original : Value) :
    Interp.enumStop (pushRootK K m) original =
      rootFrameR K (Interp.enumStop m original) := by
  cases ha : m.activeEnumerator <;> cases original <;>
    simp only [Interp.enumStop, pushRootK]
  all_goals (repeat' split) <;>
    simp_all [rootFrameR, pushRootK, Interp.newStop, Interp.withKont, Builtins.allocStrEnc]

theorem enumNext_rootFrame (K : List Kont) (m : Machine) (o : ObjId) (peek values : Bool) :
    Interp.enumNext (pushRootK K m) o peek values =
      rootFrameR K (Interp.enumNext m o peek values) := by
  unfold Interp.enumNext
  simp only [matchFrameId_rootFrame]
  rw [enumState_rootFrame]
  cases hc : (Interp.enumState m o).caller with
  | some caller => simp [frameEnumState, hc, rootFrameR]
  | none =>
    simp only [frameEnumState, hc, Option.map_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    cases hf : (Interp.enumState m o).finished with
    | some exc => simp only [hf]; exact enumStop_rootFrame K m exc
    | none =>
      simp only [hf]
      cases hl : (Interp.enumState m o).lookahead with
      | some args =>
        simp only [hl]
        cases ha : m.activeEnumerator <;> cases values <;> cases args with
        | nil => simp [Interp.enumPack, Interp.setEnumState, rootFrameR, pushRootK,
            frameEnumState, ha, hc, hf, hl, List.filter_map, Function.comp_def, Builtins.allocArr]
        | cons v rest => cases rest <;>
            simp [Interp.enumPack, Interp.setEnumState, rootFrameR, pushRootK,
              frameEnumState, ha, hc, hf, hl, List.filter_map, Function.comp_def, Builtins.allocArr]
      | none =>
        simp only [hl, executionOf_rootFrame]
        cases hs : (Interp.enumState m o).suspended with
        | some fiber =>
          cases ha : m.activeEnumerator <;> cases he : fiber.activeEnumerator <;>
            simp [hs, Interp.setEnumState, Interp.restoreExecution, rootFrameR, pushRootK,
              frameEnumState, frameExecution, ha, he, hc, hf, hl, List.filter_map, Function.comp_def, Builtins.allocArr]
        | none =>
          cases ha : m.activeEnumerator <;>
            simp [hs, Interp.setEnumState, Interp.enumQueue, rootFrameR, pushRootK,
              frameEnumState, frameExecution, ha, hc, hf, hl, List.filter_map, Function.comp_def, Builtins.allocArr]

theorem suspendEnumerator_rootFrame (K : List Kont) (m : Machine) (o : ObjId)
    (args : List Value) :
    Interp.suspendEnumerator (pushRootK K m) o args =
      rootFrameR K (Interp.suspendEnumerator m o args) := by
  unfold Interp.suspendEnumerator
  rw [enumState_rootFrame]
  cases hc : (Interp.enumState m o).caller with
  | none => simp [frameEnumState, hc, rootFrameR]
  | some caller =>
    simp only [frameEnumState, hc, Option.map_some]
    cases ha : m.activeEnumerator <;> cases he : caller.activeEnumerator <;>
      cases hv : (Interp.enumState m o).values <;> cases args with
    | nil =>
      simp [Interp.enumPack, Interp.setEnumState, Interp.restoreExecution, Interp.executionOf,
        rootFrameR, pushRootK, frameEnumState, frameExecution, ha, he, hc, hv,
        List.filter_map, Function.comp_def, Builtins.allocArr]
    | cons v rest => cases rest <;>
      simp [Interp.enumPack, Interp.setEnumState, Interp.restoreExecution, Interp.executionOf,
        rootFrameR, pushRootK, frameEnumState, frameExecution, ha, he, hc, hv,
        List.filter_map, Function.comp_def, Builtins.allocArr]

theorem finishStop_rootFrame (K : List Kont) (m : Machine) (owner : Option ObjId)
    (exc result : Value) :
    Interp.finishStop (pushRootK K m) owner exc result =
      rootFrameR K (Interp.finishStop m owner exc result) := by
  unfold Interp.finishStop
  cases exc <;> simp only [pushRootK]
  all_goals try rfl
  rename_i o
  cases ha : m.activeEnumerator
  all_goals split
  all_goals try (simp [Interp.raiseFrozen, Interp.withKont, pushRootK, rootFrameR, ha])
  all_goals cases owner
  all_goals try (simp [Interp.withCtl, pushRootK, rootFrameR, ha])
  all_goals
    rename_i e
    simp only [Interp.enumState, find_state_map]
    cases hs : m.enumerators.find? (·.1 == e) with
    | none => simp [hs, rootFrameR]
    | some entry =>
      cases hc : entry.2.caller with
      | none => simp [hc, frameEnumState, rootFrameR]
      | some caller =>
        cases he : caller.activeEnumerator <;>
          simp [Interp.setEnumState, Interp.restoreExecution, Interp.withCtl,
            rootFrameR, pushRootK, frameEnumState, frameExecution, ha, he, hc,
            List.filter_map, Function.comp_def]

#print axioms enumNext_rootFrame
#print axioms suspendEnumerator_rootFrame
#print axioms finishStop_rootFrame

end RubyCore.Proof
