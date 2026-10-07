import Books.TypeSoundness.Conformance.Core.Framed
import Books.Metatheory.Heap.HeapFacts

/-! An initializer really changes its receiver's shape. The old universal first-order
frame cannot describe that effect, even when no source local aliases the receiver. -/
set_option autoImplicit false
namespace Checker.Soundness
open RubyCore Checker

/-- Mask only the changed field. Payloads, classes, eigenclasses, and frozen flags survive. -/
theorem bindIvar_data (m : Machine) (x : String) (v : Value) (k : ObjId) :
    { (Interp.bindIvar m x v).heap.get k with ivars := [], revision := 0 } =
      { m.heap.get k with ivars := [], revision := 0 } := by
  unfold Interp.bindIvar
  split
  · rename_i o hs
    simp only [Heap.get, Heap.set]
    by_cases hk : k = o
    · subst k
      by_cases ho : o < m.heap.objs.size
      · rw [Proof.objs_getD_set!_self _ _ _ ho]
      · rw [Proof.objs_getD_set!_oob _ _ _ ho]
    · rw [Proof.objs_getD_set!_ne _ _ _ _ hk]
  · rfl

theorem bindIvar_size (m : Machine) (x : String) (v : Value) :
    (Interp.bindIvar m x v).heap.objs.size = m.heap.objs.size := by
  unfold Interp.bindIvar
  split <;> simp [Heap.set]

@[simp] theorem bindIvar_frames (m : Machine) (x : String) (v : Value) :
    (Interp.bindIvar m x v).frames = m.frames := by
  unfold Interp.bindIvar; split <;> rfl

@[simp] theorem bindIvar_stack (m : Machine) (x : String) (v : Value) :
    (Interp.bindIvar m x v).stack = m.stack := by
  unfold Interp.bindIvar; split <;> rfl

@[simp] theorem bindIvar_preludeMode (m : Machine) (x : String) (v : Value) :
    (Interp.bindIvar m x v).preludeMode = m.preludeMode := by
  unfold Interp.bindIvar; split <;> rfl

@[simp] theorem bindIvar_currentFrame (m : Machine) (x : String) (v : Value) :
    (Interp.bindIvar m x v).currentFrame = m.currentFrame := by
  simp only [Machine.currentFrame, bindIvar_frames, bindIvar_stack]

theorem FramePres.bindIvar (m : Machine) (x : String) (v : Value) :
    FramePres m (Interp.bindIvar m x v) := .of_eq (by simp) (by simp)

theorem bindIvar_ivarOnly (m : Machine) (x : String) (v : Value) :
    Proof.IvarOnly m.heap (Interp.bindIvar m x v).heap :=
  ⟨bindIvar_size m x v,
    fun k => by simpa only using congrArg Object.klass (bindIvar_data m x v k),
    fun k => by simpa only using congrArg Object.eigen (bindIvar_data m x v k),
    fun k => by simpa only using congrArg Object.payload (bindIvar_data m x v k),
    fun k => by simpa only using congrArg Object.frozen (bindIvar_data m x v k)⟩

theorem bindIvar_get_other {m : Machine} {o k : ObjId} {x : String} {v : Value}
    (hs : m.currentFrame.self = .ref o) (hk : k ≠ o) :
    (Interp.bindIvar m x v).heap.get k = m.heap.get k := by
  simp only [Interp.bindIvar, hs, Heap.get, Heap.set]
  exact Proof.objs_getD_set!_ne _ _ _ _ hk

theorem bindIvar_get_self {m : Machine} {o : ObjId} {x : String} {v : Value}
    (hs : m.currentFrame.self = .ref o) (ho : o < m.heap.objs.size) :
    (Interp.bindIvar m x v).heap.get o =
      { m.heap.get o with
        ivars := if (m.heap.get o).ivars.any (·.1 == x) then
          (m.heap.get o).ivars.map (fun (y, w) => (y, if y == x then v else w))
          else (x, v) :: (m.heap.get o).ivars,
        revision := (m.heap.get o).revision + 1 } := by
  simp only [Interp.bindIvar, hs, Heap.get, Heap.set]
  exact Proof.objs_getD_set!_self _ _ _ ho

private theorem ivar_write_read (xs : List (String × Value)) (x y : String) (v : Value) :
    (match (if xs.any (·.1 == x) then
      xs.map (fun (key, old) => (key, if key == x then v else old))
      else (x, v) :: xs).find? (·.1 == y) with
      | some (_, w) => w | none => .nil) =
      if y == x then v else
        (match xs.find? (·.1 == y) with | some (_, w) => w | none => .nil) := by
  by_cases ha : xs.any (·.1 == x) = true
  · simp only [ha, if_true, List.find?_map, Function.comp_def]
    cases hf : xs.find? (·.1 == y) with
    | none =>
      by_cases hy : y = x
      · subst y
        obtain ⟨p, hp, hx⟩ := List.any_eq_true.mp ha
        exact False.elim ((List.find?_eq_none.mp hf p hp) hx)
      · simp [hy]
    | some p =>
      have hpy := List.find?_some hf
      have hy : p.1 = y := by simpa using hpy
      simp [hy]
  · simp only [ha, if_false, List.find?_cons]
    by_cases hy : y = x
    · subst y; simp
    · simp [hy, Ne.symm hy]

theorem ivarOf_bindIvar_self {m : Machine} {o : ObjId} {x : String} {v : Value}
    (hs : m.currentFrame.self = .ref o) (ho : o < m.heap.objs.size) :
    ivarOf (Interp.bindIvar m x v).heap (.ref o) x = v := by
  simp only [ivarOf, bindIvar_get_self hs ho]
  have hr := ivar_write_read (m.heap.get o).ivars x x v
  simp only [beq_self_eq_true, if_true] at hr
  (repeat' split at hr) <;> simp_all only

theorem ivarOf_bindIvar_other {m : Machine} {o : ObjId} {x : String} {v w : Value}
    (hs : m.currentFrame.self = .ref o) (hw : w ≠ .ref o) :
    ivarOf (Interp.bindIvar m x v).heap w = ivarOf m.heap w := by
  funext y
  cases w <;> try rfl
  rename_i k
  simp only [ivarOf, bindIvar_get_other (k := k) hs (by intro h; subst k; exact hw rfl)]

theorem ivarOf_bindIvar_ne {m : Machine} {o : ObjId} {x y : String} {v : Value}
    (hs : m.currentFrame.self = .ref o) (ho : o < m.heap.objs.size) (hne : y ≠ x) :
    ivarOf (Interp.bindIvar m x v).heap (.ref o) y = ivarOf m.heap (.ref o) y := by
  simp only [ivarOf, bindIvar_get_self hs ho]
  have hr := ivar_write_read (m.heap.get o).ivars x y v
  simp only [beq_eq_false_iff_ne.mpr hne, Bool.false_eq_true, if_false] at hr
  (repeat' split at hr) <;> simp_all only

theorem getLocal_bindIvar (m : Machine) (x : String) (v : Value) (y : String) :
    (Interp.bindIvar m x v).getLocal y = m.getLocal y := by
  have hg : ∀ fuel fid, Machine.getLocal.go (Interp.bindIvar m x v) y fid fuel =
      Machine.getLocal.go m y fid fuel := by
    intro fuel
    induction fuel with
    | zero => intro fid; rfl
    | succ f ih =>
      intro fid
      simp only [Machine.getLocal.go, localFrameId_frames_eq (bindIvar_frames m x v), bindIvar_frames]
      split
      · rfl
      · split
        · exact ih _
        · rfl
  simp only [Machine.getLocal, bindIvar_stack, bindIvar_frames, hg]

theorem env_bindIvar {m : Machine} {Γ : Env} {x : String} {v : Value}
    (he : EnvOk Γ m)
    (hkeep : ∀ y τ, envGet? Γ y = some τ →
      denM (stripAlias τ) (Interp.bindIvar m x v) (m.getLocal y)) :
    EnvOk Γ (Interp.bindIvar m x v) := by
  refine ⟨?_, ?_⟩
  · intro y τ hy
    refine ⟨by rw [getLocal_bindIvar]; exact hkeep y τ hy, ?_⟩
    intro z σ hz
    simp only [getLocal_bindIvar]
    exact (he.1 y τ hy).2 z σ hz
  · intro y hy
    rw [getLocal_bindIvar]; exact he.2 y hy

/-- This is the real successful assignment transition, not a replacement execution model. -/
theorem stepFn_ivarWrite {m : Machine} {o : ObjId} {x : String} {v : Value} {rest : List Kont}
    (hs : m.currentFrame.self = .ref o) (hf : (m.heap.get o).frozen = false) :
    Interp.stepFn { m with ctl := .value v, kont := .asgnK .ivar x :: rest } =
      .next { Interp.bindIvar m x v with ctl := .value v, kont := rest } := by
  simp only [Interp.stepFn, Interp.applyKont]
  change (match m.currentFrame.self with
    | .ref o => _
    | _ => _) = _
  rw [hs]
  simp only [hf, Bool.false_eq_true, ↓reduceIte]
  simp only [Interp.bindIvar, Interp.withCtl]
  change (StepResult.next _) = _
  rw [show ({ m with ctl := .value v, kont := rest } : Machine).currentFrame.self = .ref o from hs]
  rw [hs]

/-- No tactic can prove the existing `Framed` contract for this successful write.
The forbidden old type is first-order but observes the receiver's previous nil slot. -/
theorem nil_ivar_write_not_framed {m : Machine} {o : ObjId} {x cn : String}
    (hs : m.currentFrame.self = .ref o) (ho : o < m.heap.objs.size)
    (hc : isExactInst m.heap (.ref o) cn = true)
    (hn : ivarOf m.heap (.ref o) x = .nil) :
    ¬ Framed m (Interp.bindIvar m x (.int 1)) := by
  intro hf
  have hd : denM (.inst cn (.ivarCons x .nilT .ivar0)) m (.ref o) := by
    simp [denM, denSpineFrom, hc, hn, isNilV]
  have hout := hf.firstOrder (.inst cn (.ivarCons x .nilT .ivar0)) rfl (.ref o) hd
  have hv := ivarOf_bindIvar_self (x := x) (v := .int 1) hs ho
  simp only [denM, denSpineFrom, List.not_mem_nil, false_or, and_true] at hout
  have hnil := hout.2
  rw [hv] at hnil
  cases hnil

#print axioms ivarOf_bindIvar_self
#print axioms bindIvar_ivarOnly
#print axioms stepFn_ivarWrite
#print axioms nil_ivar_write_not_framed
end Checker.Soundness
