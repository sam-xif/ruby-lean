import Books.TypeSoundness.Rules.Closure.Literal
import Books.TypeSoundness.Judgment.Run

/-! An attached literal block (`recv.m { ... }`) reifies with a live break scope, reserves
a dead frame and leaves `blockCallK` below the call. The call runs above that
continuation; returning through it only retires the scope. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

/-- The callee's view: the Proc, the dead frame and the live scope, with no continuation. -/
def attMachine (m : Machine) (ps : List RubyCore.Param) (ls : List String)
    (body : RubyCore.Expr) : Machine :=
  let base : Machine := { m with
    heap := pushHeap m.heap (litObj m ps ls body false)
    liveBreakScopes := m.frames.size :: m.liveBreakScopes
    kont := [] }
  pushDead base m.currentFrame

theorem finishSend_attached (m : Machine) (recv : Value) (site : SendSite) (name : String)
    (hn : (name == "lambda" || name == "proc") = false) (hk : m.kont = [])
    (hq : RootClean m) (ps : List RubyCore.Param) (ls : List String) (body : RubyCore.Expr) :
    Interp.finishSend m recv site name [] (.lit ps ls body) =
      Interp.invoke (Proof.pushRootK [.blockCallK m.frames.size] (attMachine m ps ls body))
        recv site name [] (some (.ref m.heap.objs.size)) [] := by
  have hget : (reifiedMachine m ps ls body false).heap.get m.heap.objs.size =
      { klass := Boot.procId, payload := .proc (reifiedClosure m ps ls body false) } := by
    simp [reifiedMachine, pushHeap_get_self]
  have hn' : name ≠ "lambda" ∧ name ≠ "proc" := by
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hn; exact hn
  have hl1 : (name == "lambda") = false := beq_eq_false_iff_ne.mpr hn'.1
  have hl2 : (name == "proc") = false := beq_eq_false_iff_ne.mpr hn'.2
  rw [Proof.pushRootK_quiescent _ (attMachine m ps ls body) hq.1 hq.2]
  simp only [Interp.finishSend, hl1, hl2, Bool.and_false, Bool.false_and, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte]
  simp only [Interp.reifyCallBlock, reifyBlock_eq, hget,
    reifiedMachine_frames, lit_heap, hn, Bool.and_false, Bool.false_and, Bool.false_eq_true,
    ↓reduceIte]
  simp only [attMachine, pushDead, hk, reifiedMachine, List.nil_append]
  rfl

/-- The same call when an installed user method shadows any Kernel selector. -/
theorem finishSend_attached_shadowed (m : Machine) (recv : Value) (site : SendSite) (name : String)
    {owner : ObjId} {md : MethodDef}
    (hl : Interp.methodOn m.heap (classOf m.heap recv) name = some (owner, md))
    (hb : md.builtin = none) (hu : md.undefined = false) (hk : m.kont = [])
    (hq : RootClean m) (ps : List RubyCore.Param) (ls : List String) (body : RubyCore.Expr) :
    Interp.finishSend m recv site name [] (.lit ps ls body) =
      Interp.invoke (Proof.pushRootK [.blockCallK m.frames.size] (attMachine m ps ls body))
        recv site name [] (some (.ref m.heap.objs.size)) [] := by
  have hget : (reifiedMachine m ps ls body false).heap.get m.heap.objs.size =
      { klass := Boot.procId, payload := .proc (reifiedClosure m ps ls body false) } := by
    simp [reifiedMachine, pushHeap_get_self]
  rw [Proof.pushRootK_quiescent _ (attMachine m ps ls body) hq.1 hq.2]
  simp only [Interp.finishSend, hl, hb, hu, Option.isNone_none, Bool.not_false, Bool.and_true,
    Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  simp only [Interp.reifyCallBlock, reifyBlock_eq, hget,
    reifiedMachine_frames, lit_heap]
  simp only [attMachine, pushDead, hk, reifiedMachine, List.nil_append]
  rfl

/-- The callee machine with the pushed Proc and live scope, before the dead frame. -/
def attBase (m : Machine) (ps : List RubyCore.Param) (ls : List String)
    (body : RubyCore.Expr) : Machine := { m with
  heap := pushHeap m.heap (litObj m ps ls body false)
  liveBreakScopes := m.frames.size :: m.liveBreakScopes
  kont := [] }

theorem attMachine_eq (m : Machine) (ps : List RubyCore.Param) (ls : List String)
    (body : RubyCore.Expr) : attMachine m ps ls body = pushDead (attBase m ps ls body) m.currentFrame :=
  rfl

theorem att_ext {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} (hm : StateOk κ Γ I m)
    (ps : List RubyCore.Param) (ls : List String) (body : RubyCore.Expr) :
    Ext m (attBase m ps ls body) :=
  have he := ext_push (m := m) (litObj m ps ls body false) hm.sat hm.core.basicSelf
    (by intro c h; cases h) rfl rfl hm.core.procBasic
  ⟨he.frames, he.stack, he.size, he.get, he.payload, he.ancestors, he.freshIvars,
    he.freshBasic, he.chains, he.rootClean⟩

theorem att_state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} (hm : StateOk κ Γ I m)
    (ps : List RubyCore.Param) (ls : List String) (body : RubyCore.Expr) :
    StateOk κ Γ I (attMachine m ps ls body) :=
  StateOk_pushDead (StateOk_ext hm (att_ext hm ps ls body)
    (stringPayloadOk_push hm.stringPayload (by simp [litObj, Boot.procId, Boot.stringId]))
    (arrayPayloadOk_push hm.arrayPayload (by intro xs h; cases h))
    (hashPayloadOk_push hm.hashPayload (by intro xs h; cases h)) rfl) _

theorem att_framed {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} (hm : StateOk κ Γ I m)
    (ps : List RubyCore.Param) (ls : List String) (body : RubyCore.Expr) :
    Framed m (attMachine m ps ls body) :=
  (Framed.of_ext (att_ext hm ps ls body)).trans
    (Framed_pushDead (m := attBase m ps ls body) hm.frameInRange _)

theorem att_payload (m : Machine) (ps : List RubyCore.Param) (ls : List String)
    (body : RubyCore.Expr) :
    (attMachine m ps ls body).heap.get m.heap.objs.size = litObj m ps ls body false := by
  simp [attMachine, pushDead, pushHeap_get_self]

/-- Returning through `blockCallK` retires the scope and keeps the answer contract. -/
theorem blockCallK_answer {origin m n : Machine} {Γ : Env} {τ I : Ty} {κ : Ctx} {a : Answer}
    (s : FrameId) (hτ : FirstOrder τ = true) (hf : Framed origin m)
    (hr : ResultOk m Γ τ a n κ I) :
    RunSpec origin (deliverA a n [.blockCallK s]) Γ τ κ I := by
  let n' : Machine := { n with liveBreakScopes := n.liveBreakScopes.filter (fun t => t != s) }
  have hfr : Framed n n' := Framed.of_heap_stack rfl rfl (.of_eq rfl rfl)
  cases a with
  | val v =>
    apply RunSpec.step (by rfl) (step_blockCallK { n with kont := [.blockCallK s] } s v rfl)
    change RunSpec origin (deliverA (.val v) n' []) Γ τ κ I
    apply RunSpec.answer
    refine ⟨hf.trans (hr.1.trans hfr), ?_, fun _ hv => ?_⟩
    · exact (denM_heap_only (m₁ := n) (m₂ := n') hτ rfl).mp (show denM τ n v from hr.2.1)
    · cases hv
      exact StateOk_ext (hr.2.2 v rfl) ⟨rfl, rfl, Nat.le_refl _, fun _ _ => rfl, fun _ => rfl,
        fun _ => rfl, fun o ho => by rw [get_oob _ ho]; rfl,
        fun o ho k hk => by rw [classOf_oob _ ho]; exact hk, id, id⟩
        (hr.2.2 v rfl).stringPayload (hr.2.2 v rfl).arrayPayload (hr.2.2 v rfl).hashPayload rfl
  | esc j =>
    obtain ⟨exc, rfl, _⟩ := hr.2.1.only_raise
    apply RunSpec.step (by rfl) (show Interp.stepFn _ = .next (deliverA (.esc (.raiseJ exc)) n' []) from rfl)
    exact RunSpec.answer ⟨hf.trans (hr.1.trans hfr), hr.2.1, fun _ hv => by cases hv⟩

#print axioms finishSend_attached
#print axioms att_state
#print axioms blockCallK_answer
end Checker.Soundness.Typed
