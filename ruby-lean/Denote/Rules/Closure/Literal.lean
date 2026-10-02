import Denote.Sem.Closure.Value
import Denote.Sem.Closure.DeadState
import Denote.Sem.Closure.LocalFacts
import Denote.Judgment.Context

/-! Actual lambda/proc literal execution. The absence premise is consumed at lookup,
so a user-defined Kernel selector cannot silently create a certified closure. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

private theorem literal_unshadowed {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) {name : String} (hn : name ∈ shadowableNames)
    (hf : nameFreeN κ name = true) :
    (match Interp.methodOn m.heap (classOf m.heap m.currentFrame.self) name with
      | some (_, md) => md.builtin.isNone && !md.undefined
      | none => false) = false := by
  cases hl : Interp.methodOn m.heap (classOf m.heap m.currentFrame.self) name with
  | none => rfl
  | some p =>
    obtain ⟨owner, md⟩ := p
    have hh := hm.nameFree name hn _ (List.mem_cons_self) owner md hl
    rcases hh with hb | hu | hn
    · cases he : md.builtin <;> simp_all
    · simp [hu]
    · rw [hf] at hn; cases hn

/-- The literal's closure: reified at the current frame, with its own break scope. -/
def litClosure (m : Machine) (ps : List RubyCore.Param) (ls : List String)
    (body : RubyCore.Expr) (lam : Bool) : Closure :=
  { reifiedClosure m ps ls body lam with breakScope := some m.frames.size }

def litObj (m : Machine) (ps : List RubyCore.Param) (ls : List String)
    (body : RubyCore.Expr) (lam : Bool) : Object :=
  { klass := Boot.procId, payload := .proc (litClosure m ps ls body lam), revision := 1 }

/-- After the literal's blockCallK: the fresh Proc, a dead copy of the current frame
reserving the break scope, and the scope no longer live. -/
def litMachine (m : Machine) (ps : List RubyCore.Param) (ls : List String)
    (body : RubyCore.Expr) (lam : Bool) : Machine :=
  let base : Machine := { m with
    heap := pushHeap m.heap (litObj m ps ls body lam)
    liveBreakScopes := m.liveBreakScopes.filter (fun s => s != m.frames.size) }
  pushDead base m.currentFrame

/-- The first step: lookup confirms the Kernel selector, then the literal reifies. -/
theorem closure_literal_step₁ {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hm : StateOk κ Γ I m) (lam : Bool)
    (hf : nameFreeN κ (if lam then "lambda" else "proc") = true)
    (ps : List Ratchet.Param) (ls : List String) (body : Ratchet.Expr) :
    let m₀ := evalFrom m (.send none (if lam then "lambda" else "proc") [] (some (.block ps ls body)))
    Interp.stepFn m₀ = .next (Interp.withCtl
      (Interp.reifyCallBlock m₀ (toRubyParams ps) ls (toRuby body) lam).2
      (.value (Interp.reifyCallBlock m₀ (toRubyParams ps) ls (toRuby body) lam).1)) := by
  intro m₀
  have hheap : m₀.heap = m.heap := rfl
  have hs := literal_unshadowed hm (name := if lam then "lambda" else "proc")
    (by cases lam <;> simp [shadowableNames]) hf
  cases hl : Interp.methodOn m.heap (classOf m.heap m.currentFrame.self)
      (if lam then "lambda" else "proc") with
  | none =>
    cases lam <;>
      change Interp.finishSend _ m.currentFrame.self .implicit _ [] (.lit _ _ _) [] = _
    all_goals
      simp only [Bool.false_eq_true, ↓reduceIte] at hl
      simp only [Interp.finishSend, evalFrom, Bool.false_eq_true, ↓reduceIte, hheap, hl]
      simp
  | some p =>
    obtain ⟨owner, md⟩ := p
    have hb : (md.builtin.isNone && !md.undefined) = false := by simpa only [hl] using hs
    cases lam <;>
      change Interp.finishSend _ m.currentFrame.self .implicit _ [] (.lit _ _ _) [] = _
    all_goals
      simp only [Bool.false_eq_true, ↓reduceIte] at hl
      simp only [Interp.finishSend, evalFrom, Bool.false_eq_true, ↓reduceIte, hheap, hl, hb]
      simp

@[simp] theorem reifiedMachine_frames (m : Machine) (ps : List RubyCore.Param) (ls : List String)
    (body : RubyCore.Expr) (lam : Bool) : (reifiedMachine m ps ls body lam).frames = m.frames := rfl

theorem push_set_size {α : Type} (a : Array α) (x y : α) : (a.push x).set! a.size y = a.push y := by
  apply Array.ext
  · simp [Array.set!]
  · intro i h1 h2
    simp only [Array.set!, Array.size_push] at h1 h2 ⊢
    rw [Array.getElem_setIfInBounds (by simpa using h2), Array.getElem_push, Array.getElem_push]
    by_cases hi : i = a.size
    · subst hi; simp
    · have : i < a.size := by omega
      simp [Ne.symm hi, this]

/-- The literal's Proc write after allocation is a single push of the final object. -/
theorem lit_heap (m : Machine) (ps : List RubyCore.Param) (ls : List String)
    (body : RubyCore.Expr) (lam : Bool) :
    (reifiedMachine m ps ls body lam).heap.set m.heap.objs.size
      { klass := Boot.procId,
        payload := .proc { reifiedClosure m ps ls body lam with breakScope := some m.frames.size } } =
      pushHeap m.heap (litObj m ps ls body lam) := by
  have hg : (reifiedMachine m ps ls body lam).heap.get m.heap.objs.size =
      { klass := Boot.procId, payload := .proc (reifiedClosure m ps ls body lam) } := by
    simp [reifiedMachine, pushHeap_get_self]
  unfold Heap.set
  rw [hg]
  simp only [reifiedMachine, pushHeap]
  rw [push_set_size]
  rfl

theorem step_blockCallK (X : Machine) (s : FrameId) (v : Value) (hk : X.kont = [.blockCallK s]) :
    Interp.stepFn (Interp.withCtl X (.value v)) =
      .next (Interp.withCtl { X with
        kont := []
        liveBreakScopes := X.liveBreakScopes.filter (fun t => t != s) } (.value v)) := by
  cases X; simp only at hk; subst hk; rfl

theorem closure_literal_step₂ (m : Machine) (lam : Bool)
    (ps : List Ratchet.Param) (ls : List String) (body : Ratchet.Expr) :
    let m₀ := evalFrom m (.send none (if lam then "lambda" else "proc") [] (some (.block ps ls body)))
    Interp.stepFn (Interp.withCtl
      (Interp.reifyCallBlock m₀ (toRubyParams ps) ls (toRuby body) lam).2
      (.value (Interp.reifyCallBlock m₀ (toRubyParams ps) ls (toRuby body) lam).1)) =
    .next (deliverA (.val (.ref m.heap.objs.size)) (litMachine m (toRubyParams ps) ls (toRuby body) lam) []) := by
  intro m₀
  have hget : (reifiedMachine m₀ (toRubyParams ps) ls (toRuby body) lam).heap.get m₀.heap.objs.size =
      { klass := Boot.procId, payload := .proc (reifiedClosure m₀ (toRubyParams ps) ls (toRuby body) lam) } := by
    simp [reifiedMachine, pushHeap_get_self]
  simp only [Interp.reifyCallBlock, reifyBlock_eq, hget, reifiedMachine_frames, lit_heap]
  rw [step_blockCallK _ _ _ rfl]
  simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- The heap/scope half of the literal: one allocation, liveness bookkeeping only. -/
def litBase (m : Machine) (ps : List RubyCore.Param) (ls : List String)
    (body : RubyCore.Expr) (lam : Bool) : Machine := { m with
  heap := pushHeap m.heap (litObj m ps ls body lam)
  liveBreakScopes := m.liveBreakScopes.filter (fun s => s != m.frames.size) }

theorem litMachine_eq (m : Machine) (ps : List RubyCore.Param) (ls : List String)
    (body : RubyCore.Expr) (lam : Bool) :
    litMachine m ps ls body lam = pushDead (litBase m ps ls body lam) m.currentFrame := rfl

theorem lit_ext {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} (hm : StateOk κ Γ I m)
    (ps : List RubyCore.Param) (ls : List String) (body : RubyCore.Expr) (lam : Bool) :
    Ext m (litBase m ps ls body lam) :=
  have he := ext_push (m := m) (litObj m ps ls body lam) hm.sat hm.core.basicSelf
    (by intro c h; cases h) rfl rfl hm.core.procBasic
  ⟨he.frames, he.stack, he.size, he.get, he.payload, he.ancestors, he.freshIvars,
    he.freshBasic, he.chains, he.rootClean⟩

theorem lit_base_state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} (hm : StateOk κ Γ I m)
    (ps : List RubyCore.Param) (ls : List String) (body : RubyCore.Expr) (lam : Bool) :
    StateOk κ Γ I (litBase m ps ls body lam) :=
  StateOk_ext hm (lit_ext hm ps ls body lam)
    (stringPayloadOk_push hm.stringPayload (by simp [litObj, Boot.procId, Boot.stringId]))
    (arrayPayloadOk_push hm.arrayPayload (by intro xs h; cases h))
    (hashPayloadOk_push hm.hashPayload (by intro xs h; cases h)) rfl

theorem lit_state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} (hm : StateOk κ Γ I m)
    (ps : List RubyCore.Param) (ls : List String) (body : RubyCore.Expr) (lam : Bool) :
    StateOk κ Γ I (litMachine m ps ls body lam) :=
  StateOk_pushDead (lit_base_state hm ps ls body lam) _

theorem lit_framed {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} (hm : StateOk κ Γ I m)
    (ps : List RubyCore.Param) (ls : List String) (body : RubyCore.Expr) (lam : Bool) :
    Framed m (litMachine m ps ls body lam) :=
  (Framed.of_ext (lit_ext hm ps ls body lam)).trans
    (Framed_pushDead (lit_base_state hm ps ls body lam).frameInRange _)

theorem lit_payload (m : Machine) (ps : List RubyCore.Param) (ls : List String)
    (body : RubyCore.Expr) (lam : Bool) :
    procClosure? (litMachine m ps ls body lam).heap (.ref m.heap.objs.size) =
      some (litClosure m ps ls body lam) := by
  simp [litMachine, pushDead, procClosure?, pushHeap_get_self, litObj]

theorem lit_live {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} (hm : StateOk κ Γ I m)
    (ps : List RubyCore.Param) (ls : List String) (body : RubyCore.Expr) (lam : Bool) :
    CaptureLive (litMachine m ps ls body lam) (some (m.stack.headD 0)) := by
  have he := lit_ext hm ps ls body lam
  have hb : CaptureLive (litBase m ps ls body lam) (some (m.stack.headD 0)) :=
    hm.toStateCore.captureLive.frames_preserved (by rw [he.frames]; exact Nat.le_refl _)
      (fun _ _ => by rw [he.frames])
  exact hb.pushDead _

theorem LocalFactsOk.pushDead {f : LocalFacts} {m : Machine} (h : LocalFactsOk f m)
    (hr : FrameInRange m) (hl : CaptureLive m (some (m.stack.headD 0))) (fr : RubyCore.Frame) :
    LocalFactsOk f (Denote.pushDead m fr) := by
  refine ⟨?_, ?_, ?_⟩
  · intro names hn x
    have := h.slots names hn x
    change frameBinds (Denote.pushDead m fr) (m.stack.headD 0) x = _
    simpa only [frameBinds, pushDead_getD hr.2] using this
  · intro x hx
    rw [getLocal_pushDead hl]
    exact h.currentProcs x hx
  · intro x hx
    have := h.bound x hx
    change frameBinds (Denote.pushDead m fr) (m.stack.headD 0) x = _
    simpa only [frameBinds, pushDead_getD hr.2] using this

#print axioms closure_literal_step₁
#print axioms closure_literal_step₂
#print axioms lit_state
#print axioms lit_framed
end Ratchet.Denote.Typed
