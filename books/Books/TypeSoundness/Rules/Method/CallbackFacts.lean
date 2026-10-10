import Books.TypeSoundness.Checker.Static.CallbackFacts
import Books.TypeSoundness.Rules.Method.BodyBoundCall

/-! Alias facts name the actual supplied callback, including native Proc class.
Assignment copies the result's proved identity; a callback preserves method locals. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

def CallbackFactsOk (facts : CallbackFacts) (m : Machine) : Prop :=
  ∀ x ∈ facts.aliases, MethodCallbackReceiver m (m.getLocal x)

theorem CallbackFactsOk.empty (m : Machine) : CallbackFactsOk .empty m := by
  intro _ h; cases h

theorem MethodCallbackReceiver.reCtl {m : Machine} {v : Value}
    (h : MethodCallbackReceiver m v) (c : Ctl) (k : List Kont) :
    MethodCallbackReceiver (reCtl m c k) v := ⟨h.block, h.klass⟩

theorem MethodCallbackReceiver.setLocal {m : Machine} {v : Value}
    (h : MethodCallbackReceiver m v) (x : String) (w : Value) :
    MethodCallbackReceiver (m.setLocal x w) v :=
  ⟨(currentFrame_setLocal_blk m x w).trans h.block, h.klass⟩

theorem CallbackFactsOk.reCtl {facts : CallbackFacts} {m : Machine}
    (h : CallbackFactsOk facts m) (c : Ctl) (k : List Kont) :
    CallbackFactsOk facts (reCtl m c k) := by
  intro x hx
  rw [getLocal_reCtl]
  exact (h x hx).reCtl c k

theorem CallbackFactsOk.write {facts : CallbackFacts} {m : Machine}
    (h : CallbackFactsOk facts m) (hi : m.stack.headD 0 < m.frames.size)
    (ha : (m.frames.getD (m.stack.headD 0) default).localAlias = none)
    (x : String) (v : Value) (callback : Bool)
    (hv : callback = true → MethodCallbackReceiver m v) :
    CallbackFactsOk (facts.write x callback) (m.setLocal x v) := by
  intro y hy
  simp only [CallbackFacts.write, List.mem_append, List.mem_filter, bne_iff_ne] at hy
  rcases hy with hy | ⟨hy, hne⟩
  · cases hc : callback <;> simp only [hc, Bool.false_eq_true, if_true, if_false,
      List.not_mem_nil, List.mem_singleton] at hy
    subst y
    rw [getLocal_setLocal_self m x v hi ha]
    exact (hv hc).setLocal x v
  · rw [getLocal_setLocal_ne m x v hne]
    exact (h y hy).setLocal x v

theorem CallbackFactsOk.copy {facts : CallbackFacts} {m : Machine}
    (h : CallbackFactsOk facts m) (hi : m.stack.headD 0 < m.frames.size)
    (ha : (m.frames.getD (m.stack.headD 0) default).localAlias = none) (x y : String) :
    CallbackFactsOk (facts.copy x y) (m.setLocal x (m.getLocal y)) :=
  h.write hi ha x (m.getLocal y) _ (fun hy => h y (by simpa using hy))

theorem CallbackFactsOk.callback {κ : Ctx} {Γ Γm : Env} {I : Ty}
    {cb : CheckedCallback κ Γ I} {fr : Checker.Frame} {origin m n : Machine} {facts : CallbackFacts}
    (h : CallbackFactsOk facts m) (hm : MethodActivation cb fr Γm origin m)
    (hc : CallbackFramed m n) : CallbackFactsOk facts n := by
  have hn := hc.inRange hm.method.frameInRange
  have hread (x : String) : n.getLocal x = m.getLocal x := by
    have ham := hm.method.headAlias
    have han : (n.frames.getD (n.stack.headD 0) default).localAlias = none := by
      rw [← currentFrame_headD hn.1, hc.active, currentFrame_headD hm.method.frameInRange.1]
      exact ham
    simp only [Machine.getLocal, Machine.getLocal.go, localFrameId_of_noAlias ham,
      localFrameId_of_noAlias han, ← currentFrame_headD hn.1,
      ← currentFrame_headD hm.method.frameInRange.1, hc.active]
    cases m.currentFrame.locals.find? (·.1 == x) <;> simp [hm.scope.uncaptured]
  intro x hx
  rw [hread]
  exact (h x hx).after hm (.callback hc)

def CallbackPost (facts : CallbackFacts) (callback : Bool) (v : Value) (m : Machine) : Prop :=
  CallbackFactsOk facts m ∧ (callback = true → MethodCallbackReceiver m v)

theorem CallbackPost.reCtl {facts : CallbackFacts} {callback : Bool} {v : Value} {m : Machine}
    (h : CallbackPost facts callback v m) (c : Ctl) (k : List Kont) :
    CallbackPost facts callback v (reCtl m c k) :=
  ⟨h.1.reCtl c k, fun hc => (h.2 hc).reCtl c k⟩

#print axioms CallbackFactsOk.write
#print axioms CallbackFactsOk.copy
#print axioms CallbackFactsOk.callback
end Checker.Soundness.Typed
