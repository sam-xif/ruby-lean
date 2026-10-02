import Denote.Rules.Method.Effects

/-! The run contract for a method body that may invoke its caller's block. Both
frames retain full typed conformance on values; MethodEffects accounts for local writes
in either frame. Sorbet's local flow typing and stable block captures motivate these
separate output environments (0.6.13405, clink 232). No source rule is admitted here. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

def MethodResultOk (origin : Machine) (Γc Γm : Env) (τ : Ty) (κc κm : Ctx) (Ic Im : Ty)
    (a : Answer) (n : Machine) : Prop :=
  MethodEffects origin n ∧ AnsOk τ n a ∧ (∀ v, a = .val v →
    StateOk κc Γc Ic (popMethodFrame n) ∧ StateOk κm Γm Im n)

def MethodRunSpec (origin start : Machine) (Γc Γm : Env) (τ : Ty) (κc κm : Ctx) (Ic Im : Ty) : Prop :=
  SafeA start ∧ ∀ fuel a n rest, runA fuel start = .ans a n rest →
    MethodResultOk origin Γc Γm τ κc κm Ic Im a n

theorem MethodRunSpec.rebase {origin middle start : Machine} {Γc Γm : Env} {τ Ic Im : Ty}
    {κc κm : Ctx} (h : MethodRunSpec middle start Γc Γm τ κc κm Ic Im)
    (hf : MethodEffects origin middle) : MethodRunSpec origin start Γc Γm τ κc κm Ic Im :=
  ⟨h.1, fun fuel a n rest hr => ⟨hf.trans (h.2 fuel a n rest hr).1, (h.2 fuel a n rest hr).2⟩⟩

theorem MethodRunSpec.step {origin start next : Machine} {Γc Γm : Env} {τ Ic Im : Ty}
    {κc κm : Ctx} (ha : answerPoint start = none) (hs : Interp.stepFn start = .next next)
    (h : MethodRunSpec origin next Γc Γm τ κc κm Ic Im) :
    MethodRunSpec origin start Γc Γm τ κc κm Ic Im := by
  constructor
  · intro fuel
    cases fuel with
    | zero => rfl
    | succ f => rw [run_succ, hs]; exact h.1 f
  · intro fuel a n rest hr
    cases fuel with
    | zero => rw [runA_zero ha] at hr; cases hr
    | succ f => rw [runA_succ ha, hs] at hr; exact h.2 f a n rest hr

theorem MethodRunSpec.answer {origin n : Machine} {Γc Γm : Env} {τ Ic Im : Ty}
    {κc κm : Ctx} {a : Answer} (h : MethodResultOk origin Γc Γm τ κc κm Ic Im a n) :
    MethodRunSpec origin (deliverA a n []) Γc Γm τ κc κm Ic Im := by
  constructor
  · cases a with
    | val v => exact safeA_value_nil n v
    | esc j => exact safeA_escape_kontOk (DKontOk.nil (τa := τ) (Γ := Γm)) n j h.2.1
  · intro fuel a' out rest hr
    rw [runA_ans (a := a) (by cases a <;> rfl)] at hr
    injection hr with ha hn
    cases ha; cases hn
    refine ⟨h.1.trans (.ordinary (Framed_reCtl _ _ _)), ?_, ?_⟩
    · cases a with
      | val v => exact denM_deliverA.mpr h.2.1
      | esc j => cases j <;> simpa [AnsOk, EscOk, deliverA] using h.2.1
    · intro v hv
      obtain ⟨hc, hm⟩ := h.2.2 v hv
      exact ⟨by simpa only [popMethodFrame, deliverA] using (StateOk_deliverA (a := a) (K := []) hc),
        StateOk_deliverA hm⟩

theorem MethodRunSpec.bind {origin m : Machine} {Γc Γm Γc' Γm' : Env}
    {σ τ Ic Im Ic' Im' : Ty} {κc κm κc' κm' : Ctx} {e : Ratchet.Expr}
    (h : MethodRunSpec m (evalFrom m e) Γc Γm σ κc κm Ic Im)
    (hroot : RootClean m)
    {K : List Kont} (hK : RubyCore.Proof.CatchFree K)
    (hk : ∀ a n, MethodResultOk m Γc Γm σ κc κm Ic Im a n →
      MethodRunSpec origin (deliverA a n K) Γc' Γm' τ κc' κm' Ic' Im') :
    MethodRunSpec origin (pushK K (evalFrom m e)) Γc' Γm' τ κc' κm' Ic' Im' := by
  constructor
  · exact safe_pushK hK haltBlind_stuck oof_stuck h.1 h.2 (fun a n hn => (hk a n hn).1) hroot
      (fun _ _ hn => hn.1.rootClean hroot)
  · intro fuel a n rest hr
    rw [runA_pushK _ hK fuel (evalFrom m e) hroot (fun a n r hr => (h.2 fuel a n r hr).1.rootClean hroot)] at hr
    cases hs : runA fuel (evalFrom m e) with
    | halt hh => rw [hs] at hr; cases hh <;> cases hr
    | oof _ => rw [hs] at hr; cases hr
    | ans a₁ n₁ r₁ =>
      rw [hs] at hr
      exact (hk a₁ n₁ (h.2 fuel a₁ n₁ r₁ hs)).2 r₁ a n rest hr

/-- A checked callback has the ordinary body contract; its real return marker converts
that result into the enclosing method's two-frame contract. -/
theorem RunSpec.bindMethod {origin m : Machine} {Γ Γc Γm : Env} {σ τ I Ic Im : Ty}
    {κ κc κm : Ctx} {e : Ratchet.Expr}
    (h : RunSpec m (evalFrom m e) Γ σ κ I)
    (hroot : RootClean m)
    {K : List Kont} (hK : RubyCore.Proof.CatchFree K)
    (hk : ∀ a n, ResultOk m Γ σ a n κ I →
      MethodRunSpec origin (deliverA a n K) Γc Γm τ κc κm Ic Im) :
    MethodRunSpec origin (pushK K (evalFrom m e)) Γc Γm τ κc κm Ic Im := by
  constructor
  · exact safe_pushK hK haltBlind_stuck oof_stuck h.1 h.2 (fun a n hn => (hk a n hn).1) hroot
      (fun _ _ hn => hn.1.rootClean hroot)
  · intro fuel a n rest hr
    rw [runA_pushK _ hK fuel (evalFrom m e) hroot (fun a n r hr => (h.2 fuel a n r hr).1.rootClean hroot)] at hr
    cases hs : runA fuel (evalFrom m e) with
    | halt hh => rw [hs] at hr; cases hh <;> cases hr
    | oof _ => rw [hs] at hr; cases hr
    | ans a₁ n₁ r₁ =>
      rw [hs] at hr
      exact (hk a₁ n₁ (h.2 fuel a₁ n₁ r₁ hs)).2 r₁ a n rest hr

/-- Cross back into the ordinary expression contract after leaving the method. -/
theorem MethodRunSpec.bindSpec {origin m : Machine} {Γc Γm Γ : Env}
    {σ τ Ic Im I : Ty} {κc κm κ : Ctx} {e : Ratchet.Expr}
    (h : MethodRunSpec m (evalFrom m e) Γc Γm σ κc κm Ic Im)
    (hroot : RootClean m)
    {K : List Kont} (hK : RubyCore.Proof.CatchFree K)
    (hk : ∀ a n, MethodResultOk m Γc Γm σ κc κm Ic Im a n →
      RunSpec origin (deliverA a n K) Γ τ κ I) :
    RunSpec origin (pushK K (evalFrom m e)) Γ τ κ I := by
  constructor
  · exact safe_pushK hK haltBlind_stuck oof_stuck h.1 h.2 (fun a n hn => (hk a n hn).1) hroot
      (fun _ _ hn => hn.1.rootClean hroot)
  · intro fuel a n rest hr
    rw [runA_pushK _ hK fuel (evalFrom m e) hroot (fun a n r hr => (h.2 fuel a n r hr).1.rootClean hroot)] at hr
    cases hs : runA fuel (evalFrom m e) with
    | halt hh => rw [hs] at hr; cases hh <;> cases hr
    | oof _ => rw [hs] at hr; cases hr
    | ans a₁ n₁ r₁ =>
      rw [hs] at hr
      exact (hk a₁ n₁ (h.2 fuel a₁ n₁ r₁ hs)).2 r₁ a n rest hr

/-- Source sequence composition retains the first expression's two-frame effects.
The second expression starts from its proved output states and may retype method locals. -/
theorem MethodRunSpec.seq {m : Machine} {Γc Γm Γc' Γm' : Env}
    {σ τ Ic Im Ic' Im' : Ty} {κc κm κc' κm' : Ctx} {e e' : Ratchet.Expr}
    (hroot : RootClean m)
    (h : MethodRunSpec m (evalFrom m e) Γc Γm σ κc κm Ic Im)
    (hk : ∀ n v, MethodResultOk m Γc Γm σ κc κm Ic Im (.val v) n →
      MethodRunSpec n (evalFrom n e') Γc' Γm' τ κc' κm' Ic' Im') :
    MethodRunSpec m (evalFrom m (.seq [e, e'])) Γc' Γm' τ κc' κm' Ic' Im' := by
  have hK (es : List RubyCore.Expr) : RubyCore.Proof.CatchFree [.seqK es] := by
    intro k hk
    simp only [List.mem_singleton] at hk
    subst k; rfl
  apply MethodRunSpec.step (by rfl) (show Interp.stepFn _ = .next
    (pushK [.seqK [toRuby e']] (evalFrom m e)) from rfl)
  apply h.bind hroot (hK _)
  intro a n hr
  cases a with
  | esc j =>
    obtain ⟨exc, rfl, _⟩ := hr.2.1.only_raise
    apply MethodRunSpec.step (next := deliverA (.esc (.raiseJ exc)) n []) (by rfl) (by rfl)
    apply MethodRunSpec.answer (a := .esc (.raiseJ exc)) (n := n)
    exact ⟨hr.1, hr.2.1, fun _ hv => by cases hv⟩
  | val v =>
    apply MethodRunSpec.step (by rfl) (show Interp.stepFn _ = .next
      (pushK [.seqK []] (evalFrom n e')) from rfl)
    apply (hk n v hr).bind (hr.1.rootClean hroot) (hK [])
    intro a out hout
    have hret := MethodRunSpec.answer ⟨hr.1.trans hout.1, hout.2⟩
    cases a with
    | val _ => exact MethodRunSpec.step (by rfl) (show Interp.stepFn _ = .next _ from rfl) hret
    | esc j =>
      obtain ⟨exc, rfl, _⟩ := hout.2.1.only_raise
      exact MethodRunSpec.step (by rfl) (show Interp.stepFn _ = .next _ from rfl) hret

/-- A mixed-effect method returns the usual caller contract through the real marker.
Only non-type-error raises may escape a currently checked body, just as for other rules. -/
theorem MethodRunSpec.methodReturn {origin m : Machine} {Γc Γm : Env} {τ Ic Im : Ty}
    {κc κm : Ctx} {e : Ratchet.Expr}
    (h : MethodRunSpec m (evalFrom m e) Γc Γm τ κc κm Ic Im)
    (hl : FrameInRange origin) (hu : RootUncaptured origin)
    (hm : FrameInRange m) (hmu : RootUncaptured m)
    (fresh : origin.frames.size ≤ m.stack.headD 0)
    (hcaller : Framed origin (popMethodFrame m)) (ht : FirstOrder τ = true) (fid : FrameId)
    (hoa : (origin.frames.getD (origin.stack.headD 0) default).localAlias = none)
    (hroot : RootClean origin) :
    RunSpec origin (pushK [.frameK fid] (evalFrom m e)) Γc τ κc Ic := by
  apply h.bindSpec (hcaller.rootClean hroot) (by
    intro k hk
    simp only [List.mem_singleton] at hk
    subst k; rfl)
  intro a n hn
  have hf := hn.1.project hl hu hoa hm hmu fresh hcaller
  cases a with
  | val v =>
    apply RunSpec.step (by rfl) (step_frameK_value n fid v)
    exact RunSpec.answer ⟨hf, (denM_heap_only (m₁ := n) (m₂ := popMethodFrame n) ht rfl).mp hn.2.1,
      fun _ hv => by cases hv; exact (hn.2.2 v rfl).1⟩
  | esc j =>
    apply frameK_escape fid j hn.2.1
    apply RunSpec.answer
    refine ⟨hf, ?_, fun _ hv => by cases hv⟩
    cases j <;> exact hn.2.1

#print axioms MethodRunSpec.bind
#print axioms RunSpec.bindMethod
#print axioms MethodRunSpec.seq
#print axioms MethodRunSpec.answer
#print axioms MethodRunSpec.methodReturn
end Ratchet.Denote.Typed
