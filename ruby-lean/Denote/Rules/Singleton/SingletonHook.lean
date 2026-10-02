import Denote.Rules.Method.MethodDispatch
import Denote.Sem.Instance.SingletonHooks

/-! def-self's queued singleton_method_added: real dispatch on the attached class,
native shadows retained as unsupported; only the native no-op returns normally. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem native_singleton_added_run (m : Machine) (recv : Value) (name : String) :
    Builtins.run "BasicObject#singleton_method_added" recv [.sym name] m = .ok .nil m := by
  have hb : Builtins.byteStrAwareBids.contains "BasicObject#singleton_method_added" = true := by rfl
  have he : ("BasicObject#singleton_method_added".endsWith "#==" ||
      "BasicObject#singleton_method_added".endsWith "#eql?" ||
      "BasicObject#singleton_method_added".endsWith "#!=" ||
      Builtins.pureEqualityBids.contains "BasicObject#singleton_method_added") = false := by decide +kernel
  simp only [Builtins.run, hb, Bool.not_true, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte, he, Bool.false_and]
  rfl

theorem invoke_native_singleton_added {m : Machine} {k owner : ObjId} {cp : ClassPayload}
    {md : MethodDef} {name : String}
    (hpay : (m.heap.get k).payload = .cls cp)
    (hl : lookup m.heap (.ref k) "singleton_method_added" = some (owner, md))
    (hb : md.builtin = some "BasicObject#singleton_method_added") (hu : md.undefined = false) :
    Interp.invoke m (.ref k) .reflective "singleton_method_added" [.sym name] none [] =
      .next (Interp.withCtl m (.value .nil)) ∨
    ∃ msg, Interp.invoke m (.ref k) .reflective "singleton_method_added" [.sym name] none [] =
      .unsupported msg := by
  have hi : Interp.invoke m (.ref k) .reflective "singleton_method_added" [.sym name] none [] =
      Interp.invoke.invokeDispatch m (.ref k) .reflective "singleton_method_added" [.sym name] none [] := by
    rw [Interp.invoke.eq_def]
    simp [hpay]
  rw [hi]
  unfold Interp.invoke.invokeDispatch
  simp only [hl, hu, Bool.false_eq_true, ↓reduceIte]
  cases hs : Interp.crubyResolvedShadow m.heap
      (if md.fromPrelude then [] else
        (ancestors m.heap (classOf m.heap (.ref k))).takeWhile (· != owner))
      "singleton_method_added" md with
  | some msg => exact Or.inr ⟨_, rfl⟩
  | none =>
    simp only [Interp.visError?, hb]
    have ht : Builtins.deferTwin? m.heap "BasicObject#singleton_method_added" (.ref k) [.sym name] = none := by
      simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
        Builtins.toAryDefer?, Builtins.coerceTwin?, Builtins.strCmpDefer?,
        Builtins.strCmpTwin?]
      repeat' split <;> simp_all
    have hmain : "BasicObject#singleton_method_added".startsWith "Main#" = false := by decide +kernel
    simp [hmain, Interp.nativeDupBid, Interp.nativeCloneBid, Interp.requireBid,
      Interp.enumBid, Interp.nativeIteratorBid, Interp.procCallBid, Interp.arrayMapBid,
      Builtins.dupBids, Builtins.cloneBids, ht, Interp.appendKwHash, native_singleton_added_run]
theorem singleton_hook_runSpec {origin n : Machine} {κ : Ctx} {Γ : Env} {I : Ty}
    {name : String} {k : ObjId}
    (hn : StateOk κ Γ I n) (hf : Framed origin n)
    (hc : (n.heap.classPayload? k).isSome = true)
    (hh : singletonDefHookQuietB n.heap k = true) :
    RunSpec origin
      { n with ctl := .send (.ref k) .reflective "singleton_method_added" [.sym name] none [],
               kont := [.methodEditsK [] (.sym name)] } Γ .sym κ I := by
  let start : Machine :=
    { n with ctl := .send (.ref k) .reflective "singleton_method_added" [.sym name] none [],
             kont := [.methodEditsK [] (.sym name)] }
  obtain ⟨cp, hcp⟩ := Option.isSome_iff_exists.mp hc
  have hpay : (n.heap.get k).payload = .cls cp := by
    unfold Heap.classPayload? at hcp
    split at hcp <;> simp_all
  unfold singletonDefHookQuietB singletonHookName singletonHookBid at hh
  cases hl : lookup n.heap (.ref k) "singleton_method_added" with
  | none => simp only [hl, Option.any] at hh; cases hh
  | some pair =>
    obtain ⟨owner, md⟩ := pair
    simp only [hl, Option.any, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hh
    obtain hs | ⟨msg, hs⟩ := invoke_native_singleton_added (m := start)
      (name := name) hpay hl hh.2 hh.1
    · apply RunSpec.step (show answerPoint start = none from rfl)
        (show Interp.stepFn start = .next (Interp.withCtl start (.value .nil)) from hs)
      apply RunSpec.step (show answerPoint (Interp.withCtl start (.value .nil)) = none from rfl)
        (show Interp.stepFn (Interp.withCtl start (.value .nil)) =
          .next (deliverA (.val (.sym name)) n []) from ?_)
      · exact RunSpec.answer ⟨hf, by simp [AnsOk, denM, isSymV], fun _ _ => hn⟩
      · rfl
    · exact RunSpec.unsupported (show answerPoint start = none from rfl) hs

#print axioms invoke_native_singleton_added
#print axioms singleton_hook_runSpec
end Ratchet.Denote.Typed
