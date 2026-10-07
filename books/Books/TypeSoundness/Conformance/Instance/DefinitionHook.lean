import Books.TypeSoundness.Conformance.Instance.UserDispatch
/-! The queued ordinary definition callback still performs real dispatch. Native
shadow gates are retained; only the installed no-op builtin can return normally. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness
theorem native_method_added_run (m : Machine) (recv : Value) (name : String) :
    Builtins.run "Module#method_added" recv [.sym name] m = .ok .nil m := by
  have hb : Builtins.byteStrAwareBids.contains "Module#method_added" = true := by rfl
  have he : ("Module#method_added".endsWith "#==" ||
      "Module#method_added".endsWith "#eql?" ||
      "Module#method_added".endsWith "#!=" ||
      Builtins.pureEqualityBids.contains "Module#method_added") = false := by decide +kernel
  simp only [Builtins.run, hb, Bool.not_true, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte, he, Bool.false_and]
  rfl

theorem invoke_native_method_added {m : Machine} {k owner : ObjId} {cp : ClassPayload}
    {md : MethodDef} {name : String}
    (hpay : (m.heap.get k).payload = .cls cp)
    (hl : lookup m.heap (.ref k) "method_added" = some (owner, md))
    (hb : md.builtin = some "Module#method_added") (hu : md.undefined = false) :
    Interp.invoke m (.ref k) .reflective "method_added" [.sym name] none [] =
      .next (Interp.withCtl m (.value .nil)) ∨
    ∃ msg, Interp.invoke m (.ref k) .reflective "method_added" [.sym name] none [] =
      .unsupported msg := by
  have hi : Interp.invoke m (.ref k) .reflective "method_added" [.sym name] none [] =
      Interp.invoke.invokeDispatch m (.ref k) .reflective "method_added" [.sym name] none [] := by
    rw [Interp.invoke.eq_def]
    simp [hpay]
  rw [hi]
  unfold Interp.invoke.invokeDispatch
  simp only [hl, hu, Bool.false_eq_true, ↓reduceIte]
  cases hs : Interp.crubyResolvedShadow m.heap
      (if md.fromPrelude then [] else
        (ancestors m.heap (classOf m.heap (.ref k))).takeWhile (· != owner))
      "method_added" md with
  | some msg => exact Or.inr ⟨_, rfl⟩
  | none =>
    simp only [Interp.visError?, hb]
    have ht : Builtins.deferTwin? m.heap "Module#method_added" (.ref k) [.sym name] = none := by
      simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
        Builtins.toAryDefer?, Builtins.coerceTwin?, Builtins.strCmpDefer?,
        Builtins.strCmpTwin?]
      repeat' split <;> simp_all
    have hmain : "Module#method_added".startsWith "Main#" = false := by decide +kernel
    simp [hmain, Interp.nativeDupBid, Interp.nativeCloneBid, Interp.requireBid,
      Interp.enumBid, Interp.nativeIteratorBid, Interp.procCallBid, Interp.arrayMapBid,
      Builtins.dupBids, Builtins.cloneBids, ht, Interp.appendKwHash, native_method_added_run]
#print axioms native_method_added_run
#print axioms invoke_native_method_added
end Checker.Soundness.Typed
