import Books.TypeSoundness.Conformance.Instance.DefinitionHook
import Books.TypeSoundness.Conformance.Instance.ClassHooks

/-! Reuse the ordinary definition-hook dispatch argument for class callbacks.
The native fidelity shadow outcome is retained. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem native_class_hook_run {name bid : String}
    (hh : (name, bid) ∈ classHookNames) (m : Machine) (recv arg : Value) :
    Builtins.run bid recv [arg] m = .ok .nil m := by
  simp only [classHookNames, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at hh
  have hb : Builtins.byteStrAwareBids.contains bid = true := by
    rcases hh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  have he : (bid.endsWith "#==" || bid.endsWith "#eql?" || bid.endsWith "#!=" ||
      Builtins.pureEqualityBids.contains bid) = false := by
    rcases hh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide +kernel
  simp only [Builtins.run, hb, Bool.not_true, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte, he, Bool.false_and]
  rcases hh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem invoke_native_class_hook {m : Machine} {k owner : ObjId} {cp : ClassPayload}
    {md : MethodDef} {name bid : String} {arg : Value}
    (hh : (name, bid) ∈ classHookNames)
    (hpay : (m.heap.get k).payload = .cls cp)
    (hl : lookup m.heap (.ref k) name = some (owner, md))
    (hb : md.builtin = some bid) (hu : md.undefined = false) :
    Interp.invoke m (.ref k) .reflective name [arg] none [] =
      .next (Interp.withCtl m (.value .nil)) ∨
    ∃ msg, Interp.invoke m (.ref k) .reflective name [arg] none [] =
      .unsupported msg := by
  have hi : Interp.invoke m (.ref k) .reflective name [arg] none [] =
      Interp.invoke.invokeDispatch m (.ref k) .reflective name [arg] none [] := by
    simp only [classHookNames, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at hh
    rcases hh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rw [Interp.invoke.eq_def] <;> simp [hpay]
  rw [hi]
  unfold Interp.invoke.invokeDispatch
  simp only [hl, hu, Bool.false_eq_true, ↓reduceIte]
  cases hs : Interp.crubyResolvedShadow m.heap
      (if md.fromPrelude then [] else
        (ancestors m.heap (classOf m.heap (.ref k))).takeWhile (· != owner)) name md with
  | some msg => exact Or.inr ⟨_, rfl⟩
  | none =>
    simp only [Interp.visError?, hb]
    have ht : Builtins.deferTwin? m.heap bid (.ref k) [arg] = none := by
      simp only [classHookNames, List.mem_cons, List.not_mem_nil, or_false,
        Prod.mk.injEq] at hh
      rcases hh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
          Builtins.toAryDefer?, Builtins.coerceTwin?, Builtins.strCmpDefer?,
          Builtins.strCmpTwin?]
      all_goals repeat' split <;> simp_all
    have hr := native_class_hook_run hh m (.ref k) arg
    simp only [classHookNames, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at hh
    rcases hh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [Interp.nativeDupBid, Interp.nativeCloneBid, Interp.requireBid,
        Interp.enumBid, Interp.nativeIteratorBid, Interp.procCallBid, Interp.arrayMapBid,
        Builtins.dupBids, Builtins.cloneBids, ht, Interp.appendKwHash, hr]

/-- The prefix guard supplies the real lookup; a successful hook changes only control. -/
theorem stepFn_class_hook {m : Machine} {name bid : String} {arg : Value}
    (hh : (name, bid) ∈ classHookNames) (hq : classHooksQuietB m.heap = true)
    (hc : Proof.ChainsIn m.heap) (ho : (m.heap.classPayload? Boot.objectId).isSome = true) :
    Interp.stepFn { m with ctl := .send (.ref Boot.objectId) .reflective name [arg] none [] } =
      .next { m with ctl := .value .nil } ∨
    ∃ msg, Interp.stepFn
      { m with ctl := .send (.ref Boot.objectId) .reflective name [arg] none [] } =
      .unsupported msg := by
  obtain ⟨owner, md, hl, hu, hb⟩ := classHooksQuietB_lookup hq hc hh
  obtain ⟨cp, hp⟩ := Option.isSome_iff_exists.mp ho
  have hpay : (m.heap.get Boot.objectId).payload = .cls cp := by
    unfold Heap.classPayload? at hp
    split at hp <;> simp_all
  let start := { m with ctl := .send (.ref Boot.objectId) .reflective name [arg] none [] }
  have hr := invoke_native_class_hook (m := start) (arg := arg) hh hpay hl hb hu
  exact hr

#print axioms native_class_hook_run
#print axioms invoke_native_class_hook
#print axioms stepFn_class_hook
end Checker.Soundness.Typed
