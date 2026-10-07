import Books.TypeSoundness.Rules.Expr.HashIndex
import Books.TypeSoundness.Rules.Primitive.PrimitiveAlloc

/-! `Hash#fetch`: a stored value, the supplied default, or a raised KeyError. -/
set_option autoImplicit false
set_option maxRecDepth 4000
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem hash_fetch_invoke {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine} {o : ObjId}
    {xs : Array (Value × Value)} (hm : StateOk κ Γ I m)
    (hp : (m.heap.get o).payload = .hsh xs) {args : List Value} {a b : Value}
    (hargs : args = [a] ∨ args = [a, b]) (hfree : nameFreeN κ "fetch" = true := by rfl) :
    Interp.invoke m (.ref o) site "fetch" args none [] =
      builtinStep (Builtins.run "Hash#fetch" (.ref o) args m) := by
  obtain ⟨hc, hd⟩ := hm.hashPayload o xs hp
  obtain ⟨owner, md, hl, hb, hu, hv, hpre, hs⟩ :=
    primitive_lookup hm (by simp [primitiveMethods]) hfree
      (k := Boot.hashId) (name := "fetch") (bid := "Hash#fetch")
  rcases hargs with rfl | rfl
  all_goals
    rw [Interp.invoke.eq_def]
    simp only [show ("fetch" == "send" || "fetch" == "public_send" || "fetch" == "__send__") = false
      from rfl, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hp]
    rcases hashDefaultNilB_cases hd with hd | hd <;> simp only [hd] <;>
    apply invokeDispatch_builtin (owner := owner) (md := md) _ hb hu hv hpre _ (by
      simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?, nativeReal,
        rationalPayload?, complexPayload?, Builtins.toAryDefer?, Builtins.strCmpDefer?,
        Builtins.strCmpTwin?, hp]) (by rfl) <;>
    first
      | (rw [lookup_eq_methodOn, hc]; exact hl)
      | simpa only [hc] using hs

theorem hash_fetch_step {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine} {recv : Value}
    {σ τ : Ty} (hm : StateOk κ Γ I m) (hk : m.kont = [])
    (hd : denM (.hashOf σ τ) m recv) (key : Value) (hfree : nameFreeN κ "fetch" = true := by rfl) :
    StepSpec m Γ τ (Interp.invoke m recv site "fetch" [key] none []) κ I := by
  obtain ⟨o, xs, rfl, hp, hx⟩ := hash_payload hd
  rw [hash_fetch_invoke hm hp (b := key) (Or.inl rfl) hfree]
  have hr : Builtins.unrepresentableByteStr m.heap (.ref o) = false := by
    simp [Builtins.unrepresentableByteStr, Builtins.strPayload?, hp]
  unfold Builtins.run
  simp only [List.any_cons, List.any_nil, hr, Bool.false_or, Bool.or_false]
  split
  · trivial
  · split
    · trivial
    · change StepSpec m Γ τ
        (builtinStep (Builtins.runCollections "Hash#fetch" (.ref o) [key] m)) κ I
      unfold Builtins.runCollections
      simp only [Builtins.hshPayload?, hp]
      cases hf : xs.find? (fun p => valueEql m.heap p.1 key) with
      | some p => exact stepSpec_value hm hk (hx _ (Array.mem_of_find?_eq_some hf)).2
      | none =>
        cases Builtins.inspectP m key with
        | ok ki => exact stepSpec_keyError hm hk _
        | error e => trivial

theorem hash_fetch_default_step {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine}
    {recv : Value} {σ τ : Ty} (hm : StateOk κ Γ I m) (hk : m.kont = [])
    (hd : denM (.hashOf σ τ) m recv) (key dflt : Value) (hdf : denM τ m dflt)
    (hfree : nameFreeN κ "fetch" = true := by rfl) :
    StepSpec m Γ τ (Interp.invoke m recv site "fetch" [key, dflt] none []) κ I := by
  obtain ⟨o, xs, rfl, hp, hx⟩ := hash_payload hd
  rw [hash_fetch_invoke hm hp (Or.inr rfl) hfree]
  have hr : Builtins.unrepresentableByteStr m.heap (.ref o) = false := by
    simp [Builtins.unrepresentableByteStr, Builtins.strPayload?, hp]
  unfold Builtins.run
  simp only [List.any_cons, List.any_nil, hr, Bool.false_or, Bool.or_false]
  split
  · trivial
  · split
    · trivial
    · change StepSpec m Γ τ
        (builtinStep (Builtins.runCollections "Hash#fetch" (.ref o) [key, dflt] m)) κ I
      unfold Builtins.runCollections
      simp only [Builtins.hshPayload?, hp]
      cases hf : xs.find? (fun p => valueEql m.heap p.1 key) with
      | some p => exact stepSpec_value hm hk (hx _ (Array.mem_of_find?_eq_some hf)).2
      | none => exact stepSpec_value hm hk hdf

#print axioms hash_fetch_step
#print axioms hash_fetch_default_step
end Checker.Soundness.Typed
