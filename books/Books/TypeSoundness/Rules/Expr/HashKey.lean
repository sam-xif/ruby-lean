import Books.TypeSoundness.Rules.Expr.HashIndex

/-! `Hash#key?`: pure key equality over the payload, any query type. -/
set_option autoImplicit false
set_option maxRecDepth 4000
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem hash_key_invoke {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine} {o : ObjId}
    {xs : Array (Value × Value)} (hm : StateOk κ Γ I m)
    (hp : (m.heap.get o).payload = .hsh xs) (key : Value) (hfree : nameFreeN κ "key?" = true := by rfl) :
    Interp.invoke m (.ref o) site "key?" [key] none [] =
      builtinStep (Builtins.run "Hash#key?" (.ref o) [key] m) := by
  obtain ⟨hc, hd⟩ := hm.hashPayload o xs hp
  have hi : Interp.invoke m (.ref o) site "key?" [key] none [] =
      Interp.invoke.invokeDispatch m (.ref o) site "key?" [key] none [] := by
    rw [Interp.invoke.eq_def]
    simp only [show ("key?" == "send" || "key?" == "public_send" || "key?" == "__send__") = false from rfl,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte, hp]
    rcases hashDefaultNilB_cases hd with hd | hd <;> simp only [hd] <;> rfl
  obtain ⟨owner, md, hl, hb, hu, hv, hpre, hs⟩ :=
    primitive_lookup hm (by simp [primitiveMethods]) hfree
      (k := Boot.hashId) (name := "key?") (bid := "Hash#key?")
  rw [hi]
  apply invokeDispatch_builtin (owner := owner) (md := md) _ hb hu hv hpre _ (by
    simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
      nativeReal, rationalPayload?, complexPayload?,
      Builtins.toAryDefer?, Builtins.strCmpDefer?, Builtins.strCmpTwin?, hp]) (by rfl)
  · rw [lookup_eq_methodOn, hc]; exact hl
  · simpa only [hc] using hs

theorem hash_key_step {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine} {recv : Value}
    {σ τ : Ty} (hm : StateOk κ Γ I m) (hk : m.kont = [])
    (hd : denM (.hashOf σ τ) m recv) (key : Value) (hfree : nameFreeN κ "key?" = true := by rfl) :
    StepSpec m Γ .bool (Interp.invoke m recv site "key?" [key] none []) κ I := by
  obtain ⟨o, xs, rfl, hp, _⟩ := hash_payload hd
  rw [hash_key_invoke hm hp key hfree]
  have hr : Builtins.unrepresentableByteStr m.heap (.ref o) = false := by
    simp [Builtins.unrepresentableByteStr, Builtins.strPayload?, hp]
  have he : Builtins.runObjects "Hash#key?" (.ref o) [key] m =
      .ok (.bool (xs.any (fun (k, _) => valueEql m.heap k key))) m := by
    change Builtins.runCollections "Hash#key?" (.ref o) [key] m = _
    unfold Builtins.runCollections
    simp only [Builtins.binArg, Builtins.hshPayload?, hp]
  simp only [Builtins.run]
  repeat' split
  all_goals first | trivial | (rw [he]; exact stepSpec_value hm hk (by simp [denM, isBoolV])) | skip

#print axioms hash_key_step
end Checker.Soundness.Typed
