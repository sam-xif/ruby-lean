import Denote.Rules.Expr.ArrayIndex

/-! `Array#length`: actual Array dispatch reads the payload size. -/
set_option autoImplicit false
set_option maxRecDepth 4000
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem array_length_run {m : Machine} {o : ObjId} {xs : Array Value}
    (hp : (m.heap.get o).payload = .arr xs) :
    Builtins.run "Array#length" (.ref o) [] m = .ok (.int xs.size) m := by
  have hrun : Builtins.run "Array#length" (.ref o) [] m =
      Builtins.runCollections "Array#length" (.ref o) [] m := by
    simp only [Builtins.run, List.any_cons, List.any_nil, Builtins.unrepresentableByteStr,
      Builtins.strPayload?, hp, Bool.false_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    simp only [show ("Array#length".endsWith "#==" || "Array#length".endsWith "#eql?" ||
      "Array#length".endsWith "#!=" || Builtins.pureEqualityBids.contains "Array#length") = false
      from by decide +kernel,
      Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [hrun]
  unfold Builtins.runCollections
  simp only [Builtins.arrPayload?, hp]

theorem array_length_invoke {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine} {o : ObjId}
    {xs : Array Value} (hm : StateOk κ Γ I m)
    (hp : (m.heap.get o).payload = .arr xs) (hfree : nameFreeN κ "length" = true := by rfl) :
    Interp.invoke m (.ref o) site "length" [] none [] =
      builtinStep (Builtins.run "Array#length" (.ref o) [] m) := by
  have hc := hm.arrayPayload o xs hp
  have hi : Interp.invoke m (.ref o) site "length" [] none [] =
      Interp.invoke.invokeDispatch m (.ref o) site "length" [] none [] := by
    rw [Interp.invoke.eq_def]
    simp only [show ("length" == "send" || "length" == "public_send" || "length" == "__send__") = false from rfl,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte, hp]
  obtain ⟨owner, md, hl, hb, hu, hv, hpre, hs⟩ :=
    primitive_lookup hm (by simp [primitiveMethods]) hfree
      (k := Boot.arrayId) (name := "length") (bid := "Array#length")
  rw [hi]
  apply invokeDispatch_builtin (owner := owner) (md := md) _ hb hu hv hpre _ (by
    simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
      nativeReal, rationalPayload?, complexPayload?,
      Builtins.toAryDefer?, Builtins.strCmpDefer?, Builtins.strCmpTwin?, hp]) (by rfl)
  · rw [lookup_eq_methodOn, hc]; exact hl
  · simpa only [hc] using hs

theorem array_length_step {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine}
    {recv : Value} {τ : Ty} (hm : StateOk κ Γ I m) (hk : m.kont = [])
    (hd : denM (.arrayOf τ) m recv) (hfree : nameFreeN κ "length" = true := by rfl) :
    StepSpec m Γ .int (Interp.invoke m recv site "length" [] none []) κ I := by
  obtain ⟨o, xs, rfl, hp, _⟩ := array_payload hd
  rw [array_length_invoke hm hp hfree, array_length_run hp]
  exact stepSpec_value hm hk (by simp [denM, isIntV])

#print axioms array_length_step
end Ratchet.Denote.Typed
