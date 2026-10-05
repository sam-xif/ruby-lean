import Denote.Rules.Expr.ArrayLength

/-! `Array#first`, `last` and `empty?`: payload reads, never a dispatch on an element. -/
set_option autoImplicit false
set_option maxRecDepth 4000
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem array_first_run {m : Machine} {o : ObjId} {xs : Array Value}
    (hp : (m.heap.get o).payload = .arr xs) :
    Builtins.run "Array#first" (.ref o) [] m = .ok (xs[0]?.getD .nil) m := by
  have hrun : Builtins.run "Array#first" (.ref o) [] m =
      Builtins.runCollections "Array#first" (.ref o) [] m := by
    simp only [Builtins.run, List.any_cons, List.any_nil, Builtins.unrepresentableByteStr,
      Builtins.strPayload?, hp, Bool.false_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    simp only [show ("Array#first".endsWith "#==" || "Array#first".endsWith "#eql?" ||
      "Array#first".endsWith "#!=" || Builtins.pureEqualityBids.contains "Array#first") = false
      from by decide +kernel,
      Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [hrun]
  unfold Builtins.runCollections
  simp only [Builtins.arrPayload?, hp]

theorem array_first_invoke {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine} {o : ObjId}
    {xs : Array Value} (hm : StateOk κ Γ I m)
    (hp : (m.heap.get o).payload = .arr xs) (hfree : nameFreeN κ "first" = true := by rfl) :
    Interp.invoke m (.ref o) site "first" [] none [] =
      builtinStep (Builtins.run "Array#first" (.ref o) [] m) := by
  have hc := hm.arrayPayload o xs hp
  have hi : Interp.invoke m (.ref o) site "first" [] none [] =
      Interp.invoke.invokeDispatch m (.ref o) site "first" [] none [] := by
    rw [Interp.invoke.eq_def]
    simp only [show ("first" == "send" || "first" == "public_send" || "first" == "__send__") = false from rfl,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte, hp]
  obtain ⟨owner, md, hl, hb, hu, hv, hpre, hs⟩ :=
    primitive_lookup hm (by simp [primitiveMethods]) hfree
      (k := Boot.arrayId) (name := "first") (bid := "Array#first")
  rw [hi]
  apply invokeDispatch_builtin (owner := owner) (md := md) _ hb hu hv hpre _ (by
    simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
      nativeReal, rationalPayload?, complexPayload?,
      Builtins.toAryDefer?, Builtins.strCmpDefer?, Builtins.strCmpTwin?, hp]) (by rfl)
  · rw [lookup_eq_methodOn, hc]; exact hl
  · simpa only [hc] using hs

theorem array_last_run {m : Machine} {o : ObjId} {xs : Array Value}
    (hp : (m.heap.get o).payload = .arr xs) :
    Builtins.run "Array#last" (.ref o) [] m = .ok (xs.back?.getD .nil) m := by
  have hrun : Builtins.run "Array#last" (.ref o) [] m =
      Builtins.runCollections "Array#last" (.ref o) [] m := by
    simp only [Builtins.run, List.any_cons, List.any_nil, Builtins.unrepresentableByteStr,
      Builtins.strPayload?, hp, Bool.false_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    simp only [show ("Array#last".endsWith "#==" || "Array#last".endsWith "#eql?" ||
      "Array#last".endsWith "#!=" || Builtins.pureEqualityBids.contains "Array#last") = false
      from by decide +kernel,
      Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [hrun]
  unfold Builtins.runCollections
  simp only [Builtins.arrPayload?, hp]

theorem array_last_invoke {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine} {o : ObjId}
    {xs : Array Value} (hm : StateOk κ Γ I m)
    (hp : (m.heap.get o).payload = .arr xs) (hfree : nameFreeN κ "last" = true := by rfl) :
    Interp.invoke m (.ref o) site "last" [] none [] =
      builtinStep (Builtins.run "Array#last" (.ref o) [] m) := by
  have hc := hm.arrayPayload o xs hp
  have hi : Interp.invoke m (.ref o) site "last" [] none [] =
      Interp.invoke.invokeDispatch m (.ref o) site "last" [] none [] := by
    rw [Interp.invoke.eq_def]
    simp only [show ("last" == "send" || "last" == "public_send" || "last" == "__send__") = false from rfl,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte, hp]
  obtain ⟨owner, md, hl, hb, hu, hv, hpre, hs⟩ :=
    primitive_lookup hm (by simp [primitiveMethods]) hfree
      (k := Boot.arrayId) (name := "last") (bid := "Array#last")
  rw [hi]
  apply invokeDispatch_builtin (owner := owner) (md := md) _ hb hu hv hpre _ (by
    simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
      nativeReal, rationalPayload?, complexPayload?,
      Builtins.toAryDefer?, Builtins.strCmpDefer?, Builtins.strCmpTwin?, hp]) (by rfl)
  · rw [lookup_eq_methodOn, hc]; exact hl
  · simpa only [hc] using hs

theorem array_empty_run {m : Machine} {o : ObjId} {xs : Array Value}
    (hp : (m.heap.get o).payload = .arr xs) :
    Builtins.run "Array#empty?" (.ref o) [] m = .ok (.bool xs.isEmpty) m := by
  have hrun : Builtins.run "Array#empty?" (.ref o) [] m =
      Builtins.runCollections "Array#empty?" (.ref o) [] m := by
    simp only [Builtins.run, List.any_cons, List.any_nil, Builtins.unrepresentableByteStr,
      Builtins.strPayload?, hp, Bool.false_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    simp only [show ("Array#empty?".endsWith "#==" || "Array#empty?".endsWith "#eql?" ||
      "Array#empty?".endsWith "#!=" || Builtins.pureEqualityBids.contains "Array#empty?") = false
      from by decide +kernel,
      Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [hrun]
  unfold Builtins.runCollections
  simp only [Builtins.arrPayload?, hp]

theorem array_empty_invoke {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine} {o : ObjId}
    {xs : Array Value} (hm : StateOk κ Γ I m)
    (hp : (m.heap.get o).payload = .arr xs) (hfree : nameFreeN κ "empty?" = true := by rfl) :
    Interp.invoke m (.ref o) site "empty?" [] none [] =
      builtinStep (Builtins.run "Array#empty?" (.ref o) [] m) := by
  have hc := hm.arrayPayload o xs hp
  have hi : Interp.invoke m (.ref o) site "empty?" [] none [] =
      Interp.invoke.invokeDispatch m (.ref o) site "empty?" [] none [] := by
    rw [Interp.invoke.eq_def]
    simp only [show ("empty?" == "send" || "empty?" == "public_send" || "empty?" == "__send__") = false from rfl,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte, hp]
  obtain ⟨owner, md, hl, hb, hu, hv, hpre, hs⟩ :=
    primitive_lookup hm (by simp [primitiveMethods]) hfree
      (k := Boot.arrayId) (name := "empty?") (bid := "Array#empty?")
  rw [hi]
  apply invokeDispatch_builtin (owner := owner) (md := md) _ hb hu hv hpre _ (by
    simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
      nativeReal, rationalPayload?, complexPayload?,
      Builtins.toAryDefer?, Builtins.strCmpDefer?, Builtins.strCmpTwin?, hp]) (by rfl)
  · rw [lookup_eq_methodOn, hc]; exact hl
  · simpa only [hc] using hs

theorem denM_opt_elem {m : Machine} {τ : Ty} {xs : Array Value} (hx : ∀ x ∈ xs, denM τ m x)
    (o : Option Value) (ho : ∀ v, o = some v → v ∈ xs) : denM (.nilable τ) m (o.getD .nil) := by
  rw [denM]
  cases o with
  | none => exact Or.inl rfl
  | some v => exact Or.inr (hx v (ho v rfl))

theorem array_first_step {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine}
    {recv : Value} {τ : Ty} (hm : StateOk κ Γ I m) (hk : m.kont = [])
    (hd : denM (.arrayOf τ) m recv) (hfree : nameFreeN κ "first" = true := by rfl) :
    StepSpec m Γ (.nilable τ) (Interp.invoke m recv site "first" [] none []) κ I := by
  obtain ⟨o, xs, rfl, hp, hx⟩ := array_payload hd
  rw [array_first_invoke hm hp hfree, array_first_run hp]
  exact stepSpec_value hm hk (denM_opt_elem hx _ (fun v hv => Array.mem_of_getElem? hv))

theorem array_last_step {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine}
    {recv : Value} {τ : Ty} (hm : StateOk κ Γ I m) (hk : m.kont = [])
    (hd : denM (.arrayOf τ) m recv) (hfree : nameFreeN κ "last" = true := by rfl) :
    StepSpec m Γ (.nilable τ) (Interp.invoke m recv site "last" [] none []) κ I := by
  obtain ⟨o, xs, rfl, hp, hx⟩ := array_payload hd
  rw [array_last_invoke hm hp hfree, array_last_run hp]
  exact stepSpec_value hm hk (denM_opt_elem hx _ (fun v hv => by
    rw [Array.back?] at hv; exact Array.mem_of_getElem? hv))

theorem array_empty_step {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine}
    {recv : Value} {τ : Ty} (hm : StateOk κ Γ I m) (hk : m.kont = [])
    (hd : denM (.arrayOf τ) m recv) (hfree : nameFreeN κ "empty?" = true := by rfl) :
    StepSpec m Γ .bool (Interp.invoke m recv site "empty?" [] none []) κ I := by
  obtain ⟨o, xs, rfl, hp, _⟩ := array_payload hd
  rw [array_empty_invoke hm hp hfree, array_empty_run hp]
  exact stepSpec_value hm hk (by simp [denM, isBoolV])

#print axioms array_first_step
#print axioms array_last_step
#print axioms array_empty_step
end Ratchet.Denote.Typed
