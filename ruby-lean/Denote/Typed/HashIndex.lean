import Denote.Typed.PrimitiveStep

/-! Hash lookup returns a stored value or nil. Dispatch/default behavior is a checked
heap invariant; arbitrary query types are allowed, and byte-string gates remain gates. -/
set_option autoImplicit false
set_option maxRecDepth 4000
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem hash_payload {m : Machine} {v : Value} {σ τ : Ty} (hd : denM (.hashOf σ τ) m v) :
    ∃ o xs, v = .ref o ∧ (m.heap.get o).payload = .hsh xs ∧
      ∀ p ∈ xs, denM σ m p.1 ∧ denM τ m p.2 := by
  rw [denM] at hd
  obtain ⟨xs, hx, hd⟩ := hd
  cases v with
  | ref o =>
    cases hp : (m.heap.get o).payload with
    | hsh ys =>
      simp only [hshEntries?, hp, Option.some.injEq] at hx
      subst ys
      exact ⟨o, xs, rfl, hp, hd⟩
    | _ => simp [hshEntries?, hp] at hx
  | _ => simp [hshEntries?] at hx

theorem hash_index_invoke {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine} {o : ObjId}
    {xs : Array (Value × Value)} (hm : StateOk κ Γ I m)
    (hp : (m.heap.get o).payload = .hsh xs) (key : Value) (hfree : nameFreeN κ "[]" = true := by rfl) :
    Interp.invoke m (.ref o) site "[]" [key] none [] =
      builtinStep (Builtins.run "Hash#[]" (.ref o) [key] m) := by
  obtain ⟨hc, hd⟩ := hm.hashPayload o xs hp
  have hi : Interp.invoke m (.ref o) site "[]" [key] none [] =
      Interp.invoke.invokeDispatch m (.ref o) site "[]" [key] none [] := by
    rw [Interp.invoke.eq_def]
    simp only [show ("[]" == "send" || "[]" == "public_send" || "[]" == "__send__") = false from rfl,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte, hp]
    rcases hashDefaultNilB_cases hd with hd | hd <;> simp only [hd]
  obtain ⟨owner, md, hl, hb, hu, hv, hpre, hs⟩ :=
    primitive_lookup hm (by simp [primitiveMethods]) hfree
      (k := Boot.hashId) (name := "[]") (bid := "Hash#[]")
  rw [hi]
  apply invokeDispatch_builtin (owner := owner) (md := md) _ hb hu hv hpre _ (by rfl) (by rfl)
  · rw [lookup_eq_methodOn, hc]; exact hl
  · simpa only [hc] using hs

theorem hash_index_step {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine} {recv : Value} {σ τ : Ty}
    (hm : StateOk κ Γ I m) (hk : m.kont = [])
    (hd : denM (.hashOf σ τ) m recv) (key : Value) (hfree : nameFreeN κ "[]" = true := by rfl) :
    StepSpec m Γ (.nilable τ) (Interp.invoke m recv site "[]" [key] none []) κ I := by
  obtain ⟨o, xs, rfl, hp, hx⟩ := hash_payload hd
  rw [hash_index_invoke hm hp key hfree]
  have hr : Builtins.unrepresentableByteStr m.heap (.ref o) = false := by
    simp [Builtins.unrepresentableByteStr, Builtins.strPayload?, hp]
  unfold Builtins.run
  simp only [List.any_cons, List.any_nil, hr, Bool.false_or, Bool.or_false]
  split
  · trivial
  · change StepSpec m Γ (.nilable τ)
      (builtinStep (Builtins.runCollections "Hash#[]" (.ref o) [key] m)) κ I
    unfold Builtins.runCollections
    simp only [Builtins.binArg, hp]
    cases hf : xs.find? (fun p => valueEql m.heap p.1 key) with
    | some p =>
      obtain ⟨k, v⟩ := p
      apply stepSpec_value hm hk
      rw [denM]
      exact Or.inr (hx _ (Array.mem_of_find?_eq_some hf)).2
    | none =>
      rcases hashDefaultNilB_cases (hm.hashPayload o xs hp).2 with hdef | hdef <;>
        simp only [hdef] <;>
        exact stepSpec_value hm hk (by rw [denM]; exact Or.inl rfl)

-- The entries do not constrain a missing-key default: an empty hash still returns true
-- with this default. The new conformance check rejects it, but accepts explicit nil.
private def defaultHash (d : Option HashDefault) : Machine :=
  let (o, h) := bootMachine.heap.alloc
    { klass := Boot.hashId, payload := .hsh #[], hashDflt := d }
  { (bootMachine.setLocal "h" (.ref o)) with heap := h }

#guard !hashPayloadB (defaultHash (some (.val (.bool true)))).heap
#guard !hashPayloadB (defaultHash (some (.prc 0))).heap
#guard hashPayloadB (defaultHash (some (.val .nil))).heap
#guard match Interp.run 100 (evalFrom (defaultHash (some (.val (.bool true))))
    (.send (some (.var .lvar "h")) "[]" [.sym "absent"] none)) with
  | .value (.bool true) _ => true
  | _ => false

#guard ([none, some (.val .nil)] : List (Option HashDefault)).all fun d =>
  match Interp.run 100 (evalFrom (defaultHash d)
      (.send (some (.var .lvar "h")) "[]" [.sym "absent"] none)) with
  | .value .nil _ => true
  | _ => false

#guard ([(.sym "a", .int 3), (.sym "b", .int 2), (.sym "missing", .nil), (.int 1, .nil)] :
    List (Value × Value)).all fun (key, expected) =>
  let (h, m) := Builtins.allocHsh bootMachine #[(.sym "a", .int 3), (.sym "b", .int 2)]
  match Interp.run 100 (evalFrom ((m.setLocal "h" h).setLocal "key" key)
      (.send (some (.var .lvar "h")) "[]" [.var .lvar "key"] none)) with
  | .value v _ => v.identEq expected
  | _ => false

private def byteKeyProbe : Machine :=
  let (h, m) := Builtins.allocHsh bootMachine #[]
  let (key, m) := Builtins.allocStrEnc m (String.singleton (Char.ofNat 255)) true
  (m.setLocal "h" h).setLocal "key" key

#guard match Interp.run 100 (evalFrom byteKeyProbe
    (.send (some (.var .lvar "h")) "[]" [.var .lvar "key"] none)) with
  | .unsupported _ _ => true
  | _ => false

#print axioms hash_index_step
end Ratchet.Denote.Typed
