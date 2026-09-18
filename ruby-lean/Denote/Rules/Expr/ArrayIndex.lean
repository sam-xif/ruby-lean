import Denote.Rules.Primitive.PrimitiveStep

/-! Integer indexing: actual Array dispatch, negative offsets, and nil on either bound. -/
set_option autoImplicit false
set_option maxRecDepth 4000
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem array_payload {m : Machine} {v : Value} {τ : Ty} (hd : denM (.arrayOf τ) m v) :
    ∃ o xs, v = .ref o ∧ (m.heap.get o).payload = .arr xs ∧ ∀ x ∈ xs, denM τ m x := by
  rw [denM] at hd
  obtain ⟨xs, hx, hd⟩ := hd
  cases v with
  | ref o =>
    cases hp : (m.heap.get o).payload with
    | arr ys =>
      simp only [arrElems?, hp, Option.some.injEq] at hx
      subst ys
      exact ⟨o, xs, rfl, hp, hd⟩
    | _ => simp [arrElems?, hp] at hx
  | _ => simp [arrElems?] at hx

theorem array_index_run {m : Machine} {o : ObjId} {xs : Array Value}
    (hp : (m.heap.get o).payload = .arr xs) (i : Int) :
    Builtins.run "Array#[]" (.ref o) [.int i] m =
      (let idx := if i < 0 then i + xs.size else i
       if idx < 0 || idx ≥ xs.size then .ok .nil m else .ok xs[idx.toNat]! m) := by
  have hrun : Builtins.run "Array#[]" (.ref o) [.int i] m =
      Builtins.runCollections "Array#[]" (.ref o) [.int i] m := by
    simp only [Builtins.run, List.any_cons, List.any_nil, Builtins.unrepresentableByteStr,
      Builtins.strPayload?, hp, Bool.false_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [hrun]
  unfold Builtins.runCollections
  simp only [Builtins.arrPayload?, hp]

theorem array_index_invoke {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine} {o : ObjId}
    {xs : Array Value} (hm : StateOk κ Γ I m)
    (hp : (m.heap.get o).payload = .arr xs) (i : Int) (hfree : nameFreeN κ "[]" = true := by rfl) :
    Interp.invoke m (.ref o) site "[]" [.int i] none [] =
      builtinStep (Builtins.run "Array#[]" (.ref o) [.int i] m) := by
  have hc := hm.arrayPayload o xs hp
  have hi : Interp.invoke m (.ref o) site "[]" [.int i] none [] =
      Interp.invoke.invokeDispatch m (.ref o) site "[]" [.int i] none [] := by
    rw [Interp.invoke.eq_def]
    simp only [show ("[]" == "send" || "[]" == "public_send" || "[]" == "__send__") = false from rfl,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte, hp]
  obtain ⟨owner, md, hl, hb, hu, hv, hpre, hs⟩ :=
    primitive_lookup hm (by simp [primitiveMethods]) hfree
      (k := Boot.arrayId) (name := "[]") (bid := "Array#[]")
  rw [hi]
  apply invokeDispatch_builtin (owner := owner) (md := md) _ hb hu hv hpre _ (by rfl) (by rfl)
  · rw [lookup_eq_methodOn, hc]; exact hl
  · simpa only [hc] using hs

theorem array_index_step {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine} {recv : Value} {τ : Ty}
    (hm : StateOk κ Γ I m) (hk : m.kont = [])
    (hd : denM (.arrayOf τ) m recv) (i : Int) (hfree : nameFreeN κ "[]" = true := by rfl) :
    StepSpec m Γ (.nilable τ) (Interp.invoke m recv site "[]" [.int i] none []) κ I := by
  obtain ⟨o, xs, rfl, hp, hx⟩ := array_payload hd
  rw [array_index_invoke hm hp i hfree, array_index_run hp i]
  let idx : Int := if i < 0 then i + xs.size else i
  change StepSpec m Γ (.nilable τ)
    (builtinStep (if idx < 0 || idx ≥ xs.size then .ok .nil m else .ok xs[idx.toNat]! m)) κ I
  by_cases hbound : (decide (idx < 0) || decide (idx ≥ xs.size)) = true
  · rw [if_pos hbound]
    exact stepSpec_value hm hk (by rw [denM]; exact Or.inl rfl)
  · rw [if_neg hbound]
    have hb : idx.toNat < xs.size := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hbound
      omega
    apply stepSpec_value hm hk
    rw [denM]
    apply Or.inr
    rw [getElem!_pos xs _ hb]
    exact hx _ (Array.getElem_mem hb)

-- A payload-only type does not imply the dispatch class. This synthetic machine
-- witnesses the missing premise; the new conformance check rejects it.
private def fakeArray : Machine :=
  let (o, h) := bootMachine.heap.alloc { klass := Boot.basicObjectId, payload := .arr #[.int 1] }
  { (bootMachine.setLocal "a" (.ref o)) with heap := h }

#guard !arrayPayloadB fakeArray.heap
#guard match arrElems? fakeArray.heap (fakeArray.getLocal "a") with
  | some #[.int 1] => true
  | _ => false
#guard Semantics.typeStuck (Interp.run 100
  (evalFrom fakeArray (.send (some (.var .lvar "a")) "[]" [.int 0] none)))

-- Runtime boundaries agree with CRuby: -2 and -1 succeed; both outer bounds return nil.
#guard ([-3, -2, -1, 0, 1, 2] : List Int).all fun i =>
  match Interp.run 100 (evalFrom bootMachine
      (.send (some (.array [.int 10, .int 20])) "[]" [.int i] none)) with
  | .value v _ => v.identEq (if i == -2 || i == 0 then .int 10
                            else if i == -1 || i == 1 then .int 20 else .nil)
  | _ => false

#print axioms array_index_step
end Ratchet.Denote.Typed
