import Denote.Sem.Send

/-!
# `Denote/Sem/Query.lean` — the dispatch of a boot query builtin

`Denote/Sem/Send.lean` takes a call's run apart down to `finishSend`. This file walks the rest
of the chain for the **query builtins** — the ones whose conclusion type does not depend on a
signature table, only on the shape of what the builtin answers:

```
finishSend … .none  =  invoke …                        -- `rfl`
invoke …            =  invoke.invokeDispatch …         -- `invoke_dispatch_of_plain`
invokeDispatch …    →  Builtins.run bid recv args m    -- `../Sem/State.lean`'s `QueryOk`
```

The middle step is the fiddly one and it is pure case analysis: `invoke` intercepts eight names
(`send`/`public_send`/`__send__`, `call`/`()`/`[]`/`yield` on a `Proc`, `[]` on a `Hash` with a
default proc, `new` on a class) and everything else falls through to `invokeDispatch`.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-- **A `.clsOf` value is a live class reference.** `classNamed?` only answers at an id whose
class payload is present, so the three facts come together — and `cpathContainer`/`is_a?` both
need the third. Factored out of `Denote/Rules/Path.lean`, which extracts the first two inline
twice. -/
theorem denM_clsOf_ref {m : Machine} {cn : String} {v : Value} (h : denM (.clsOf cn) m v) :
    ∃ k, classNamed? m.heap cn = some k ∧ v = .ref k ∧
      (m.heap.classPayload? k).isSome = true := by
  simp only [denM, isClassRefNamed] at h
  cases hcn : classNamed? m.heap cn with
  | none => rw [hcn] at h; exact absurd h (by cases v <;> simp)
  | some k =>
    rw [hcn] at h
    cases v with
    | ref o =>
      refine ⟨k, rfl, by simp only [beq_iff_eq] at h; rw [h], ?_⟩
      -- `classNamed?` answers `some k` only through its own payload test
      simp only [classNamed?] at hcn
      cases hcl : constLookup m.heap cn with
      | none => rw [hcl] at hcn; exact absurd hcn (by simp)
      | some w =>
        rw [hcl] at hcn
        cases w with
        | ref o' =>
          simp only at hcn
          split at hcn
          · rename_i hpo
            have hok : o' = k := by simpa using hcn
            rw [← hok]; exact hpo
          · exact absurd hcn (by simp)
        | _ => exact absurd hcn (by simp)
    | _ => exact absurd h (by simp)

/-- `visError?` is `none` at a public method, whatever the site. -/
theorem visError?_pub {m : Machine} {recv : Value} {site : SendSite} {md : MethodDef}
    {mname : String} (h : md.visibility = .pub) :
    Interp.visError? m recv site md mname = none := by
  simp only [Interp.visError?, h]

/-- `invokeMaybeNew` is only about `new`, so at any other name it is `invokeDispatch`. -/
theorem invokeMaybeNew_isA (m : Machine) (recv : Value) (o : ObjId) (c : ClassPayload)
    (site : SendSite) (args : List Value) (blk : Option Value) (kw : List (Value × Value)) :
    Interp.invoke.invokeMaybeNew m recv o c site "is_a?" args blk kw
      = Interp.invoke.invokeDispatch m recv site "is_a?" args blk kw := by
  rw [Interp.invoke.invokeMaybeNew.eq_def, if_neg (by simp)]

/-- **`invoke` falls through to `invokeDispatch` at `is_a?`.**

Stated at the *literal* name rather than generically, and that is what makes it short: `invoke`
intercepts eight names by `==` and a `Math` module method by a `match` on `(mname, args)`, so at
a literal every one of those tests reduces, and only the receiver's payload cases remain. The
generic version needs a hypothesis per intercepted name — including the `Math` family — and is
not worth it until a second query rung wants it. -/
theorem invoke_isA (m : Machine) (recv : Value) (site : SendSite) (args : List Value)
    (blk : Option Value) (kw : List (Value × Value)) :
    Interp.invoke m recv site "is_a?" args blk kw
      = Interp.invoke.invokeDispatch m recv site "is_a?" args blk kw := by
  rw [Interp.invoke.eq_def]
  cases recv with
  | ref o =>
    cases hp : (m.heap.get o).payload <;> simp only [hp] <;>
      first
        | rfl
        | (split <;> simp_all [invokeMaybeNew_isA])
        | simp_all [invokeMaybeNew_isA]
  | _ => rfl

/-- An empty keyword bundle appends nothing. -/
theorem appendKwHash_nil (m : Machine) (args : List Value) :
    Interp.appendKwHash m args [] = (args, m) := rfl

/-- `is_a?` defers to no prelude twin: `deferTwin?` tests the *bid* against a fixed list of
`inspect`/`to_s`/coerce/`to_ary` names, and this is not one. -/
theorem deferTwin?_isA (h : Heap) (recv : Value) (args : List Value) :
    Builtins.deferTwin? h "Object#is_a?" recv args = none := by
  -- full `simp`, not `simp only`: the tests are string literals and it is the literal
  -- simproc that decides them
  simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
    Builtins.toAryDefer?, Builtins.coerceTwin?]
  rcases args with _ | ⟨a, rest⟩
  · rfl
  · cases rest <;> rfl

/-- `Object#is_a?` at a class argument answers the ancestor test and leaves the machine alone
— **or gates**. The second alternative is not slack: `Builtins.run` refuses outright when an
argument is a byte string the model cannot represent, and that check runs before any bid is
looked at. A gate produces no value, so the rung does not care which happened. -/
theorem run_isA (m : Machine) (recv : Value) {ka : ObjId}
    (hka : (m.heap.classPayload? ka).isSome = true) :
    Builtins.run "Object#is_a?" recv [.ref ka] m = .ok (.bool (isA m.heap recv ka)) m ∨
      ∃ r, Builtins.run "Object#is_a?" recv [.ref ka] m = .unsupported r := by
  rw [Builtins.run.eq_def]
  -- the `have h := m.heap` is a `let_fun`; `dsimp only` zeta-reduces it so `split` can see
  -- the guard
  dsimp only
  split
  · exact Or.inr ⟨_, rfl⟩
  · refine Or.inl ?_
    -- `rw [eq_def]`, not the arm equation: an *earlier* arm of `runObjects` matches a `.ref`
    -- receiver, so the arm equation carries a "no earlier pattern matched" side condition
    -- (`AGENTS.md`'s equation-compiler trap). At a literal bid the whole match reduces.
    rw [Builtins.runObjects.eq_def]
    simp [hka, Builtins.zeroArgBids, Builtins.dupBids, Builtins.cloneBids]

/-- **`invokeDispatch` at `is_a?`, given the dispatch precondition**: one step to the boolean
the builtin computes. Every hypothesis here is a conjunct of `QueryOk`
(`../Sem/State.lean`) except the last, which is the *argument's* type — `denM (.clsOf cn)` says
the argument is a class reference, and `Object#is_a?` answers `TypeError` at anything else. -/
theorem invokeDispatch_isA {m : Machine} {recv : Value} {site : SendSite} {ka : ObjId}
    {owner : ObjId} {md : MethodDef}
    (hfound : Interp.methodOn m.heap (classOf m.heap recv) "is_a?" = some (owner, md))
    (hb : md.builtin = some "Object#is_a?") (hu : md.undefined = false)
    (hv : md.visibility = .pub) (hp : md.fromPrelude = false)
    (hsh : Interp.crubyShadow m.heap
      ((ancestors m.heap (classOf m.heap recv)).takeWhile (fun x => x != owner)) "is_a?" = none)
    (hka : (m.heap.classPayload? ka).isSome = true) :
    Interp.invoke.invokeDispatch m recv site "is_a?" [.ref ka] none []
        = .next (Interp.withCtl m (.value (.bool (isA m.heap recv ka)))) ∨
      ∃ r, Interp.invoke.invokeDispatch m recv site "is_a?" [.ref ka] none []
        = .unsupported r := by
  rw [Interp.invoke.invokeDispatch.eq_def, lookup_eq_methodOn, hfound]
  simp only [hu, hp, if_false, Bool.false_eq_true, reduceIte, hsh, visError?_pub hv, hb,
    deferTwin?_isA]
  rcases run_isA m recv hka with hr | ⟨r, hr⟩
  · exact Or.inl (by simp [appendKwHash_nil, hr])
  · exact Or.inr ⟨r, by simp [appendKwHash_nil, hr]⟩

/-- **`invokeDispatch` at a name the machine resolves nowhere** produces no value: the
`try*` families decline at `is_a?`, the CRuby shadow gates answer `.unsupported`, and
`method_missing` — with `QueryOk`'s second half saying any binding is a builtin —
leaves `missNoMethod`, which raises.

`Denote/Rules/Bare.lean`'s `dispatchMiss_vcall` is this lemma at `.vcall "x"`; this is the same
argument at `is_a?` and an arbitrary site, which is what a query rung needs. -/
theorem dispatchMiss_isA_no_value (m : Machine) (recv : Value) (site : SendSite)
    (args : List Value)
    (hmm : ∀ o md, Interp.methodOn m.heap (classOf m.heap recv) "method_missing"
        = some (o, md) → md.builtin.isSome = true) :
    (∃ r, Interp.dispatchMiss m recv site "is_a?" args none = .unsupported r) ∨
    (∃ cls msg, Interp.dispatchMiss m recv site "is_a?" args none
      = .next (Interp.raiseErr m cls msg)) := by
  unfold Interp.dispatchMiss
  simp only [Interp.tryIterator, Interp.tryMixin, Interp.tryReflect]
  repeat' split
  all_goals (try (simp only [Interp.missNoMethod]))
  all_goals (try split)
  all_goals first
    | (right; exact ⟨_, _, rfl⟩)
    | (left; exact ⟨_, rfl⟩)
    | simp_all [Interp.missNoMethod]

/-- **`invokeDispatch` when the lookup misses**: the kw bundle is empty, so the arm is
`dispatchMiss` directly. -/
theorem invokeDispatch_isA_miss {m : Machine} {recv : Value} {site : SendSite}
    {args : List Value}
    (hnone : Interp.methodOn m.heap (classOf m.heap recv) "is_a?" = none)
    (hmm : ∀ o md, Interp.methodOn m.heap (classOf m.heap recv) "method_missing"
        = some (o, md) → md.builtin.isSome = true) :
    (∃ r, Interp.invoke.invokeDispatch m recv site "is_a?" args none [] = .unsupported r) ∨
    (∃ cls msg, Interp.invoke.invokeDispatch m recv site "is_a?" args none []
      = .next (Interp.raiseErr m cls msg)) := by
  rw [Interp.invoke.invokeDispatch.eq_def, lookup_eq_methodOn, hnone]
  simp only [appendKwHash_nil]
  exact dispatchMiss_isA_no_value m recv site args hmm

#print axioms invokeDispatch_isA_miss
#print axioms dispatchMiss_isA_no_value
#print axioms invokeDispatch_isA
#print axioms visError?_pub
#print axioms invoke_isA

end Ratchet.Denote
