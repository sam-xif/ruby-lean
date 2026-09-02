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

/-- **An `.inst`-typed value is an object of exactly the named class** — `isExactInst` read
out as an existential, in the shape a dispatch wants. The `.clsOf` twin above (`denM_clsOf_ref`)
gives the class *object*; this gives the class *of* an object, and `Judge.classOf` is the rule
that turns one into the other. -/
theorem denM_inst_exact {m : Machine} {n : String} {I : Ty} {v : Value}
    (h : denM (.inst n I) m v) :
    ∃ k, classNamed? m.heap n = some k ∧ realClassOf m.heap v = k := by
  rw [denM] at h
  obtain ⟨hex, _⟩ := h
  -- `unfold`, not `rw`: `isExactInst`'s equation lemmas include the catch-all arm, and `rw`
  -- picks it (`AGENTS.md`'s equation-compiler trap) — collapsing the hypothesis to `false`
  unfold isExactInst at hex
  -- `split` on the two-scrutinee match: the only arm that can be `true` is
  -- "the name resolves and the value is a reference"
  split at hex
  · rename_i k o hcn _
    simp only [Bool.and_eq_true, beq_iff_eq] at hex
    exact ⟨k, hcn, hex.2⟩
  · exact absurd hex (by simp)

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

/-! ## `C === v` — the same chain at a class-object receiver

`Module#===` is a different method on a different receiver, and the lemmas are stated at the
literal name for the same reason `invoke_isA` is: at a literal, `invoke`'s eight interception
tests all reduce. Two things differ from the `is_a?` family and both make this end *easier*:
the receiver is known to be a class object (so `invokeMaybeNew`'s payload case is the only one
that can fire), and the **argument is unconstrained** — `Module#===` is total on it. -/

theorem invokeMaybeNew_caseEq (m : Machine) (recv : Value) (o : ObjId) (c : ClassPayload)
    (site : SendSite) (args : List Value) (blk : Option Value) (kw : List (Value × Value)) :
    Interp.invoke.invokeMaybeNew m recv o c site "===" args blk kw
      = Interp.invoke.invokeDispatch m recv site "===" args blk kw := by
  rw [Interp.invoke.invokeMaybeNew.eq_def, if_neg (by simp)]

theorem invoke_caseEq (m : Machine) (recv : Value) (site : SendSite) (args : List Value)
    (blk : Option Value) (kw : List (Value × Value)) :
    Interp.invoke m recv site "===" args blk kw
      = Interp.invoke.invokeDispatch m recv site "===" args blk kw := by
  rw [Interp.invoke.eq_def]
  cases recv with
  | ref o =>
    cases hp : (m.heap.get o).payload <;> simp only [hp] <;>
      first
        | rfl
        | (split <;> simp_all [invokeMaybeNew_caseEq])
        | simp_all [invokeMaybeNew_caseEq]
  | _ => rfl

theorem deferTwin?_caseEq (h : Heap) (recv : Value) (args : List Value) :
    Builtins.deferTwin? h "Module#===" recv args = none := by
  simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
    Builtins.toAryDefer?, Builtins.coerceTwin?]
  rcases args with _ | ⟨a, rest⟩
  · rfl
  · cases rest <;> rfl

/-- **`Module#===` is the ancestor test with the operands swapped**, and it is total in the
argument: `binArg` takes the one argument, and the only question asked afterwards is whether
the *receiver* is a class — which `denM (.clsOf cn)` settles. The `unsupported` alternative is
`Builtins.run`'s byte-string gate again, exactly as in `run_isA`. -/
theorem run_caseEq (m : Machine) (av : Value) {k : ObjId}
    (hk : (m.heap.classPayload? k).isSome = true) :
    Builtins.run "Module#===" (.ref k) [av] m = .ok (.bool (isA m.heap av k)) m ∨
      ∃ r, Builtins.run "Module#===" (.ref k) [av] m = .unsupported r := by
  rw [Builtins.run.eq_def]
  dsimp only
  split
  · exact Or.inr ⟨_, rfl⟩
  · refine Or.inl ?_
    rw [Builtins.runObjects.eq_def]
    simp only [Builtins.zeroArgBids, Builtins.dupBids, Builtins.cloneBids]
    rw [Builtins.runNumerics.eq_def]
    simp only
    rw [Builtins.runStrings.eq_def]
    simp only
    rw [Builtins.runCollections.eq_def]
    simp only
    rw [Builtins.runModules.eq_def]
    simp [Builtins.binArg, hk]

/-- `invokeDispatch` at `===`, given the dispatch precondition. Every hypothesis is a conjunct
of `ClsQueryOk` (`../Sem/State.lean`) except the last, which is the *receiver*'s type. -/
theorem invokeDispatch_caseEq {m : Machine} {site : SendSite} {k : ObjId} {av : Value}
    {owner : ObjId} {md : MethodDef}
    (hfound : Interp.methodOn m.heap (classOf m.heap (.ref k)) "===" = some (owner, md))
    (hb : md.builtin = some "Module#===") (hu : md.undefined = false)
    (hv : md.visibility = .pub) (hp : md.fromPrelude = false)
    (hsh : Interp.crubyShadow m.heap
      ((ancestors m.heap (classOf m.heap (.ref k))).takeWhile (fun x => x != owner)) "===" = none)
    (hk : (m.heap.classPayload? k).isSome = true) :
    Interp.invoke.invokeDispatch m (.ref k) site "===" [av] none []
        = .next (Interp.withCtl m (.value (.bool (isA m.heap av k)))) ∨
      ∃ r, Interp.invoke.invokeDispatch m (.ref k) site "===" [av] none []
        = .unsupported r := by
  rw [Interp.invoke.invokeDispatch.eq_def, lookup_eq_methodOn, hfound]
  simp only [hu, hp, if_false, Bool.false_eq_true, reduceIte, hsh, visError?_pub hv, hb,
    deferTwin?_caseEq]
  rcases run_caseEq m av hk with hr | ⟨r, hr⟩
  · exact Or.inl (by simp [appendKwHash_nil, hr])
  · exact Or.inr ⟨r, by simp [appendKwHash_nil, hr]⟩

/-- `dispatchMiss` at `===` produces no value. Same script as `dispatchMiss_isA_no_value`,
re-run at this name because the `try*` families decide by string literal. -/
theorem dispatchMiss_caseEq_no_value (m : Machine) (recv : Value) (site : SendSite)
    (args : List Value)
    (hmm : ∀ o md, Interp.methodOn m.heap (classOf m.heap recv) "method_missing"
        = some (o, md) → md.builtin.isSome = true) :
    (∃ r, Interp.dispatchMiss m recv site "===" args none = .unsupported r) ∨
    (∃ cls msg, Interp.dispatchMiss m recv site "===" args none
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

theorem invokeDispatch_caseEq_miss {m : Machine} {recv : Value} {site : SendSite}
    {args : List Value}
    (hnone : Interp.methodOn m.heap (classOf m.heap recv) "===" = none)
    (hmm : ∀ o md, Interp.methodOn m.heap (classOf m.heap recv) "method_missing"
        = some (o, md) → md.builtin.isSome = true) :
    (∃ r, Interp.invoke.invokeDispatch m recv site "===" args none [] = .unsupported r) ∨
    (∃ cls msg, Interp.invoke.invokeDispatch m recv site "===" args none []
      = .next (Interp.raiseErr m cls msg)) := by
  rw [Interp.invoke.invokeDispatch.eq_def, lookup_eq_methodOn, hnone]
  simp only [appendKwHash_nil]
  exact dispatchMiss_caseEq_no_value m recv site args hmm

#print axioms invoke_caseEq
#print axioms run_caseEq
#print axioms invokeDispatch_caseEq
#print axioms invokeDispatch_caseEq_miss

/-! ## `x.class` — the rung the exact reading unlocked

`Object#class` answers `realClassOf`, and `Ty.inst`'s denotation is now `isExactInst`, which
*is* `realClassOf` (`found-issues.md` §F12). So the two ends meet definitionally and this is
the shortest rung in the dispatch family — which is the point: under the old is-a reading the
obligation was **false** (§F8), and the same one-line mismatch was what made every other
dispatch rule unprovable. -/

theorem invokeMaybeNew_clsq (m : Machine) (recv : Value) (o : ObjId) (c : ClassPayload)
    (site : SendSite) (args : List Value) (blk : Option Value) (kw : List (Value × Value)) :
    Interp.invoke.invokeMaybeNew m recv o c site "class" args blk kw
      = Interp.invoke.invokeDispatch m recv site "class" args blk kw := by
  rw [Interp.invoke.invokeMaybeNew.eq_def, if_neg (by simp)]

theorem invoke_clsq (m : Machine) (recv : Value) (site : SendSite) (args : List Value)
    (blk : Option Value) (kw : List (Value × Value)) :
    Interp.invoke m recv site "class" args blk kw
      = Interp.invoke.invokeDispatch m recv site "class" args blk kw := by
  rw [Interp.invoke.eq_def]
  cases recv with
  | ref o =>
    cases hp : (m.heap.get o).payload <;> simp only [hp] <;>
      first
        | rfl
        | (split <;> simp_all [invokeMaybeNew_clsq])
        | simp_all [invokeMaybeNew_clsq]
  | _ => rfl

theorem deferTwin?_clsq (h : Heap) (recv : Value) (args : List Value) :
    Builtins.deferTwin? h "Object#class" recv args = none := by
  simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
    Builtins.toAryDefer?, Builtins.coerceTwin?]
  rcases args with _ | ⟨a, rest⟩
  · rfl
  · cases rest <;> rfl

/-- **`Object#class` is the class field, and it does not allocate** — so unlike `Module#to_s`
this rung's post-machine is its pre-machine. The `unsupported` alternative is `Builtins.run`'s
byte-string gate, as everywhere. -/
theorem run_clsq (m : Machine) (recv : Value) :
    Builtins.run "Object#class" recv [] m = .ok (.ref (realClassOf m.heap recv)) m ∨
      ∃ r, Builtins.run "Object#class" recv [] m = .unsupported r := by
  rw [Builtins.run.eq_def]
  dsimp only
  split
  · exact Or.inr ⟨_, rfl⟩
  split
  · rename_i hz; exact absurd hz (by simp)
  split
  · rename_i hd
    exact absurd hd (by simp [Builtins.dupBids, Builtins.cloneBids])
  exact Or.inl rfl

theorem invokeDispatch_clsq {m : Machine} {recv : Value} {site : SendSite}
    {owner : ObjId} {md : MethodDef}
    (hfound : Interp.methodOn m.heap (classOf m.heap recv) "class" = some (owner, md))
    (hb : md.builtin = some "Object#class") (hu : md.undefined = false)
    (hv : md.visibility = .pub) (hp : md.fromPrelude = false)
    (hsh : Interp.crubyShadow m.heap
      ((ancestors m.heap (classOf m.heap recv)).takeWhile (fun x => x != owner)) "class"
      = none) :
    Interp.invoke.invokeDispatch m recv site "class" [] none []
        = .next (Interp.withCtl m (.value (.ref (realClassOf m.heap recv)))) ∨
      ∃ r, Interp.invoke.invokeDispatch m recv site "class" [] none [] = .unsupported r := by
  rw [Interp.invoke.invokeDispatch.eq_def, lookup_eq_methodOn, hfound]
  simp only [hu, hp, if_false, Bool.false_eq_true, hsh, visError?_pub hv, hb, deferTwin?_clsq]
  rcases run_clsq m recv with hr | ⟨r, hr⟩
  · exact Or.inl (by simp [appendKwHash_nil, hr])
  · exact Or.inr ⟨r, by simp [appendKwHash_nil, hr]⟩

theorem dispatchMiss_clsq_no_value (m : Machine) (recv : Value) (site : SendSite)
    (args : List Value)
    (hmm : ∀ o md, Interp.methodOn m.heap (classOf m.heap recv) "method_missing"
        = some (o, md) → md.builtin.isSome = true) :
    (∃ r, Interp.dispatchMiss m recv site "class" args none = .unsupported r) ∨
    (∃ cls msg, Interp.dispatchMiss m recv site "class" args none
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

theorem invokeDispatch_clsq_miss {m : Machine} {recv : Value} {site : SendSite}
    {args : List Value}
    (hnone : Interp.methodOn m.heap (classOf m.heap recv) "class" = none)
    (hmm : ∀ o md, Interp.methodOn m.heap (classOf m.heap recv) "method_missing"
        = some (o, md) → md.builtin.isSome = true) :
    (∃ r, Interp.invoke.invokeDispatch m recv site "class" args none [] = .unsupported r) ∨
    (∃ cls msg, Interp.invoke.invokeDispatch m recv site "class" args none []
      = .next (Interp.raiseErr m cls msg)) := by
  rw [Interp.invoke.invokeDispatch.eq_def, lookup_eq_methodOn, hnone]
  simp only [appendKwHash_nil]
  exact dispatchMiss_clsq_no_value m recv site args hmm

#print axioms invoke_clsq
#print axioms run_clsq
#print axioms invokeDispatch_clsq
#print axioms invokeDispatch_clsq_miss

#print axioms invokeDispatch_isA_miss
#print axioms dispatchMiss_isA_no_value
#print axioms invokeDispatch_isA
#print axioms visError?_pub
#print axioms invoke_isA

end Ratchet.Denote
