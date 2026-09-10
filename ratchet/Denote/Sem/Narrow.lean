import Denote.Sem.Judge
import Denote.Join

/-!
# `Denote/Sem/Narrow.lean` — narrowing soundness, the type-level half

`Judge.if'`/`ifNoElse` type each branch in a **narrowed** environment: if control reached the
then-branch, the condition evaluated truthy, and for a condition of a recognized shape that is
information about a local's or an instance variable's type. `Ratchet/Judge.lean`'s
`narrowEnvs`/`narrowSpine` compute it; nothing has said it is *true*.

The claim splits cleanly in two, and this file is the half that needs no run:

> **the refined type still denotes the value**, given what the branch tells you about it.

Six functions, six lemmas, each an induction over `Ty` following the function's own recursion.
The pattern is the same in all six and worth stating once:

* the arm that answers `.never` is where the branch is **unreachable**, and it is discharged by
  the hypothesis rather than by `denM` — `truthyTy .nilT = .never` is sound precisely because
  `nil` is not truthy, so `denM .nilT m v` and `v.truthy = true` cannot both hold;
* `.nilable`/`.union` recurse and rebuild with `joinT`, so they need "a join is an upper
  bound" (`Denote/Join.lean`) and nothing else;
* the catch-all `τ => τ` is `exact h`.

`Denote/Sem/notes.md`'s twelfth stall point lists these six first for a reason: they are the
part with no dependence on the interpreter at all, so if one of them is *false* the fix is in
`Ratchet/Ty.lean` and no run has to be inverted to find out.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## `if x` — truthiness -/

/-- **`truthyTy` keeps the truthy values.** The `.nilT` arm is the interesting one: it answers
`.never`, whose denotation is `False`, and that is discharged from `v.truthy = true` — `nil` is
not truthy. Everything else either recurses or is the identity. -/
theorem denM_truthyTy : ∀ (τ : Ty) {m : Machine} {v : Value},
    denM τ m v → v.truthy = true → denM (Ratchet.truthyTy τ) m v
  | .nilT, _, v, h, ht => by
    -- `denM .nilT` says the value *is* `nil`, and `nil` is not truthy
    cases v <;> simp_all [denM, isNilV, Value.truthy]
  | .nilable ρ, m, v, h, ht => by
    rw [Ratchet.truthyTy]
    rw [denM] at h
    rcases h with hnil | hρ
    · -- the `nil` half is excluded by truthiness, so the type is `ρ`'s refinement
      cases v <;> simp_all [isNilV, Value.truthy]
    · exact denM_truthyTy ρ hρ ht
  | .union σ τ, m, v, h, ht => by
    rw [Ratchet.truthyTy]
    rw [denM] at h
    rcases h with hσ | hτ
    · exact denM_joinT_left (denM_truthyTy σ hσ ht)
    · exact denM_joinT_right (denM_truthyTy τ hτ ht)
  | .int, _, _, h, _ => h
  | .bool, _, _, h, _ => h
  | .sym, _, _, h, _ => h
  | .float, _, _, h, _ => h
  | .any, _, _, h, _ => h
  | .never, _, _, h, _ => h
  | .cls _, _, _, h, _ => h
  | .clsOf _, _, _, h, _ => h
  | .arrayOf _, _, _, h, _ => h
  | .hashOf _ _, _, _, h, _ => h
  | .inst _ _, _, _, h, _ => h
  | .sameAs _ _, _, _, h, _ => h
  | .ivar0, _, _, h, _ => h
  | .ivarCons .., _, _, h, _ => h
  | .arrow0 _, _, _, h, _ => h
  | .arrowCons .., _, _, h, _ => h
  | .clos .., _, _, h, _ => h

/-- **`falsyTy` keeps the falsy values.** The catch-all is `.never` here rather than the
identity, and that is the asymmetry `Ratchet/Ty.lean`'s docstring calls the whole point: `if x`
where `x : Integer` has an unreachable else-branch. It is sound because Ruby's falsiness is
exactly `{nil, false}`, and this proof is where that is *used* — every immediate arm discharges
`.never`'s `False` from `v.truthy = false`. -/
theorem denM_falsyTy : ∀ (τ : Ty) {m : Machine} {v : Value},
    denM τ m v → v.truthy = false → denM (Ratchet.falsyTy τ) m v
  | .nilT, _, _, h, _ => h
  | .bool, _, _, h, _ => h
  | .any, _, _, h, _ => h
  | .nilable ρ, m, v, h, ht => by
    rw [Ratchet.falsyTy]
    rw [denM] at h
    rcases h with hnil | hρ
    · exact denM_joinT_left (by simpa [denM] using hnil)
    · exact denM_joinT_right (denM_falsyTy ρ hρ ht)
  | .union σ τ, m, v, h, ht => by
    rw [Ratchet.falsyTy]
    rw [denM] at h
    rcases h with hσ | hτ
    · exact denM_joinT_left (denM_falsyTy σ hσ ht)
    · exact denM_joinT_right (denM_falsyTy τ hτ ht)
  | .int, _, v, h, ht => by cases v <;> simp_all [denM, isIntV, Value.truthy]
  | .sym, _, v, h, ht => by cases v <;> simp_all [denM, isSymV, Value.truthy]
  | .float, _, v, h, ht => by cases v <;> simp_all [denM, isFltV, Value.truthy]
  | .never, _, _, h, _ => h
  -- the two nominal arms are the identity now (see `Ratchet/Ty.lean`), so they are free
  | .cls _, _, _, h, _ => h
  | .inst _ _, _, _, h, _ => h
  | .clsOf _, _, v, h, ht => by
    cases v <;> simp_all [denM, isClassRefNamed, Value.truthy]
  | .arrayOf _, _, v, h, ht => by
    cases v <;> simp_all [denM, arrElems?, Value.truthy]
  | .hashOf _ _, _, v, h, ht => by
    cases v <;> simp_all [denM, hshEntries?, Value.truthy]
  | .sameAs _ ρ, m, v, h, ht => by
    -- an alias denotes exactly its payload, and `falsyTy` now refines *under* it (the arm
    -- this proof asked for — see `Ratchet/Ty.lean`)
    rw [Ratchet.falsyTy, denM]
    rw [denM] at h
    exact denM_falsyTy ρ h ht
  -- spines are not value types: `denM` is `False`, so there is nothing to refine
  | .ivar0, _, _, h, _ => by rw [denM] at h; exact h.elim
  | .ivarCons .., _, _, h, _ => by rw [denM] at h; exact h.elim
  -- a Proc is a reference, and every reference is truthy
  | .arrow0 _, _, v, h, ht => by
    rw [denM] at h
    cases v <;> simp_all [isProcV, procClosure?, Value.truthy]
  | .arrowCons .., _, v, h, ht => by
    rw [denM] at h
    cases v <;> simp_all [isProcV, procClosure?, Value.truthy]
  | .clos .., _, v, h, ht => by
    rw [denM] at h
    obtain ⟨cl, hcl, _⟩ := h
    cases v <;> simp_all [procClosure?, Value.truthy]


/-! ## `if x.nil?` — nil-ness

`nil?` differs from truthiness at exactly one value, `false`, and that is why these are two
pairs of functions rather than one: `false.nil?` is `false`, so the then-branch of `if x.nil?`
learns strictly more than the then-branch of `if !x`. -/

/-- **`isNilTy` keeps the `nil` values.** Hypothesis is `v = .nil`, which is stronger than
falsiness — so the `.bool` arm answers `.never` here where `falsyTy` answered `.bool`. -/
theorem denM_isNilTy : ∀ (τ : Ty) {m : Machine} {v : Value},
    denM τ m v → v = .nil → denM (Ratchet.isNilTy τ) m v
  | .nilT, _, _, h, _ => h
  | .any, _, _, h, _ => h
  | .nilable _, _, v, _, hv => by subst hv; rw [Ratchet.isNilTy, denM]; rfl
  | .union σ τ, m, v, h, hv => by
    rw [Ratchet.isNilTy]
    rw [denM] at h
    rcases h with hσ | hτ
    · exact denM_joinT_left (denM_isNilTy σ hσ hv)
    · exact denM_joinT_right (denM_isNilTy τ hτ hv)
  | .sameAs _ ρ, m, v, h, hv => by
    rw [Ratchet.isNilTy, denM]
    rw [denM] at h
    exact denM_isNilTy ρ h hv
  | .cls _, _, _, h, _ => h
  | .inst _ _, _, _, h, _ => h
  | .int, _, v, h, hv => by rw [denM, hv] at h; exact absurd h (by simp [isIntV])
  | .bool, _, v, h, hv => by rw [denM, hv] at h; exact absurd h (by simp [isBoolV])
  | .sym, _, v, h, hv => by rw [denM, hv] at h; exact absurd h (by simp [isSymV])
  | .float, _, v, h, hv => by rw [denM, hv] at h; exact absurd h (by simp [isFltV])
  | .never, _, _, h, _ => h
  | .clsOf _, _, v, h, hv => by
    rw [denM, hv] at h; exact absurd h (by simp [isClassRefNamed])
  | .arrayOf _, _, v, h, hv => by
    rw [denM, hv] at h; exact absurd h (by simp [arrElems?])
  | .hashOf _ _, _, v, h, hv => by
    rw [denM, hv] at h; exact absurd h (by simp [hshEntries?])
  | .ivar0, _, _, h, _ => by rw [denM] at h; exact h.elim
  | .ivarCons .., _, _, h, _ => by rw [denM] at h; exact h.elim
  | .arrow0 _, _, v, h, hv => by
    rw [denM, hv] at h; exact absurd h.1 (by simp [isProcV, procClosure?])
  | .arrowCons .., _, v, h, hv => by
    rw [denM, hv] at h; exact absurd h.1 (by simp [isProcV, procClosure?])
  | .clos .., _, v, h, hv => by
    rw [denM, hv] at h
    obtain ⟨cl, hcl, _⟩ := h
    exact absurd hcl (by simp [procClosure?])

/-- **`nonNilTy` keeps the non-`nil` values.** The mirror image, and the one whose catch-all is
the *identity* — so, unlike `falsyTy`, it needed no correction: refusing to refine is always
sound, and this is the direction where refusing is what the function already did. -/
theorem denM_nonNilTy : ∀ (τ : Ty) {m : Machine} {v : Value},
    denM τ m v → v ≠ .nil → denM (Ratchet.nonNilTy τ) m v
  | .nilT, _, v, h, hv => by
    rw [denM] at h
    exact absurd (by cases v <;> simp_all [isNilV] : v = Value.nil) hv
  | .any, _, _, h, _ => h
  | .nilable ρ, m, v, h, hv => by
    rw [Ratchet.nonNilTy]
    rw [denM] at h
    rcases h with hnil | hρ
    · exact absurd (by cases v <;> simp_all [isNilV] : v = Value.nil) hv
    · exact denM_nonNilTy ρ hρ hv
  | .union σ τ, m, v, h, hv => by
    rw [Ratchet.nonNilTy]
    rw [denM] at h
    rcases h with hσ | hτ
    · exact denM_joinT_left (denM_nonNilTy σ hσ hv)
    · exact denM_joinT_right (denM_nonNilTy τ hτ hv)
  | .int, _, _, h, _ => h
  | .bool, _, _, h, _ => h
  | .sym, _, _, h, _ => h
  | .float, _, _, h, _ => h
  | .never, _, _, h, _ => h
  | .cls _, _, _, h, _ => h
  | .clsOf _, _, _, h, _ => h
  | .arrayOf _, _, _, h, _ => h
  | .hashOf _ _, _, _, h, _ => h
  | .inst _ _, _, _, h, _ => h
  | .sameAs _ _, _, _, h, _ => h
  | .ivar0, _, _, h, _ => h
  | .ivarCons .., _, _, h, _ => h
  | .arrow0 _, _, _, h, _ => h
  | .arrowCons .., _, _, h, _ => h
  | .clos .., _, _, h, _ => h

#print axioms denM_isNilTy
#print axioms denM_nonNilTy


/-! ## `if x.is_a?(C)` — the nominal test, and the two lemmas that need a heap fact

`truthyTy`/`isNilTy` and their complements are facts about `Ty` alone. `isATy`/`notATy` are
not: they answer from `isAAnswer`, a **static table**, while the branch's justification is the
machine's own ancestor walk. So these two are where the file stops being independent of the
heap and starts spending `BaseChainsOk`/`DeclClassOk` (`../Sem/State.lean`) — and where §F9,
§F10 and §F12 came from, each of them a way the static answer could be wrong.

Only the `.never` answers need anything: `isAAnswer = some false` under `isATy` (and `some
true` under `notATy`) means "this branch cannot run", and everything else keeps the type, where
the hypothesis *is* the goal. So each proof is: recurse through `.union`/`.nilable`, and at the
catch-all contradict the one answer that claims emptiness.
-/

/-- **A `.cls n` value's class is the row's base.** Split out of `isA_base_of_denM` because it
is the only row with real content: `denM (.cls n)` *is* `isAName`, so the value is an **is-a**
of the class `n` names, and it takes `BaseChainsOk`'s no-subclasses clause to turn that back
into equality. (That clause is also the one §F11 is about, from the other side.) -/
theorem isA_base_of_cls {κ : Ctx} {m : Machine} (hbc : BaseChainsOk κ m) {n : String}
    {ch : List String} {v : Value} {base : ObjId}
    (hmem : (base, ch) ∈ builtinBases) (hhead : ch.head? = some n)
    (hcf : Ratchet.coreConstFreeN κ = true)
    (hno : Ratchet.isANoOk κ.wholeCls ch = true) (hv : denM (.cls n) m v) :
    RubyCore.classOf m.heap v = base := by
  obtain ⟨hpos, hneg⟩ := hbc base ch hmem
  obtain ⟨hnamed, _⟩ := hpos hcf
  obtain ⟨_, hex⟩ := hneg hno
  rw [denM, isAName, hnamed n hhead] at hv
  simp only at hv
  exact hex (RubyCore.classOf m.heap v) hv

/-- **The bridge from a value's type to the class its values belong to.** One row per surviving
`builtinAncestors` row, and the content is entirely in `denM`: an `.int` is an `Integer` by
`classOf`'s own definition, and a `.cls "String"` is a `String` because that arm of `denM` *is*
`isAName`. (`.arrayOf`/`.hashOf` have no row — see `builtinAncestors`, where they were dropped
for exactly the reason this lemma would otherwise have to invent one.) -/
theorem isA_base_of_denM {κ : Ctx} {m : Machine} (hbc : BaseChainsOk κ m)
    (hcf : Ratchet.coreConstFreeN κ = true) :
    ∀ (τ : Ty) (ch : List String) (v : Value),
      Ratchet.builtinAncestors τ = some ch → Ratchet.isANoOk κ.wholeCls ch = true →
      denM τ m v → ∃ base, (base, ch) ∈ builtinBases ∧ RubyCore.classOf m.heap v = base := by
  intro τ ch v hb hno hv
  match τ with
  | .int =>
    obtain rfl : ch = ["Integer", "Numeric", "Comparable"] ++ Ratchet.rootAncestors := by
      simpa [Ratchet.builtinAncestors] using hb.symm
    refine ⟨Boot.integerId, by simp [builtinBases], ?_⟩
    rw [denM] at hv; cases v <;> simp_all [isIntV, RubyCore.classOf]
  | .float =>
    obtain rfl : ch = ["Float", "Numeric", "Comparable"] ++ Ratchet.rootAncestors := by
      simpa [Ratchet.builtinAncestors] using hb.symm
    refine ⟨Boot.floatId, by simp [builtinBases], ?_⟩
    rw [denM] at hv; cases v <;> simp_all [isFltV, RubyCore.classOf]
  | .nilT =>
    obtain rfl : ch = "NilClass" :: Ratchet.rootAncestors := by
      simpa [Ratchet.builtinAncestors] using hb.symm
    refine ⟨Boot.nilClassId, by simp [builtinBases], ?_⟩
    rw [denM] at hv; cases v <;> simp_all [isNilV, RubyCore.classOf]
  | .sym =>
    obtain rfl : ch = ["Symbol", "Comparable"] ++ Ratchet.rootAncestors := by
      simpa [Ratchet.builtinAncestors] using hb.symm
    refine ⟨Boot.symbolId, by simp [builtinBases], ?_⟩
    rw [denM] at hv; cases v <;> simp_all [isSymV, RubyCore.classOf]
  | .cls n =>
    by_cases h1 : n = "String"
    · subst h1
      obtain rfl : ch = ["String", "Comparable"] ++ Ratchet.rootAncestors := by
        simpa [Ratchet.builtinAncestors] using hb.symm
      exact ⟨Boot.stringId, by simp [builtinBases],
        isA_base_of_cls hbc (by simp [builtinBases]) rfl hcf hno hv⟩
    · by_cases h2 : n = "Hash"
      · subst h2
        obtain rfl : ch = ["Hash", "Enumerable"] ++ Ratchet.rootAncestors := by
          simpa [Ratchet.builtinAncestors] using hb.symm
        exact ⟨Boot.hashId, by simp [builtinBases],
          isA_base_of_cls hbc (by simp [builtinBases]) rfl hcf hno hv⟩
      · exact absurd hb (by simp [Ratchet.builtinAncestors, h1, h2])
  | .never => rw [denM] at hv; exact hv.elim
  | .bool | .any | .clsOf _ | .nilable _ | .union _ _ | .arrayOf _ | .hashOf _ _
  | .inst _ _ | .sameAs _ _ | .ivar0 | .ivarCons .. | .arrow0 _ | .arrowCons ..
  | .clos .. => exact absurd hb (by simp [Ratchet.builtinAncestors])


/-- **`isAAnswer` cannot say "no" about a value that *is* one.** The negative half of the
conformance, packaged for the two refinement lemmas: at a type with a `builtinAncestors` row,
if the machine says the value is a `cn` then `cn` is in the row — so `some false` is
unavailable. Everything the proof needs beyond `BaseChainsOk` is `isA_base_of_denM`. -/
theorem mem_chain_of_isA {κ : Ctx} {m : Machine} (hbc : BaseChainsOk κ m)
    (hcf : Ratchet.coreConstFreeN κ = true)
    {τ : Ty} {ch : List String} {v : Value} {cn : String} {k : ObjId}
    (hg : (Ratchet.constGet? κ cn).isNone = true)
    (hb : Ratchet.builtinAncestors τ = some ch) (hno : Ratchet.isANoOk κ.wholeCls ch = true)
    (hv : denM τ m v) (hcn : classNamed? m.heap cn = some k)
    (hisa : RubyCore.isA m.heap v k = true) : cn ∈ ch := by
  obtain ⟨base, hmem, hcls⟩ := isA_base_of_denM hbc hcf τ ch v hb hno hv
  obtain ⟨_, hneg⟩ := hbc base ch hmem
  obtain ⟨hout, _⟩ := hneg hno
  exact hout cn k hg hcn (by rw [← hcls]; exact hisa)

/-- The same for a **declared** class, off `DeclClassOk`'s chain clause. `.inst` denotes the
class *exactly* (§F12), so this one needs no no-subclasses side condition — which is the whole
practical difference the exactness fix made. -/
theorem mem_chain_of_isA_inst {κ : Ctx} {m : Machine} (hdc : DeclClassOk κ m)
    {n : String} {I : Ty} {v : Value} {cn : String} {k : ObjId} {ch : List String}
    (hmem : ∃ c ∈ κ.classes, c.name = n)
    (hanc : Ratchet.ancestors? κ.classes n = some ch)
    (hmf : Ratchet.mixinFreeChain κ.wholeCls Ratchet.rootAncestors = true)
    (hv : denM (.inst n I) m v) (hcn : classNamed? m.heap cn = some k)
    (hisa : RubyCore.isA m.heap v k = true) : cn ∈ ch ++ Ratchet.rootAncestors := by
  obtain ⟨c, hc, hcname⟩ := hmem
  -- `isExactInst`, read out: a live reference, no eigenclass, and the class field is the class
  -- the name resolves to
  rw [denM] at hv
  obtain ⟨hex, _⟩ := hv
  unfold isExactInst at hex
  -- `split` names the two scrutinees' results; the value is a reference and the name resolves,
  -- or the conjunct is `false`
  split at hex
  · -- four binders: the class the name resolves to, the object id, the resolution equation,
    -- and the spine (which this lemma does not use)
    rename_i cid oid heqn _
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Option.isNone_iff_eq_none]
      at hex
    obtain ⟨⟨_, heig⟩, hkl⟩ := hex
    obtain ⟨_, _, _, _, _, _, hchain⟩ := hdc c hc cid (by rw [hcname]; exact heqn)
    obtain ⟨_, hout⟩ := hchain ch (by rw [hcname]; exact hanc) hmf
    refine hout cn k hcn ?_
    -- with no eigenclass, `classOf` *is* the class field, so the value's ancestor walk is the
    -- class's — which is what the chain clause is about
    rw [RubyCore.isA, RubyCore.classOf, heig] at hisa
    simp only at hisa
    rw [← hkl]
    exact hisa
  · exact absurd hex (by simp)

#print axioms isA_base_of_denM



/-- A declared ancestor chain implies the class is in the table — `ancestorsUp`'s first step is
a `clsGet?`, so this is that step read backwards. Needed because `DeclClassOk` is keyed on
membership while `isAAnswer` is keyed on the chain. -/
theorem ancestors?_mem {C : Ratchet.CTable} {n : String} {ch : List String}
    (h : Ratchet.ancestors? C n = some ch) : ∃ c ∈ C, c.name = n := by
  simp only [Ratchet.ancestors?] at h
  cases hl : C.length with
  | zero =>
    rw [hl] at h
    exact absurd h (by simp [Ratchet.ancestorsUp])
  | succ f =>
    rw [hl] at h
    rw [Ratchet.ancestorsUp] at h
    cases hcg : Ratchet.clsGet? C n with
    | none => rw [hcg] at h; exact absurd h (by simp)
    | some c =>
      simp only [Ratchet.clsGet?] at hcg
      exact ⟨c, List.mem_of_find?_eq_some hcg, by simpa using List.find?_some hcg⟩

/-- **`isAAnswer` cannot answer "no" about a value the machine says yes to.** The two arms of
`isAAnswer` are the two chain facts: `BaseChainsOk` for a builtin row, `DeclClassOk`'s chain
clause for a declared class. Everything else answers `none`, which is not `some false`. -/
theorem isAAnswer_not_no {κ : Ctx} {m : Machine} (hbc : BaseChainsOk κ m)
    (hdc : DeclClassOk κ m)
    (hmf : Ratchet.mixinFreeChain κ.wholeCls Ratchet.rootAncestors = true)
    (hcf : Ratchet.coreConstFreeN κ = true)
    {τ : Ty} {v : Value} {cn : String} {k : ObjId}
    (hg : (Ratchet.constGet? κ cn).isNone = true)
    (ha : Ratchet.isAAnswer κ.classes κ.wholeCls cn τ = some false)
    (hv : denM τ m v) (hcn : classNamed? m.heap cn = some k)
    (hisa : RubyCore.isA m.heap v k = true) : False := by
  cases τ
  -- the declared arm: `ancestors?` answered, and `DeclClassOk`'s chain clause contradicts it
  case inst n I =>
    rw [Ratchet.isAAnswer] at ha
    cases hanc : Ratchet.ancestors? κ.classes n with
    | none => rw [hanc] at ha; exact absurd ha (by simp)
    | some ch =>
      rw [hanc] at ha
      simp only [Option.bind_some] at ha
      split at ha
      · exact absurd ha (by simp)
      · rename_i hnc
        exact absurd (by
          simpa using mem_chain_of_isA_inst hdc (ancestors?_mem hanc) hanc hmf hv hcn hisa) hnc
  -- and every other shape goes through `builtinAncestors`, where `BaseChainsOk` does
  all_goals
    simp only [Ratchet.isAAnswer, Option.bind_eq_some_iff] at ha
    obtain ⟨ch, hba, hif⟩ := ha
    split at hif
    · rename_i hno
      split at hif
      · exact absurd hif (by simp)
      · rename_i hnc
        exact absurd (by simpa using mem_chain_of_isA hbc hcf hg hba hno hv hcn hisa) hnc
    · exact absurd hif (by simp)


/-- **`isAAnswer` cannot answer "yes" about a value the machine says no to** — the mirror, and
it spends the *other* direction of the same two clauses (every name in the chain resolves to a
real ancestor). `notATy`'s `.never` is the answer this refutes. -/
theorem isAAnswer_not_yes {κ : Ctx} {m : Machine} (hbc : BaseChainsOk κ m)
    (hdc : DeclClassOk κ m)
    (hmf : Ratchet.mixinFreeChain κ.wholeCls Ratchet.rootAncestors = true)
    (hcf : Ratchet.coreConstFreeN κ = true)
    {τ : Ty} {v : Value} {cn : String} {k : ObjId}
    (ha : Ratchet.isAAnswer κ.classes κ.wholeCls cn τ = some true)
    (hv : denM τ m v) (hcn : classNamed? m.heap cn = some k)
    (hisa : RubyCore.isA m.heap v k = false) : False := by
  cases τ
  case inst n I =>
    rw [Ratchet.isAAnswer] at ha
    cases hanc : Ratchet.ancestors? κ.classes n with
    | none => rw [hanc] at ha; exact absurd ha (by simp)
    | some ch =>
      rw [hanc] at ha
      simp only [Option.bind_some] at ha
      split at ha
      · -- the name is in the declared chain, so the machine's walk has it too
        rename_i hc
        obtain ⟨c, hcm, hcname⟩ := ancestors?_mem hanc
        rw [denM] at hv
        obtain ⟨hex, _⟩ := hv
        unfold isExactInst at hex
        split at hex
        · rename_i cid oid heqn _
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
            Option.isNone_iff_eq_none] at hex
          obtain ⟨⟨_, heig⟩, hkl⟩ := hex
          obtain ⟨_, _, _, _, _, _, hchain⟩ := hdc c hcm cid (by rw [hcname]; exact heqn)
          obtain ⟨hin, _⟩ := hchain ch (by rw [hcname]; exact hanc) hmf
          obtain ⟨j, hj, hjanc⟩ := hin cn (by simpa using hc)
          rw [hcn, Option.some.injEq] at hj
          rw [RubyCore.isA, RubyCore.classOf, heig] at hisa
          simp only at hisa
          rw [← hj] at hjanc
          rw [hkl] at hisa
          exact absurd hjanc (by rw [hisa]; simp)
        · exact absurd hex (by simp)
      · -- the answer is `some true` only through that branch
        exact absurd ha (by simp)
  all_goals
    simp only [Ratchet.isAAnswer, Option.bind_eq_some_iff] at ha
    obtain ⟨ch, hba, hif⟩ := ha
    split at hif
    · rename_i hno
      split at hif
      · rename_i hc
        obtain ⟨base, hmem, hcls⟩ := isA_base_of_denM hbc hcf _ ch _ hba hno hv
        obtain ⟨hpos, _⟩ := hbc base ch hmem
        obtain ⟨_, hin⟩ := hpos hcf
        obtain ⟨j, hj, hjanc⟩ := hin cn (by simpa using hc)
        rw [hcn, Option.some.injEq] at hj
        rw [RubyCore.isA, hcls] at hisa
        rw [← hj] at hjanc
        exact absurd hjanc (by rw [hisa]; simp)
      · exact absurd hif (by simp)
    · exact absurd hif (by simp)

/-! ## The two nominal refinement lemmas

With the chain facts in hand these are the same shape as `truthyTy`/`falsyTy`: recurse through
`.union`/`.nilable`, and at the catch-all contradict the answer that claims emptiness. The
hypotheses are the *branch's* information — the machine says the value is (or is not) a `cn` —
and the conclusion is that the refined type still denotes it. -/

/-- **`isATy` keeps the values that really are a `cn`.** -/
theorem denM_isATy {κ : Ctx} {m : Machine} (hbc : BaseChainsOk κ m) (hdc : DeclClassOk κ m)
    (hmf : Ratchet.mixinFreeChain κ.wholeCls Ratchet.rootAncestors = true)
    (hcf : Ratchet.coreConstFreeN κ = true) {cn : String}
    (hg : (Ratchet.constGet? κ cn).isNone = true) :
    ∀ (τ : Ty) {v : Value} {k : ObjId},
      denM τ m v → classNamed? m.heap cn = some k → RubyCore.isA m.heap v k = true →
      denM (Ratchet.isATy κ.classes κ.wholeCls cn τ) m v := by
  intro τ
  induction τ with
  | union σ τ ihσ ihτ =>
    intro v k hv hcn hisa
    rw [Ratchet.isATy, denM] at *
    rcases hv with h | h
    · exact denM_joinT_left (ihσ h hcn hisa)
    · exact denM_joinT_right (ihτ h hcn hisa)
  | nilable ρ ih =>
    intro v k hv hcn hisa
    rw [Ratchet.isATy]
    rw [denM] at hv
    rcases hv with hnil | hρ
    · -- the `nil` half: `isANilPart` answers `.nilT` unless it can show `nil` is not a `cn`,
      -- and `BaseChainsOk`'s `NilClass` row is what makes that answer available
      refine denM_joinT_left ?_
      unfold Ratchet.isANilPart
      split
      · rw [denM]; exact hnil
      · split
        · -- `.never`: `nil` would have to be a `cn` outside `NilClass`'s chain
          rename_i hno hcontains
          exfalso
          have hmem := mem_chain_of_isA hbc hcf hg (τ := Ty.nilT)
            (by simp [Ratchet.builtinAncestors]) hcontains (by rw [denM]; exact hnil) hcn
            (by
              cases v <;> simp_all [isNilV])
          exact hno (by simpa using hmem)
        · rw [denM]; exact hnil
    · exact denM_joinT_right (ih hρ hcn hisa)
  | _ =>
    intro v k hv hcn hisa
    -- the catch-all: only a `some false` answer has to be refuted, and that is
    -- `isAAnswer_not_no`
    simp only [Ratchet.isATy]
    split
    · rename_i ha
      rw [denM]
      exact isAAnswer_not_no hbc hdc hmf hcf hg ha hv hcn hisa
    · exact hv


/-- **`notATy` keeps the values that really are *not* a `cn`.** The mirror of `denM_isATy`,
refuting `some true` instead of `some false`, and its `.nilable` arm reads `notANilPart` — the
one piece that needed no §F9 guard, because its `.never` is on the side where `cn` *is* in
`NilClass`'s chain. -/
theorem denM_notATy {κ : Ctx} {m : Machine} (hbc : BaseChainsOk κ m) (hdc : DeclClassOk κ m)
    (hmf : Ratchet.mixinFreeChain κ.wholeCls Ratchet.rootAncestors = true)
    (hcf : Ratchet.coreConstFreeN κ = true) {cn : String} :
    ∀ (τ : Ty) {v : Value} {k : ObjId},
      denM τ m v → classNamed? m.heap cn = some k → RubyCore.isA m.heap v k = false →
      denM (Ratchet.notATy κ.classes κ.wholeCls cn τ) m v := by
  intro τ
  induction τ with
  | union σ τ ihσ ihτ =>
    intro v k hv hcn hisa
    rw [Ratchet.notATy, denM] at *
    rcases hv with h | h
    · exact denM_joinT_left (ihσ h hcn hisa)
    · exact denM_joinT_right (ihτ h hcn hisa)
  | nilable ρ ih =>
    intro v k hv hcn hisa
    rw [Ratchet.notATy]
    rw [denM] at hv
    rcases hv with hnil | hρ
    · refine denM_joinT_left ?_
      unfold Ratchet.notANilPart
      split
      · -- `.never`: `cn` is in `NilClass`'s chain, so `nil` *is* a `cn` — and the branch's
        -- hypothesis says it is not. Straight off `BaseChainsOk`'s positive clauses, which
        -- need only `coreConstFree`; `notANilPart` carries no `isANoOk` guard and does not
        -- need one, its `.never` being on the side a mixin cannot disturb.
        rename_i hc
        exfalso
        obtain ⟨hpos, _⟩ := hbc Boot.nilClassId ("NilClass" :: Ratchet.rootAncestors)
          (by simp [builtinBases])
        obtain ⟨_, hin⟩ := hpos hcf
        obtain ⟨j, hj, hjanc⟩ := hin cn (by simpa using hc)
        rw [hcn, Option.some.injEq] at hj
        rw [← hj] at hjanc
        have hcls : RubyCore.classOf m.heap v = Boot.nilClassId := by
          cases v <;> simp_all [isNilV, RubyCore.classOf]
        rw [RubyCore.isA, hcls] at hisa
        exact absurd hjanc (by rw [hisa]; simp)
      · rw [denM]; exact hnil
    · exact denM_joinT_right (ih hρ hcn hisa)
  | _ =>
    intro v k hv hcn hisa
    simp only [Ratchet.notATy]
    split
    · rename_i ha
      rw [denM]
      exact isAAnswer_not_yes hbc hdc hmf hcf ha hv hcn hisa
    · exact hv

#print axioms denM_truthyTy
#print axioms denM_falsyTy
#print axioms denM_isATy
#print axioms denM_notATy

end Ratchet.Denote
