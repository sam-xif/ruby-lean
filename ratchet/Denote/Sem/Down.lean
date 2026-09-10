import Denote.Sem.State

/-!
# `Denote/Sem/Down.lean` — weakening conformance back down a declaration

The one transport `JudgeSeq.cons` needs, and the one `context-splitting.md` §3 priced at
"antitone, one line" without checking:

> `StateOk (κ.afterStmt e σ) Γ I m → StateOk κ Γ I m`

**Why it is not one line.** L268 recorded that `StateOk` transports in *neither* direction
across `afterStmt`, on two families with opposite variance. The **up** family is gone —
`context-splitting.md` step 1 moved `NameFreeOk`/`BareNameFree`/`MissFree`/`MethodsExact` (and
then `BaseChainsOk`'s three guards) onto `Neg`, which `afterStmt` does not touch, so every one
of them is now *invariant* and the transport for them is `rfl`. What is left is the **down**
family, and it splits three ways:

* **Free** — `ClassesOk`, `DefsOk` and the membership half of `NestedClassesOk`/`DeclClassOk`
  are `∀ x ∈ table` claims, and `Pos`'s list components genuinely *grow*: `mergeCls`
  **prepends** the merged entry rather than replacing it in place (its own docstring says so and
  gives the reason), and `extendDefs`/`addPrivNames` cons. `§1 Growth` below is that fact.
* **Invariant** — everything reading `κ.neg` or `κ.scope`, since `Ctx.afterStmt` rewrites only
  `pos`. Those components are *definitionally* the same proposition at both contexts and are
  reused rather than transported.
* **Owed** — `ConstsOk`/`ConstPathsOk` (because `extendConsts` is `envSet`, which **overwrites**)
  and `DeclClassOk`'s four guarded clauses (whose antecedents fire on fewer inputs as the table
  grows). `Ratchet.ctxKept` is the decidable premise that buys exactly these, and
  `JudgeSeq.cons` carries it.

`found-issues.md` §F21 is the finding this file answers.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## 1. Growth: `Ctx.afterStmt` only ever adds to the list components -/

theorem mergeCls_sub {C : CTable} {x : Cls} {c : Cls} (h : c ∈ C) : c ∈ mergeCls C x := by
  unfold Ratchet.mergeCls
  cases Ratchet.clsGet? C x.name <;> exact List.mem_cons_of_mem _ h

theorem mergeAll_sub : ∀ (cs : List Cls) {C : CTable} {c : Cls}, c ∈ C → c ∈ mergeAll C cs
  | [], _, _, h => h
  | _ :: cs, _, _, h => mergeAll_sub cs (mergeCls_sub h)

theorem extendClasses_sub {C : CTable} {e : Expr} {c : Cls} (h : c ∈ C) :
    c ∈ extendClasses C e := by
  unfold Ratchet.extendClasses
  split
  · split
    · split
      · exact mergeAll_sub _ (mergeCls_sub h)
      · exact mergeAll_sub _ (mergeCls_sub h)
      · exact h
    · exact h
  · split
    · exact mergeAll_sub _ (mergeCls_sub h)
    · exact h
  · exact h

theorem extendDefs_sub {D : DefTable} {e : Expr} {d : Defn} (h : d ∈ D) :
    d ∈ extendDefs D e := by
  unfold Ratchet.extendDefs
  split
  · exact List.mem_cons_of_mem _ h
  · exact h

/-- The two together, at the shape `Ctx.afterStmt` produces. -/
theorem afterStmt_classes_sub {κ : Ctx} {e : Expr} {τ : Ty} {c : Cls} (h : c ∈ κ.classes) :
    c ∈ (κ.afterStmt e τ).classes := extendClasses_sub h

theorem afterStmt_defs_sub {κ : Ctx} {e : Expr} {τ : Ty} {d : Defn} (h : d ∈ κ.defs) :
    d ∈ (κ.afterStmt e τ).defs := extendDefs_sub h

/-- A name the smaller table resolves, the bigger one resolves too — the form
`NestedClassesOk`'s and `DeclClassOk`'s *hypotheses* are in. -/
theorem clsGet?_isSome_of_sub {C C' : CTable} {n : String} {c : Cls}
    (hsub : ∀ x ∈ C, x ∈ C') (h : clsGet? C n = some c) : ∃ c', clsGet? C' n = some c' := by
  have hmem : c ∈ C := List.mem_of_find?_eq_some h
  have hname : (c.name == n) = true := by simpa using List.find?_some h
  cases hc : clsGet? C' n with
  | some c' => exact ⟨c', rfl⟩
  | none =>
    exfalso
    have := (List.find?_eq_none).mp hc c (hsub c hmem)
    exact this hname

/-! ## 2. The constant half of `ctxKept`, unpacked -/

/-- `envGet?_mem` in `Denote/Sem/State.lean` gives `∃ z, (z, σ) ∈ Γ` — the *key* is not pinned,
which is all its consumer needed. `ctxKept`'s clauses are stated per pair, so this one pins
it. -/
theorem envGet?_pair_mem : ∀ {S : Env} {k : String} {τ : Ty}, envGet? S k = some τ → (k, τ) ∈ S
  | [], _, _, h => absurd h (by simp [Ratchet.envGet?])
  | (z, ρ) :: S, k, τ, h => by
    by_cases hz : z = k
    · subst hz
      rw [envGet?_cons_self] at h
      rw [show τ = ρ from (Option.some.inj h).symm]
      exact List.mem_cons_self
    · rw [envGet?_cons_ne _ _ hz] at h
      exact List.mem_cons_of_mem _ (envGet?_pair_mem h)

theorem ctxKept_consts {κ κ' : Ctx} (hk : ctxKept κ κ' = true) {k : String} {τ : Ty}
    (h : envGet? κ.consts k = some τ) : envGet? κ'.consts k = some τ := by
  simp only [Ratchet.ctxKept, Bool.and_eq_true, List.all_eq_true] at hk
  -- `ctxKept` states this clause with `decide` rather than `==`: `Ty` derives `DecidableEq`
  -- and `BEq` as *separate* instances, so `Option Ty` has no `LawfulBEq` and `==` would not
  -- come back out.
  have := hk.1.1.1 (k, τ) (envGet?_pair_mem h)
  exact of_decide_eq_true this

theorem ctxKept_noNew {κ κ' : Ctx} (hk : ctxKept κ κ' = true) {f : Frame}
    (hf : κ.frame = some f) {k : String} (h : envGet? κ.consts k = none) :
    envGet? κ'.consts k = none := by
  simp only [Ratchet.ctxKept, Bool.and_eq_true, List.all_eq_true] at hk
  have hall := hk.1.1.2
  rw [hf] at hall
  simp only [List.all_eq_true] at hall
  cases hc : envGet? κ'.consts k with
  | none => rfl
  | some ρ =>
    exfalso
    have := hall (k, ρ) (envGet?_pair_mem hc)
    rw [show ((k, ρ) : String × Ty).1 = k from rfl, h] at this
    exact absurd this (by simp)

/-- **`constGet?` survives**, which is `ConstsOk`'s form. Both keys of `constPaths` are covered,
and the frame case is where the second `ctxKept` clause is spent: a *new* qualified key would
change the answer for a name whose own binding did not move. -/
theorem ctxKept_constGet {κ κ' : Ctx} (hk : ctxKept κ κ' = true) (hsc : κ.scope = κ'.scope)
    {n : String} {τ : Ty} (h : constGet? κ n = some τ) : constGet? κ' n = some τ := by
  have hfr : κ'.frame = κ.frame := by
    show κ'.scope.frame = κ.scope.frame
    rw [hsc]
  simp only [Ratchet.constGet?, Ratchet.constPaths] at h ⊢
  rw [hfr]
  cases hf : κ.frame with
  | none =>
    rw [hf] at h
    simp only [List.findSome?] at h ⊢
    cases h1 : envGet? κ.consts (constKey n) with
    | none => rw [h1] at h; exact absurd h (by simp)
    | some ρ =>
      rw [h1] at h
      cases h
      rw [ctxKept_consts hk h1]
  | some fr =>
    rw [hf] at h
    simp only [List.findSome?] at h ⊢
    cases h1 : envGet? κ.consts (constKeyIn fr.defClass n) with
    | some ρ =>
      rw [h1] at h; cases h
      rw [ctxKept_consts hk h1]
    | none =>
      rw [h1] at h
      rw [ctxKept_noNew hk hf h1]
      simp only [List.findSome?] at h ⊢
      cases h2 : envGet? κ.consts (constKey n) with
      | none => rw [h2] at h; exact absurd h (by simp)
      | some ρ =>
        rw [h2] at h; cases h
        rw [ctxKept_consts hk h2]

/-! ## 3. The class-table antecedents of `ctxKept`, unpacked -/

theorem ctxKept_ancestors {κ κ' : Ctx} (hk : ctxKept κ κ' = true) {c : Cls} (hc : c ∈ κ.classes) :
    ancestors? κ.classes c.name = ancestors? κ'.classes c.name := by
  simp only [Ratchet.ctxKept, Bool.and_eq_true, List.all_eq_true] at hk
  have := hk.1.2 c hc
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this.1.1

theorem ctxKept_new {κ κ' : Ctx} (hk : ctxKept κ κ' = true) {c : Cls} (hc : c ∈ κ.classes)
    (h : smroGet? κ.classes c.name "new" = none) : smroGet? κ'.classes c.name "new" = none := by
  simp only [Ratchet.ctxKept, Bool.and_eq_true, List.all_eq_true] at hk
  have := hk.1.2 c hc
  simp only [Bool.and_eq_true, h] at this
  simpa using this.1.2

theorem ctxKept_ctor {κ κ' : Ctx} (hk : ctxKept κ κ' = true) {c : Cls} (hc : c ∈ κ.classes)
    (h : ctorGet? κ.classes c.name = none) : ctorGet? κ'.classes c.name = none := by
  simp only [Ratchet.ctxKept, Bool.and_eq_true, List.all_eq_true] at hk
  have := hk.1.2 c hc
  simp only [Bool.and_eq_true, h] at this
  simpa using this.2

theorem ctxKept_mixinFree {κ κ' : Ctx} (hk : ctxKept κ κ' = true)
    (h : mixinFreeChain κ.classes rootAncestors = true) :
    mixinFreeChain κ'.classes rootAncestors = true := by
  simp only [Ratchet.ctxKept, Bool.and_eq_true] at hk
  simpa [h] using hk.2

/-! ## 4. The transport

Component by component. The shape of the proof is the finding: **most of it is `exact h.field`**
— those are the components reading `κ.neg` or `κ.scope`, which `Ctx.afterStmt` leaves alone, so
the proposition at the two contexts is the same one. Six need an argument, and every one of the
six is a component `context-splitting.md` §3's table either mis-classified or omitted. -/

theorem StateOk_down {κ κ' : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    (hk : ctxKept κ κ' = true)
    (hpos : (∀ c ∈ κ.classes, c ∈ κ'.classes) ∧ (∀ d ∈ κ.defs, d ∈ κ'.defs))
    (hneg : κ.neg = κ'.neg) (hsc : κ.scope = κ'.scope)
    (h : StateOk κ' Γ I m) : StateOk κ Γ I m := by
  obtain ⟨hcls, hdfs⟩ := hpos
  have hse : κ'.scope = κ.scope := hsc.symm
  have hnf : ∀ n, Ratchet.nameFreeN κ n = Ratchet.nameFreeN κ' n := by
    intro n
    show (!κ.neg.unpinned && !κ.neg.declared.contains n)
       = (!κ'.neg.unpinned && !κ'.neg.declared.contains n)
    rw [hneg]
  have hcf : Ratchet.coreConstFreeN κ = Ratchet.coreConstFreeN κ' := by
    show coreChainNames.all (fun n => !κ.neg.boundConsts.contains n)
       = coreChainNames.all (fun n => !κ'.neg.boundConsts.contains n)
    rw [hneg]
  have hbc : κ.neg.boundConsts = κ'.neg.boundConsts := by rw [hneg]
  have hwc : κ.neg.wholeCls = κ'.neg.wholeCls := by rw [hneg]
  refine
    { sat := h.sat, core := h.core, frameInRange := h.frameInRange, env := h.env
      selfSpine := h.selfSpine, constScope := h.constScope, selfLive := h.selfLive
      privConsts := trivial, closures := trivial
      -- **Invariant**: `Ctx.afterStmt` rewrites only `pos`, so every component reading
      -- `κ.neg` or `κ.scope` is literally the same proposition at both contexts.
      asms := by have := h.asms; show AsmsOk κ.scope.asms m; rw [← hse]; exact this
      frame := by have := h.frame; show FrameOk κ.scope.frame m; rw [← hse]; exact this
      blockTy := by have := h.blockTy; show BlockTyOk κ.scope.blockTy m; rw [← hse]; exact this
      selfTy := by have := h.selfTy; show SelfTyOk κ.scope.selfTy m; rw [← hse]; exact this
      exact := by intro k cp hcp n md hmem
                  rcases h.exact k cp hcp n md hmem with a | a | a
                  · exact Or.inl a
                  · exact Or.inr (Or.inl a)
                  · exact Or.inr (Or.inr (by rw [hnf]; exact a))
      nameFree := by intro n hn o md hmo
                     rcases h.nameFree n hn o md hmo with a | a | a
                     · exact Or.inl a
                     · exact Or.inr (Or.inl a)
                     · exact Or.inr (Or.inr (by rw [hnf]; exact a))
      bareFree := by intro n hn hfree hself
                     refine h.bareFree n hn ?_ ?_
                     · rw [← hnf]; exact hfree
                     · show κ'.scope.selfTy = none; rw [hse]; exact hself
      missFree := by intro hfree hself
                     refine h.missFree ?_ ?_
                     · rw [← hnf]; exact hfree
                     · show κ'.scope.selfTy = none; rw [hse]; exact hself
      query := by intro mn bid hmem hfree
                  exact h.query mn bid hmem (by rw [← hnf]; exact hfree)
      clsQuery := by intro mn bid hmem hfree
                     exact h.clsQuery mn bid hmem (by rw [← hnf]; exact hfree)
      nilQuery := by intro hfree
                     exact h.nilQuery (by rw [← hnf]; exact hfree)
      baseChains := by
        intro base ch hmem
        obtain ⟨hp, hn⟩ := h.baseChains base ch hmem
        refine ⟨fun hcf0 => hp (by rw [← hcf]; exact hcf0),
                fun hok => ?_⟩
        obtain ⟨h2, h3⟩ := hn (by rw [show κ'.wholeCls = κ.wholeCls from hwc.symm]; exact hok)
        exact ⟨fun cn j hg => h2 cn j (by rw [show κ'.boundConsts = κ.boundConsts from hbc.symm]; exact hg), h3⟩
      -- **Free**: `Pos`'s list components grow, so a `∀ x ∈ table` claim weakens for nothing.
      classes := fun c hc => h.classes c (hcls c hc)
      defs := fun d hd => h.defs d (hdfs d hd)
      nested := by
        intro owner n c hc
        obtain ⟨c', hc'⟩ := clsGet?_isSome_of_sub hcls hc
        exact h.nested owner n c' hc'
      -- **Owed**: the two families `ctxKept` buys.
      consts := by
        intro n τ hg
        exact h.consts n τ (ctxKept_constGet hk hsc hg)
      constPaths := by
        intro owner n τ k hkey
        exact h.constPaths owner n τ k (ctxKept_consts hk hkey)
      declCls := by
        intro c hc k hcn
        obtain ⟨hA, hB, hC, hD, hNew, hCtor, hChain⟩ := h.declCls c (hcls c hc) k hcn
        refine ⟨hA, hB, hC, hD, fun hs => hNew (ctxKept_new hk hc hs),
                fun hct => hCtor (ctxKept_ctor hk hc hct), fun ch han hmf => ?_⟩
        rw [ctxKept_ancestors hk hc] at han
        -- `DeclClassOk`'s chain clause now guards on `mixinFreeChain κ.wholeCls`, which is a
        -- `Neg` field and so invariant; only the *ancestor chain itself* is owed.
        exact hChain ch han (by rw [show κ'.wholeCls = κ.wholeCls from hwc.symm]; exact hmf) }

/-- The form `JudgeSeq.cons` spends: the two `Pos` inclusions and the `neg`/`scope` equalities
are all `rfl` at `κ.afterStmt`, so the premise is exactly `ctxKept`. -/
theorem StateOk_afterStmt_down {κ : Ctx} {e : Expr} {σ : Ty} {Γ : Env} {I : Ty} {m : Machine}
    (hk : ctxKept κ (κ.afterStmt e σ) = true) (h : StateOk (κ.afterStmt e σ) Γ I m) :
    StateOk κ Γ I m :=
  StateOk_down hk ⟨fun _ hc => afterStmt_classes_sub hc, fun _ hd => afterStmt_defs_sub hd⟩
    rfl rfl h

end Ratchet.Denote
