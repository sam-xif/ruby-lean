# J1/J2 build — working design notes (2026-08-26)

Working notes for the judgment-layer machine-typing build (judgment-layer.md J1/J2).
Decision records go to `Judgment/implementation-notes.md` (J-numbers) as rungs land;
this file is scratch state for the build itself and may be deleted at the end.

## The spine (what is being built)

Mirror of the infer-based spine, authored over `Judge`:

- `Inv` (Proof/Static/Konts.lean:1346) → `InvJ`: same heap conjuncts (NoHook,
  Saturated, LitClsOk, ClassOk, BottomObj, framePopLabels, ClosuresOk — all reused
  verbatim, they mention no typing), existential over
  `F : Decls, c : JCtx, Γ : Env, Γs : List (JCtx × Env)` with `DeclsOkJ`,
  `FramesOkJ` (VTy-based), `StackCtx` (REUSED as-is at `.toFrameCtx` projections —
  it only uses ValueTy at `.cls sc`, atomic), `GlobalsOk` (reused: rows are
  ground), `CtlOkJ`.
- `CtlOk` → `CtlOkJ`: eval arm = `mfrag e = true ∧ ∃ τ τw Γ' D' Γk, Judge D Γ e
  Γs.isEmpty c τ Γ' D' ∧ SubJ τ τw ∧ SubEnv Γk Γ' ∧ KontOkJ D' heap ((c,Γk)::Γs) τw kont`.
  value arm = `∃ τ Γk, VTy heap v τ ∧ SubEnv Γk Γ ∧ KontOkJ ...`. Jump arms mirror
  (RetOkJ / RaiseOk-reuse-or-clone / NxtOkJ).
- `KontOk` → `KontOkJ`: constructor-for-constructor transliteration; infer*
  premises → Judge*/JudgeSeq/JudgeArgs/JudgeElems; subTy → SubJ; ValueTy → VTy;
  stored program additionally `mfragSeq`-gated where needed for the eval arm to
  re-fire (seqK, ifK, recvK args, arrK).
- `step_ok` (Preservation.lean:263) → `step_okJ` over `StepOkJ` (same as StepOk
  with InvJ). Helper lemmas inv_eval/inv_value/inv_push/inv_grow_value/
  inv_implicit_send0/inv_continueArray transliterate (Konts.lean:1969-2245).
- `UserConforms` (Proof/Static/Decls.lean:331) → `UserConformsJ`: same 3 guards +
  `mfrag md.body` + `∃ Γ' r τb, Judge D [] md.body false (JCtx of {cls:=c,
  selfCls:=some c, ret:=r, meth:=some mname, params:=some []}) τb Γ' D ∧
  SubJ τb d.ret ∧ (∀ σ, r = some σ → σ = d.ret)`. `EntryOkJ` = BuiltinEntryOk ∨
  UserEntryOkJ ∨ IterEntryOk (outer two reused). `DeclsOkJ` = DeclsOk with
  MethodRowsOkJ first conjunct; other four halves reused verbatim.
  Transports `DeclsOkJ_grow`/`DeclsOkJ_defineMethod`: reuse the per-half lemmas,
  re-derive only the MethodRowsOk half (UserConformsJ is heap-free like
  UserConforms, so it passes through transports unchanged — the only new content
  is the resolution halves, same as old).

## VTy — the SubJ-closed value judgment

`def VTy (h) (v) (τ) : Prop := ∃ σ, ValueTy h v σ ∧ SubJ σ τ`
(+ later, if lambdas-at-arrows enter the machine fragment, a second disjunct
`ProcAtom` carrying the closure's Judge derivation; NOT in rung 1 — mfrag
excludes literal-block sends including `lambda` initially).

Key lemmas:
- `VTy.ofValueTy`, `VTy.weaken (SubJ.trans)`, `VTy.congr (ValueTy.congr)`,
  `VTy.any`.
- `groundTy : Ty → Bool` (no union/arrow anywhere relevant; and not... define as:
  true at int/bool/nilT/sym/float/cls/clsOf/any/arrayOf e (elements don't matter
  — subTy compares arrayOf by equality); `nilable σ` recurse; false at
  union/arrow0/arrowCons).
- `VTy.toValueTy : VTy h v τ → groundTy τ = true → ValueTy h v τ` — by the
  SubJ-induction lemma `valueTy_subJ : ValueTy h v σ → SubJ σ τ → groundTy τ →
  ValueTy h v τ` (induction on SubJ; union-left vacuous since ValueTy at union
  is uninhabited — prove `valueTy_union_false`; nilableL uses subTy inversion at
  nilable; arrows: ValueTy at arrow uninhabited — `valueTy_arrow_false`).
- `sigOf D τr mname = some _ → groundTy τr` (sigOf → tyClassNames ≠ [] → shape;
  check sigOf's nilable arm L260) — lets dispatch cases convert VTy → ValueTy
  and reuse ALL old dispatch lemmas unchanged.
- narrowing bridges: `VTy v nilT → v = nil`; `VTy v bool → v = true ∨ false`;
  truthiness lemmas (see below).

## SubJ theory needed (extend Judgment/Sub.lean)

- `SubJ.trans` — induction on the RIGHT derivation? Careful: standard proof is
  by induction on (σ ≤ τ) + inversion... plan: prove by double induction via
  size or: induction on first derivation with a nested induction for base-right
  decomposition. Alternative: prove via the Bool checker: `subJb` (fuel) with
  `subJb_sound : subJb n σ τ = true → SubJ σ τ` and `subJb_complete`
  (SubJ → ∀ big-enough fuel). Then trans on the Bool side or directly.
  SIMPLEST: prove `SubJ.trans` directly by induction on the SECOND derivation
  generalizing the first, with a helper inversion `SubJ σ (union a b)` when σ is
  not a union... messy. Fallback: fuel-indexed `subJb` + soundness only (trans
  provable semantically? no). Budget a real attempt; it's core.
  NOTE: subTy_trans exists. For base-base compose ✓.
- Inversions at atomic left/right used by delivery cases.
- `SubJs.trans`, `SubJs_length`, append lemmas (for argsK).
- `subJb : Nat → Ty → Ty → Bool` kernel-reducible + `subJb_sound` (for
  Deriv.check).

## Mutual induction driver (WORKS — tested)

```
refine Judge.rec
  (motive_1 := fun D _ _ _ ctx _ _ D' _ => P) ... (motive_10 := ...)
  ?_ ×92 h hyps...
```
92 minor premises; motive_11 = Judge, 1=Opt 2=Recv 3=Seq 4=Args 5=Elems 6=Pairs
7=KwEntries 8=Rescues(6 idx) 9=Else(7 idx) 10=Ens(5 idx). `induction h using
Judge.rec` FAILS (introN bug); `refine` with explicit ?_ works; discharge bulk
with `all_goals intros; all_goals first | trivial | (exact ...)`.

Mega-lemmas needed:
1. `judge_table_ret` : ctx.ret.isSome → D' = D (and same for ctx.inLoop.isSome)
   — one combined lemma `(ctx.ret.isSome ∨ ctx.inLoop.isSome) → D' = D`.
   Verify defPromote is the ONLY table-changing ctor and it has ret=none,
   inLoop=none premises. For KontOkJ.retOk/nxtOk derivations.
2. Head inversion modulo `.sub` — NOT a mega-lemma; instead each eval case in
   step_okJ handles `.sub` via a single generic strip lemma:
   `judge_strip : Judge D Γ e top ctx τ Γ' D' → ∃ τ₀ Γ'₀, JudgeNS D Γ e top ctx
   τ₀ Γ'₀ D' ∧ SubJ τ₀ τ ∧ SubEnv Γ' Γ'₀` where JudgeNS is... NO — avoid a
   duplicate relation. Instead: the eval-arm carries the slack outside, and each
   eval case does `cases hj` + in the `.sub` case RECURSES — impossible in
   cases. => Use per-head inversion lemmas proved with the Judge.rec driver, or
   ONE mega inversion producing a per-head `match e` Prop (`JInv`). DECISION:
   one mega-lemma `judge_inv : Judge ... → JInv D Γ e top ctx τ Γ' D'` where
   `JInv` is a def matching on (e, with sub-slack baked into each arm as
   ∃ + SubJ + SubEnv). Sub case: slack-compose lemma per arm
   (`JInv_weaken : JInv ... τ Γ' → SubJ τ σ → SubEnv Γ'' Γ' → JInv ... σ Γ''` —
   by match on e, SubJ.trans/SubEnv.trans). Only needs arms for mfrag heads —
   out-of-fragment heads map to `True` (eval case refutes by mfrag first).

## mfrag — the machine-typed fragment gate (Bool, kernel-reducible)

Recursively pinned. Rung 1 (T1 core): int flt str sym tru fls nil, self',
var .lvar, vasgn .lvar (rhs frag), seq (all frag), if' with cond frag AND cond
not a bare `.var .lvar _` (narrowing excluded until the narrow rung), while'
(cond/body frag). Rung 2+: send/vcall/def'/class'/const/ret/nxt/array/...
grown head by head, each with its preservation case. EXCLUDED indefinitely at
J1: cvar (assumption rules undischargeable), begin' (J8 soundness-open — needs
a Judge-rule fix first), yield/retry/redo, literal-block sends (incl. lambda —
keeps arrows out of VTy), sends named "call" (arrow elim), kwargs/hash/splat
etc. until wanted.

## Narrowing machine-typing (LATER RUNG — design solved, don't lose this)

Problem: ifNarrow* rules need value↔store correlation at ifK delivery.
Solution: at the PUSH step (eval `.if' (.var .lvar x) t els`, narrow
derivation), case-split on the CURRENT stored value v₀ = localOfIn frames cur x
(the var-read step returns exactly it, one step later):
- v₀ truthy → next-state env Γnew := envSet Γb x (dropNil τ₀), kont index
  τidx := dropNil τ₀
- v₀ = nil → Γnew := envSet Γb x nilT, τidx := nilT (premise SubJ nilT τ₀)
- v₀ = false → Γnew := envSet Γb x bool, τidx := bool (premises SubJ bool τ₀,
  boolFree τ₀ = false)
One kont constructor `ifNarrowK` carrying the 3-way disjunct + both branch
judgments at the narrowed envs (then@dropNil τ₀, else@elseNarrow τ₀) + joins.
Delivery case per disjunct:
- τidx = dropNil τ₀: truthy-dir eval then at Γnew (=then-env, rfl); falsy-dir:
  boolFree → refute (VTy v (dropNil τ₀) is nil-free+bool-free → truthy);
  ¬boolFree → else-env = envSet x τ₀, conformance by pointwise weakening
  dropNil τ₀ ≤ τ₀.
- τidx = nilT: truthy-dir refuted (VTy v nilT → v = nil); falsy-dir else-env
  conformance via nilT ≤ elseNarrow τ₀ (boolFree: rfl nilT; else nilT ≤ τ₀
  premise).
- τidx = bool: truthy-dir then-env conformance via bool ≤ dropNil τ₀ (lemma
  from SubJ bool τ₀: dropNil preserves bool member); falsy-dir else-env via
  bool ≤ τ₀ (elseNarrow = τ₀ since ¬boolFree).
Needs: FrameConformsJ pointwise-SubJ env weakening lemma; FramesOkJ narrowHead
analogue that REPLACES one binding given the stored value conforms.

## Composition target (J1 exit)

`validate_sound_of_judge`: from (table half of validate: rowsGuarded etc.) +
residue-as-EntryOkJ + a checked root derivation (J2: Deriv.check) →
`InvJ (Machine.init p)` → via invariant_sound_from → ¬typeStuck. New validateJ
path in Judgment/Check.lean; do NOT touch chk/validate (goal says chk theory
may go stale, but simplest is to leave it untouched and add a parallel
validateJ). declsOkJ_of_validate mirrors Bridge.lean's declsOk_table with
EntryOkJ (residue atoms injected via Or.inl BuiltinEntryOk for egEven).

## Key file/line references (scavenge map)

- Inv/CtlOk/KontOk/RetOk/NxtOk/RaiseOk + inv_* helpers: Proof/Static/Konts.lean
  (KontOk at :76, CtlOk :925, Inv :1346, inv_eval.. :1969-2245; RaiseOk :787,
  KontOk.retOk :580, KontOk.nxtOk :869, heap_congr' :1006).
- step_ok: Proof/Static/Preservation.lean:263 (eval cases from :281; StepOk :31;
  inv_implicit_send0 :66; inv_continueArray :198).
- FramesOk/FrameConforms/StackCtx/ValueTy/LocalsOk/FrameOk/FrameShallow/
  BottomObj: Proof/Static/Locals.lean (valueTy? :163, ValueTy :193, ValuesTy
  :485, FrameConforms :559, FramesOk :589, StackCtx :707, TypeAgree :1407).
- DeclsOk/EntryOk/UserConforms/ConformsAt/entry_dispatch: Proof/Static/
  Decls.lean (UserConforms :331, EntryOk :551, DeclsOk :872, entry_dispatch
  :895; DeclsOk_grow / DeclsOk_defineMethod further down).
- Composed cert theorem: Proof/Cert/Sound.lean (validate_sound_of_ctl :102;
  egEven/entryOk_even :164-199). Bridge: Proof/Cert/Bridge.lean (declsOk_table).
- initiation_ctl: Proof/StaticSoundness.lean:102 (transliterate for InvJ).
- Judge/JCtx/bindParamsJ: Judgment/Judge.lean; SubJ/mkUnion/dropNil/boolFree/
  elseNarrow/arrowOf: Judgment/Sub.lean; subTy/SubEnv/envGet?/envSet/FrameCtx:
  Types/Ty.lean.

## Norms

- Proofs off default build target: `lake build Judgment` +
  `lake build RubyCore.Proof.*`; check-proofs.sh audit; axiom-clean
  (#guard_msgs #print axioms), no native_decide on trusted path; norm 5
  kernel-reducibility applies to Deriv.check/mfrag/subJb only.
- Commits: small rungs, J-numbers in Judgment/implementation-notes.md,
  Co-Authored-By trailer. Ratchet: difftest untouched (no interpreter changes).
