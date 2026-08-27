import RubyCore.Judgment.Check
import RubyCore.Proof.Judgment.Cert

/-!
# Adequacy: `Deriv.check` accepts only derivable judgments (J25) — J2's theorem

The near-triviality §4(3) promised: because the checker's nodes mirror `Judge`'s
constructors one-to-one, soundness is a single fuel induction whose every case is
"split the node's side conditions, apply the constructor". Composed at the bottom
into `validateJ_certifies` — a **data** certificate (rows + derivation tree),
checked by one kernel-reduced `Bool`, concluding the reachability property. The
worked ends re-certify `egEven` (claimed row) and `egUserCall` (class body,
promoted row, user dispatch) from literal `Deriv` values under `decide`.
-/

namespace RubyCore
namespace Proof
namespace Judgment

open Interp
open RubyCore.Types
open RubyCore.Cert
open RubyCore.Judgment
open RubyCore.Proof.Static
open RubyCore.Proof.Cert

set_option maxRecDepth 100000

/-- The membership form `defFreeAll` composes from. -/
theorem defFreeAll_of_forall : ∀ {es : List Expr},
    (∀ e ∈ es, defFree e = true) → defFreeAll es = true
  | [], _ => by simp [defFreeAll]
  | e :: rest, h => by
    simp only [defFreeAll, Bool.and_eq_true]
    exact ⟨h e (by simp), defFreeAll_of_forall fun e' he' => h e' (by simp [he'])⟩

/-- The fuel `defFree` is sound against the well-founded original. The arms with
    an option payload case it *before* unfolding — the fuel twin's equations split
    on the nested match, so an abstract option blocks them. -/
theorem defFreeB_sound : ∀ {n : Nat} {e : Expr}, defFreeB n e = true → defFree e = true := by
  intro n
  induction n with
  | zero => intro e h; exact absurd h (by simp [defFreeB])
  | succ n ih =>
    intro e h
    match e with
    | .def' _ _ _ => exact absurd h (by simp [defFreeB])
    | .class' _ _ _ => exact absurd h (by simp [defFreeB])
    | .seq es =>
      simp only [defFreeB, List.all_eq_true] at h
      simp only [defFree]
      exact defFreeAll_of_forall fun e' he' => ih (h e' he')
    | .if' c t els =>
      cases els with
      | some e' =>
        simp only [defFreeB, Bool.and_eq_true] at h
        simp only [defFree, Bool.and_eq_true]
        exact ⟨⟨ih h.1.1, ih h.1.2⟩, ih h.2⟩
      | none =>
        simp only [defFreeB, Bool.and_eq_true] at h
        simp only [defFree, Bool.and_eq_true]
        exact ⟨⟨ih h.1.1, ih h.1.2⟩, trivial⟩
    | .while' c b =>
      simp only [defFreeB, Bool.and_eq_true] at h
      simp only [defFree, Bool.and_eq_true]
      exact ⟨ih h.1, ih h.2⟩
    | .vasgn _ _ rhs =>
      simp only [defFreeB] at h
      simp only [defFree]
      exact ih h
    | .send r _ args blk =>
      cases r <;> cases blk <;>
        simp only [defFreeB, Bool.and_eq_true, List.all_eq_true] at h
      · have h2 : defFreeAll args = true :=
          defFreeAll_of_forall fun e' he' => ih (h.1.2 e' he')
        simp [defFree, h2]
      · have h2 : defFreeAll args = true :=
          defFreeAll_of_forall fun e' he' => ih (h.1.2 e' he')
        simp [defFree, h2, ih h.2]
      · have h2 : defFreeAll args = true :=
          defFreeAll_of_forall fun e' he' => ih (h.1.2 e' he')
        simp [defFree, h2, ih h.1.1]
      · have h2 : defFreeAll args = true :=
          defFreeAll_of_forall fun e' he' => ih (h.1.2 e' he')
        simp [defFree, h2, ih h.1.1, ih h.2]
    | .block _ _ b =>
      simp only [defFreeB] at h
      simp only [defFree]
      exact ih h
    | .array es =>
      simp only [defFreeB, List.all_eq_true] at h
      simp only [defFree]
      exact defFreeAll_of_forall fun e' he' => ih (h e' he')
    | .ret e =>
      cases e with
      | some e' =>
        simp only [defFreeB] at h
        simp only [defFree]
        exact ih h
      | none => simp [defFree]
    | .cpath base _ =>
      cases base with
      | some b =>
        simp only [defFreeB] at h
        simp only [defFree]
        exact ih h
      | none => simp [defFree]
    | .super' args blk =>
      cases blk with
      | some b =>
        simp only [defFreeB, Bool.and_eq_true, List.all_eq_true] at h
        simp only [defFree, Bool.and_eq_true]
        exact ⟨defFreeAll_of_forall fun e' he' => ih (h.1 e' he'), ih h.2⟩
      | none =>
        simp only [defFreeB, Bool.and_eq_true, List.all_eq_true] at h
        simp only [defFree, Bool.and_eq_true]
        exact ⟨defFreeAll_of_forall fun e' he' => ih (h.1 e' he'), trivial⟩
    | .splat e =>
      cases e with
      | some e' =>
        simp only [defFreeB] at h
        simp only [defFree]
        exact ih h
      | none => simp [defFree]
    | .zsuper blk =>
      cases blk with
      | some b =>
        simp only [defFreeB] at h
        simp only [defFree]
        exact ih h
      | none => simp [defFree]
    | .nxt e =>
      cases e with
      | some e' => simp [defFree]
      | none => simp [defFree]
    | .int _ | .flt _ | .str _ | .sym _ | .tru | .fls | .nil | .self'
    | .var _ _ | .const _ | .casgn _ _ | .cpathAsgn _ _ _ | .vcall _
    | .kwargs _ | .fwd | .yield' _ | .dowhile _ _ | .for' _ _ _
    | .brk _ | .retry' | .redo' | .defs _ _ _ _ | .module' _ _
    | .scopedClass _ _ _ | .scopedModule _ _ _ | .sclass _ _
    | .begin' _ _ _ _ | .alias' _ _ | .undef _ | .defined _
    | .hash _ | .blockpass _ => simp [defFree]

/-- The claim-context guard, decoded (J35). -/
theorem reqClsOkB_sound {cl : SemClaim} {ctx : JCtx} (h : reqClsOkB cl ctx = true) :
    ∀ cn, cl.reqCls = some cn →
      ctx.cls = cn ∧ ctx.inClassBody = true ∧ ctx.inBlock = false := by
  intro cn hcn
  unfold reqClsOkB at h
  rw [hcn] at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

set_option maxHeartbeats 1600000 in
/-- **J31 — the canonical-claim pins.** A checked judgment at an out-of-fragment
    head can only have come from the `.semantic` node (every other node's
    expression pattern is a `fragHead`-true shape, and the `.sub` node is guarded),
    so its result is the canonical one. This is what supplies the `JudgeSeq`
    coupling premises in `check_sound_all` — the checker needs no extra guards. -/
theorem check_fragHead_false {n : Nat} {A : SemAxioms} {d : Deriv} {D : Decls}
    {Γ : Env} {e : Expr} {top : Bool} {ctx : JCtx} {τ : Ty} {Γ' : Env} {D' : Decls}
    (h : RubyCore.Judgment.check n A d D Γ e top ctx = some (τ, Γ', D'))
    (hf : fragHead e = false) :
    ∃ cl ∈ A, cl.e = e ∧ τ = cl.τ ∧ Γ' = Γ ∧ D' = addRows D cl.rows ∧
      (cl.rows = [] ∨ ctx.meth = none) ∧
      (∀ cn, cl.reqCls = some cn →
        ctx.cls = cn ∧ ctx.inClassBody = true ∧ ctx.inBlock = false) ∧
      (∀ r ∈ cl.rows, declaresName D r.2.1 = false) := by
  match n with
  | 0 => exact absurd h (by simp [RubyCore.Judgment.check])
  | n + 1 =>
    match d, e with
    | .semantic i, e =>
      simp only [RubyCore.Judgment.check] at h
      split at h
      · next cl hi =>
        split at h
        · next hguard =>
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
            Bool.and_eq_true] at hguard
          obtain ⟨⟨⟨⟨hg1, hg2⟩, hg3⟩, hg4⟩, hg5⟩ := hguard
          have hreq := reqClsOkB_sound hg4
          have hfr : ∀ r ∈ cl.rows, declaresName D r.2.1 = false := by
            intro r hr
            have := List.all_eq_true.mp hg5 r hr
            simpa using this
          simp only [Bool.or_eq_true, List.isEmpty_iff,
            Option.isNone_iff_eq_none] at hg3
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨cl, List.mem_of_getElem? hi, exprEqB_sound hg1, rfl, rfl,
            rfl, hg3, hreq, hfr⟩
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    | .sub d' σ Γ'', e =>
      simp [RubyCore.Judgment.check, hf] at h
      | .int, .int _ => simp [fragHead] at hf
      | .flt, .flt _ => simp [fragHead] at hf
      | .str, .str _ => simp [fragHead] at hf
      | .sym, .sym _ => simp [fragHead] at hf
      | .tru, .tru => simp [fragHead] at hf
      | .fls, .fls => simp [fragHead] at hf
      | .nil, .nil => simp [fragHead] at hf
      | .self, .self' => simp [fragHead] at hf
      | .varLvar, .var .lvar _ => simp [fragHead] at hf
      | .vasgnLvar _, .vasgn .lvar _ _ => simp [fragHead] at hf
      | .seq _, .seq _ => simp [fragHead] at hf
      | .const, .const _ => simp [fragHead] at hf
      | .cpathAbs, .cpath none _ => simp [fragHead] at hf
      | .cpathScoped _, .cpath (some _) _ => simp [fragHead] at hf
      | .varIvar, .var .ivar _ => simp [fragHead] at hf
      | .varGvar, .var .gvar _ => simp [fragHead] at hf
      | .vasgnIvar _, .vasgn .ivar _ _ => simp [fragHead] at hf
      | .vasgnGvar _, .vasgn .gvar _ _ => simp [fragHead] at hf
      | .array _, .array _ => simp [fragHead] at hf
      | .ifElse _ _ _ _ _, .if' _ _ (some _) => simp [fragHead] at hf
      | .ifNone _ _ _ _, .if' _ _ none => simp [fragHead] at hf
      | .ifNarrowElse _ _ _ _, .if' _ _ (some _) => simp [fragHead] at hf
      | .ifNarrowNone _ _ _, .if' _ _ none => simp [fragHead] at hf
      | .while' _ _ _, .while' _ _ => simp [fragHead] at hf
      | .vcall, .vcall _ => simp [fragHead] at hf
      | .send _ _, .send _ _ _ none => simp [fragHead] at hf
      | .defDecl _ _ _ _, .def' _ _ _ => simp [fragHead] at hf
      | .defPromote _, .def' _ _ _ => simp [fragHead] at hf
      | .classTop _, .class' _ none _ => simp [fragHead] at hf

set_option maxHeartbeats 4000000 in
/-- **Adequacy, all five checkers at once** — one fuel induction. -/
theorem check_sound_all : ∀ (n : Nat),
    (∀ {d D Γ e top ctx τ Γ' D'}, RubyCore.Judgment.check n A d D Γ e top ctx = some (τ, Γ', D') →
       Judge A D Γ e top ctx τ Γ' D') ∧
    (∀ {dr D Γ ro top ctx τ Γ' D'}, checkRecv n A dr D Γ ro top ctx = some (τ, Γ', D') →
       JudgeRecv A D Γ ro top ctx τ Γ' D') ∧
    (∀ {ds D Γ es top ctx τ Γ' D'}, checkSeq n A ds D Γ es top ctx = some (τ, Γ', D') →
       JudgeSeq A D Γ es top ctx τ Γ' D') ∧
    (∀ {da D Γ es top ctx τs Γ' D'}, checkArgs n A da D Γ es top ctx = some (τs, Γ', D') →
       JudgeArgs A D Γ es top ctx τs Γ' D') ∧
    (∀ {da D Γ es top ctx Γ' D'}, checkElems n A da D Γ es top ctx = some (Γ', D') →
       JudgeElems A D Γ es top ctx Γ' D') := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      (intros; simp [RubyCore.Judgment.check, checkRecv, checkSeq, checkArgs,
        checkElems] at *)
  | succ n ih =>
    obtain ⟨ihc, ihr, ihs, iha, ihe⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro d D Γ e top ctx τ Γ' D' h
      match d, e with
      | .int, .int _ =>
        simp only [RubyCore.Judgment.check, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .int
      | .flt, .flt _ =>
        simp only [RubyCore.Judgment.check, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .flt
      | .str, .str _ =>
        simp only [RubyCore.Judgment.check, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .str
      | .sym, .sym _ =>
        simp only [RubyCore.Judgment.check, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .sym
      | .tru, .tru =>
        simp only [RubyCore.Judgment.check, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .tru
      | .fls, .fls =>
        simp only [RubyCore.Judgment.check, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .fls
      | .nil, .nil =>
        simp only [RubyCore.Judgment.check, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .nil
      | .semantic i, e =>
        simp only [RubyCore.Judgment.check] at h
        split at h
        · next cl hi =>
          split at h
          · next hguard =>
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
              Bool.and_eq_true] at hguard
            obtain ⟨⟨⟨⟨hg1, hg2⟩, hg3⟩, hg4⟩, hg5⟩ := hguard
            have hreq := reqClsOkB_sound hg4
            have hfr : ∀ r ∈ cl.rows, declaresName D r.2.1 = false := by
              intro r hr
              have := List.all_eq_true.mp hg5 r hr
              simpa using this
            simp only [Bool.or_eq_true, List.isEmpty_iff,
              Option.isNone_iff_eq_none] at hg3
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            have hcle : cl.e = e := exprEqB_sound hg1
            subst hcle
            exact .semantic (List.mem_of_getElem? hi) (by simpa using hg2) hreq hfr
              hg3
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      | .self, .self' =>
        simp only [RubyCore.Judgment.check] at h
        split at h
        · next cc hcc =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact .self hcc
        · exact absurd h (by simp)
      | .varLvar, .var .lvar x =>
        simp only [RubyCore.Judgment.check] at h
        split at h
        · next τ0 hget =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact .varLvar hget
        · exact absurd h (by simp)
      | .vasgnLvar rhs, .vasgn .lvar x e' =>
        simp only [RubyCore.Judgment.check] at h
        split at h
        · exact absurd h (by simp)
        · next hib =>
          split at h
          · next τ0 Γ₁ D₁ hr =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact .vasgnLvar (by simpa using hib) (ihc hr)
          · exact absurd h (by simp)
      | .seq ds, .seq es =>
        simp only [RubyCore.Judgment.check] at h
        exact .seq (ihs h)
      | .const, .const nm =>
        simp only [RubyCore.Judgment.check] at h
        split at h
        · next τ0 hre =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact .const hre
        · exact absurd h (by simp)
      | .cpathAbs, .cpath none nm =>
        simp only [RubyCore.Judgment.check] at h
        split at h
        · next τ0 hre =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact .cpathAbs hre
        · exact absurd h (by simp)
      | .cpathScoped base, .cpath (some b) nm =>
        simp only [RubyCore.Judgment.check] at h
        split at h
        · next cname Γ₁ D₁ hb =>
          split at h
          · next τ0 hsco =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact .cpathScoped (ihc hb) hsco
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      | .varIvar, .var .ivar x =>
        simp only [RubyCore.Judgment.check] at h
        split at h
        · next cc hcc =>
          split at h
          · next σ hiv =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact .varIvar hcc hiv
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      | .varGvar, .var .gvar x =>
        simp only [RubyCore.Judgment.check] at h
        split at h
        · next hpg =>
          split at h
          · next σ hgt =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact .varGvar hpg hgt
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      | .vasgnIvar rhs, .vasgn .ivar x e' =>
        simp only [RubyCore.Judgment.check] at h
        split at h
        · next cc hcc =>
          split at h
          · next τ0 Γ₁ D₁ hr0 =>
            split at h
            · next σ hiv =>
              split at h
              · next hsj =>
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                exact .vasgnIvarDecl hcc (ihc hr0) hiv (subJb_sound hsj)
              · exact absurd h (by simp)
            · next hiv =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              exact .vasgnIvarFresh hcc (ihc hr0) hiv
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      | .vasgnGvar rhs, .vasgn .gvar x e' =>
        simp only [RubyCore.Judgment.check] at h
        split at h
        · next hpg =>
          split at h
          · next τ0 Γ₁ D₁ hr0 =>
            split at h
            · next σ hgt =>
              split at h
              · next hsj =>
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                exact .vasgnGvar hpg (ihc hr0) hgt (subJb_sound hsj)
              · exact absurd h (by simp)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      | .array ds, .array es =>
        simp only [RubyCore.Judgment.check] at h
        split at h
        · next Γ0 D0 he0 =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact .array (ihe he0)
        · exact absurd h (by simp)
      | .ifElse dc dt de τj Γc, .if' cnd t (some els) =>
        simp only [RubyCore.Judgment.check] at h
        split at h
        all_goals try (simp at h; done)
        split at h
        all_goals try (simp at h; done)
        rename_i hc0
        split at h
        all_goals try (simp at h; done)
        rename_i ht0
        split at h
        all_goals try (simp at h; done)
        rename_i he0
        split at h
        all_goals try (simp at h; done)
        rename_i hguards
        simp only [Bool.and_eq_true, beq_iff_eq] at hguards
        obtain ⟨⟨⟨⟨heq, hjt⟩, hje⟩, hct⟩, hce⟩ := hguards
        subst heq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .ifElse (ihc hc0) (ihc ht0) (ihc he0)
          (subJb_sound hjt) (subJb_sound hje)
          (subEnvB_sound hct) (subEnvB_sound hce)
      | .ifNone dc dt τj Γc, .if' cnd t none =>
        simp only [RubyCore.Judgment.check] at h
        split at h
        all_goals try (simp at h; done)
        split at h
        all_goals try (simp at h; done)
        rename_i hc0
        split at h
        all_goals try (simp at h; done)
        rename_i ht0
        split at h
        all_goals try (simp at h; done)
        rename_i hguards
        simp only [Bool.and_eq_true, beq_iff_eq] at hguards
        obtain ⟨⟨⟨⟨heq, hjt⟩, hjn⟩, hct⟩, hcΓ⟩ := hguards
        subst heq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .ifNone (ihc hc0) (ihc ht0)
          (subJb_sound hjt) (subJb_sound hjn)
          (subEnvB_sound hct) (subEnvB_sound hcΓ)
      | .ifNarrowElse dt de τj Γc, .if' (.var .lvar x) t (some els) =>
        simp only [RubyCore.Judgment.check] at h
        split at h
        all_goals try (simp at h; done)
        rename_i hget
        split at h
        all_goals try (simp at h; done)
        rename_i ht0
        split at h
        all_goals try (simp at h; done)
        rename_i he0
        split at h
        all_goals try (simp at h; done)
        rename_i hguards
        simp only [Bool.and_eq_true, beq_iff_eq] at hguards
        obtain ⟨⟨⟨⟨heq, hjt⟩, hje⟩, hct⟩, hce⟩ := hguards
        subst heq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .ifNarrowElse hget (ihc ht0) (ihc he0)
          (subJb_sound hjt) (subJb_sound hje)
          (subEnvB_sound hct) (subEnvB_sound hce)
      | .ifNarrowNone dt τj Γc, .if' (.var .lvar x) t none =>
        simp only [RubyCore.Judgment.check] at h
        split at h
        all_goals try (simp at h; done)
        rename_i hget
        split at h
        all_goals try (simp at h; done)
        rename_i ht0
        split at h
        all_goals try (simp at h; done)
        rename_i hguards
        simp only [Bool.and_eq_true, beq_iff_eq] at hguards
        obtain ⟨⟨⟨⟨heq, hjt⟩, hjn⟩, hct⟩, hcΓ⟩ := hguards
        subst heq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .ifNarrowNone hget (ihc ht0)
          (subJb_sound hjt) (subJb_sound hjn)
          (subEnvB_sound hct) (subEnvB_sound hcΓ)
      | .while' Γl dc db, .while' cnd body =>
        simp only [RubyCore.Judgment.check] at h
        split at h
        · next hentry =>
          split at h
          · next τc Γ₁ Dc hc0 =>
            split at h
            · next hg1 =>
              simp only [Bool.and_eq_true, beq_iff_eq] at hg1
              obtain ⟨rfl, hs1⟩ := hg1
              split at h
              · next τb Γ₂ Db hb0 =>
                split at h
                · next hg2 =>
                  simp only [Bool.and_eq_true, beq_iff_eq] at hg2
                  obtain ⟨rfl, hs2⟩ := hg2
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl, rfl⟩ := h
                  exact .while' (subEnvB_sound hentry) (ihc hc0) (subEnvB_sound hs1)
                    (ihc hb0) (subEnvB_sound hs2)
                · exact absurd h (by simp)
              · exact absurd h (by simp)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      | .vcall, .vcall mname =>
        simp only [RubyCore.Judgment.check] at h
        split at h
        · next cc hcc =>
          split at h
          · next τret hsg =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact .vcall hcc hsg
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      | .send dr da, .send recvO mname args none =>
        simp only [RubyCore.Judgment.check] at h
        split at h
        · next τr Γ₁ D₁ hr0 =>
          split at h
          · next τs Γ₂ D₂ ha0 =>
            split at h
            · next ps τret hsg =>
              split at h
              · next hsub =>
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                exact .send (ihr hr0) (iha ha0) hsg (subJsb_sound hsub)
              · exact absurd h (by simp)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      | .defDecl τs σ bs db, .def' name ps body =>
        simp only [RubyCore.Judgment.check] at h
        split at h
        · exact absurd h (by simp)
        · next hguards =>
          simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, beq_iff_eq,
            decide_eq_true_eq, Decidable.not_not] at hguards
          split at h
          · next τb Γb Db hb0 =>
            split at h
            · next hg2 =>
              simp only [Bool.and_eq_true, beq_iff_eq] at hg2
              obtain ⟨rfl, hjb⟩ := hg2
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              exact .defDecl hguards.1.1.1
                ⟨by simpa using hguards.1.1.2, by simpa using hguards.1.2⟩
                (by simpa using hguards.2)
                (ihc hb0) (subJb_sound hjb)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
      | .defPromote db, .def' name [] body =>
        simp only [RubyCore.Judgment.check] at h
        split at h
        · exact absurd h (by simp)
        · next hguards =>
          simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hguards
          obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hfresh, hha⟩, hdm⟩, htop⟩, hinit⟩, hreop⟩, hgroundc⟩,
            hdf⟩, hret⟩, hloop⟩, hblk⟩ := hguards
          split at h
          · next τb Γb Db hb0 =>
            split at h
            · next hg2 =>
              simp only [beq_iff_eq] at hg2
              subst hg2
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              refine .defPromote hfresh ⟨?_, ?_⟩ (ihc hb0) htop ?_ ?_ hgroundc
                (defFreeB_sound (n := n) ?_) ?_ ?_ hblk
              · intro hq
                rw [hq] at hha
                simp at hha
              · intro hq
                rw [hq] at hdm
                simp at hdm
              · intro hq
                rw [hq] at hinit
                simp at hinit
              · simpa using hreop
              · simpa using hdf
              · simpa using hret
              · simpa using hloop
            · exact absurd h (by simp)
          · exact absurd h (by simp)
      | .classTop db, .class' name none body =>
        simp only [RubyCore.Judgment.check] at h
        split at h
        · next hguards =>
          simp only [Bool.and_eq_true] at hguards
          split at h
          · next τ0 Γb Db hb0 =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            have htop : top = true := hguards.2
            subst htop
            exact .classTop hguards.1 (ihc hb0)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      | .sub d' σ Γ'', e =>
        simp only [RubyCore.Judgment.check] at h
        split at h
        case isFalse => exact absurd h (by simp)
        split at h
        · next τ0 Γ0 D0 h0 =>
          split at h
          · next hg2 =>
            simp only [Bool.and_eq_true] at hg2
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact .sub (ihc h0) (subJb_sound hg2.1) (subEnvB_sound hg2.2)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
    · intro dr D Γ ro top ctx τ Γ' D' h
      match dr, ro with
      | .self, none =>
        simp only [checkRecv] at h
        split at h
        · next cc hcc =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact .self hcc
        · exact absurd h (by simp)
      | .expl d, some r =>
        simp only [checkRecv] at h
        exact .expl (ihc h)
    · intro ds D Γ es top ctx τ Γ' D' h
      match ds, es with
      | .nil, [] =>
        simp only [checkSeq, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .nil
      | .single d, [e] =>
        simp only [checkSeq] at h
        by_cases hfe : fragHead e = true
        · exact .single (ihc h) (hcpl := fun hh => Bool.noConfusion (hfe.symm.trans hh))
        · replace hfe : fragHead e = false := by simpa using hfe
          exact .single (ihc h) (hcpl := fun _ => check_fragHead_false h hfe)
      | .cons d rest, e :: e₂ :: es' =>
        simp only [checkSeq] at h
        split at h
        · next τ1 Γ₁ D₁ h1 =>
          by_cases hfe : fragHead e = true
          · exact .cons (ihc h1) (ihs h)
              (hcpl := fun hh => Bool.noConfusion (hfe.symm.trans hh))
          · replace hfe : fragHead e = false := by simpa using hfe
            exact .cons (ihc h1) (ihs h) (hcpl := fun _ => check_fragHead_false h1 hfe)
        · exact absurd h (by simp)
    · intro da D Γ es top ctx τs Γ' D' h
      match da, es with
      | .nil, [] =>
        simp only [checkArgs, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .nil
      | .cons d rest, e :: es' =>
        simp only [checkArgs] at h
        split at h
        · next τ1 Γ₁ D₁ h1 =>
          split at h
          · next τs' Γ'' D'' h2 =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact .cons (ihc h1) (iha h2)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
    · intro da D Γ es top ctx Γ' D' h
      match da, es with
      | .nil, [] =>
        simp only [checkElems, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .nil
      | .cons d rest, e :: es' =>
        simp only [checkElems] at h
        split at h
        · next τ1 Γ₁ D₁ h1 =>
          exact .cons (ihc h1) (ihe h)
        · exact absurd h (by simp)

/-- The headline adequacy statement. -/
theorem check_sound {n : Nat} {d : Deriv} {D : Decls} {Γ : Env} {e : Expr}
    {top : Bool} {ctx : JCtx} {τ : Ty} {Γ' : Env} {D' : Decls}
    (h : RubyCore.Judgment.check n A d D Γ e top ctx = some (τ, Γ', D')) :
    Judge A D Γ e top ctx τ Γ' D' := (check_sound_all n).1 h

/-! ## The composed pipeline: `validateJ` accepts ⇒ no reachable type-stuck outcome -/

/-- **J38b: `tableOk_declsOkJ` at a constant-extended base.** The certificate's
    constant claims land as the appended halves of `constExtend`, one
    `ConstOk`/`ScopedConstOk` residue each; every other conjunct is the same walk
    (`constExtend` touches no other field, so `declFor` and the user-arm
    refutation are unchanged definitionally). A claim shadowed by a base entry is
    inert: `find?` answers the base half first, whose conjunct `hd` supplies. -/
theorem tableOk_declsOkJ_constExtend {A : SemAxioms} {h : Heap}
    {cs : List (String × Ty)} {scs : List ((String × String) × Ty)}
    (ht : TableOk h) (hcls : ClassOk h)
    (hc : ∀ e ∈ cs, ConstOk h e.1 e.2)
    (hsc : ∀ e ∈ scs, ScopedConstOk h e.1.1 e.1.2 e.2) :
    DeclsOkJ A (constExtend baseDecls cs scs) h := by
  have hd : DeclsOkJ A baseDecls h := tableOk_declsOkJ ht hcls
  refine ⟨?_, ?_, hd.2.2.1, ?_, hd.2.2.2.2.1, hd.2.2.2.2.2.1,
    hd.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2⟩
  · -- Rows: `declFor` reads no constant half, so the row set is the base's; the
    -- base's builtin/iterator witnesses are table-free and the user arm is refuted
    -- by `tableOk_declsOkJ`'s own walk (repeated here at the extended index).
    intro τr mname d hdecl
    have hdecl' : declFor baseDecls τr mname = some d := hdecl
    rcases hd.1 τr mname d hdecl' with hb | ⟨mdu, cu, htys, hres, hnm, hconf⟩ | hi
    · exact Or.inl hb
    · rcases htys with heq | ⟨⟨e, he⟩, hcu⟩
      · subst heq
        by_cases hg : cu ∈ groundClassNames
        · exact absurd hdecl' (by simp [declFor, tyClassNames, hg])
        · have hne : ("Integer" == cu) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq]
            intro hq
            exact hg (hq ▸ (by decide))
          exact absurd hdecl'
            (by simp [declFor, tyClassNames, hg, declOf?, declsFor, baseDecls, hne])
      · subst he
        exact absurd hdecl'
          (by simp [declFor, tyClassNames, declOf?, declsFor, baseDecls])
    · exact Or.inr (Or.inr hi)
  · -- Constants: split the appended list.
    intro n τ hn
    have hn' : ((baseDecls.consts ++ cs).find? (·.1 == n)).map (·.2) = some τ := hn
    rw [List.find?_append] at hn'
    cases hbase : baseDecls.consts.find? (·.1 == n) with
    | some e =>
      rw [hbase] at hn'
      exact hd.2.1 n τ (by simpa [constTy?, hbase] using hn')
    | none =>
      rw [hbase] at hn'
      simp only [Option.orElse, Option.map_eq_some_iff] at hn'
      obtain ⟨e, hfind, rfl⟩ := hn'
      have hmem := List.mem_of_find?_eq_some hfind
      have hkey : e.1 = n := by
        have := List.find?_some hfind
        simpa using this
      exact hkey ▸ hc e hmem
  · -- Scoped constants: the same split at the pair key.
    intro cname n τ hn
    have hn' : ((baseDecls.scopedConsts ++ scs).find? (·.1 == (cname, n))).map (·.2)
        = some τ := hn
    rw [List.find?_append] at hn'
    cases hbase : baseDecls.scopedConsts.find? (·.1 == (cname, n)) with
    | some e =>
      rw [hbase] at hn'
      exact hd.2.2.2.1 cname n τ (by simpa [scopedConstTy?, hbase] using hn')
    | none =>
      rw [hbase] at hn'
      simp only [Option.orElse, Option.map_eq_some_iff] at hn'
      obtain ⟨e, hfind, rfl⟩ := hn'
      have hmem := List.mem_of_find?_eq_some hfind
      have hkey : e.1 = (cname, n) := by
        have := List.find?_some hfind
        simpa using this
      have := hsc e hmem
      rw [hkey] at this
      exact this

/-- **The J-certificate theorem** — J2's exit: a *data* certificate (rows +
    constant claims + a derivation tree), one kernel-reduced `Bool`, the
    reachability property. The residue stays the honest hypotheses, exactly as in
    `validate_sound_of_ctl` — one `EntryOkJ` per claimed row, one
    `ConstOk`/`ScopedConstOk` per claimed constant (J38b). -/
theorem validateJ_certifies {c : JCert} {p : Expr} {fuel : Nat}
    (hax : SemAxiomsOk c.semAssumes)
    (h : validateJ c p fuel = true)
    (ha : ∀ r ∈ c.deltaRows,
      EntryOkJ c.semAssumes (c.table p) Boot.initHeap (nomTy r.cls) r.name r.sig)
    (hac : ∀ e ∈ c.deltaConsts, ConstOk Boot.initHeap e.1 e.2 := by
      intro e he; exact absurd (show e ∈ [] from he) (by simp))
    (hasc : ∀ e ∈ c.deltaScopedConsts,
      ScopedConstOk Boot.initHeap e.1.1 e.1.2 e.2 := by
      intro e he; exact absurd (show e ∈ [] from he) (by simp)) :
    ∀ r, ReachableResult (Machine.init p) r → ¬ typeStuck r := by
  unfold validateJ at h
  simp only [Bool.and_eq_true, Option.isSome_iff_exists] at h
  obtain ⟨⟨⟨⟨hg, hgr⟩, hfr⟩, hmf⟩, ⟨τ, Γ', D'⟩, hchk⟩ := h
  have htbl : c.table p = rowFold (c.baseTable p) c.deltaRows := rfl
  refine judge_sound hax ?_ (mfragB_sound hmf) hfr (check_sound hchk)
  rw [htbl] at ha ⊢
  refine DeclsOkJ_of_subDecls
    (show DeclsOkJ c.semAssumes (c.baseTable p) Boot.initHeap from
      tableOk_declsOkJ_constExtend tableOk_initHeap classOk_initHeap hac hasc)
    (subDecls_rowFold c.deltaRows _ hg) ?_
  intro τ0 n0 d0 hnone hsome
  rcases declFor_rowFold_inv c.deltaRows _ hg hsome with ⟨r, hm, hk, rfl, rfl⟩ | hd2
  · have hτ : τ0 = nomTy r.cls := tyClassNames_singleton_inv hk
    subst hτ
    refine ⟨ha r hm, ?_⟩
    have := List.all_eq_true.mp hgr r hm
    exact fun q hq => List.all_eq_true.mp this q hq
  · rw [hd2] at hnone
    exact absurd hnone (by simp)

/-! ## The worked ends, from literal data -/

/-- `egEven`'s certificate as **data**. -/
def egEvenJCert : JCert :=
  { deltaRows := [egEvenRow], deriv := .send (.expl .int) .nil }

theorem egEvenJCert_validates : validateJ egEvenJCert egEven 8 = true := by decide

/-- `1.even?` under a claimed row, certified from a serialized-shape certificate:
    the pipeline `Deriv` → `check` → `Judge` → `judge_sound`, end to end. -/
theorem egEven_data_certified :
    ∀ r, ReachableResult (Machine.init egEven) r → ¬ typeStuck r :=
  validateJ_certifies semAxiomsOk_nil egEvenJCert_validates
    (fun r hm => by
      simp only [egEvenJCert, List.mem_singleton] at hm
      subst hm
      exact entryOkJ_even)

/-- `egUserCall`'s certificate as data — no claimed rows at all: the user row is
    threaded by the derivation's own promotion node. -/
def egUserCallJCert : JCert :=
  { deriv := .classTop (.seq (.cons (.defPromote .int)
      (.single (.send (.expl .str) .nil)))) }

theorem egUserCallJCert_validates :
    validateJ egUserCallJCert Static.egUserCall 12 = true := by decide

/-- The T5 `class_hierarchy` shape, certified from data, unconditionally. -/
theorem egUserCall_data_certified :
    ∀ r, ReachableResult (Machine.init Static.egUserCall) r → ¬ typeStuck r :=
  validateJ_certifies semAxiomsOk_nil egUserCallJCert_validates (fun r hm => by simp [egUserCallJCert] at hm)

/-- **The DRuby pattern, certified**: `x = (true ? 1 : nil); if x then x + 1 else
    0 end` — the local is an optional, the guard narrows it, and the narrowed
    branch dispatches on it. This is T4's flagship shape (the guard-discrimination
    false-positive class the narrowing rules exist to kill), certified from
    certificate data end to end. -/
def egNarrow : Expr :=
  .seq [ .vasgn .lvar "x" (.if' .tru (.int 1) (some .nil)),
         .if' (.var .lvar "x")
           (.send (some (.var .lvar "x")) "+" [.int 1] none)
           (some (.int 0)) ]

def egNarrowJCert : JCert :=
  { deriv := .seq (.cons
      (.vasgnLvar (.ifElse .tru .int .nil (.nilable .int) []))
      (.single (.ifNarrowElse
        (.send (.expl .varLvar) (.cons .int .nil))
        .int .int []))) }

theorem egNarrowJCert_validates : validateJ egNarrowJCert egNarrow 12 = true := by
  decide

theorem egNarrow_certified :
    ∀ r, ReachableResult (Machine.init egNarrow) r → ¬ typeStuck r :=
  validateJ_certifies semAxiomsOk_nil egNarrowJCert_validates (fun r hm => by simp [egNarrowJCert] at hm)

/-! ## The J38b worked end: `Float::INFINITY`, from literal data

Both new rules and both constant channels: `Float` claimed at the toplevel
(`ConstOk` residue, discharged by `constOkB` at the boot heap) and
`Float::INFINITY` claimed scoped (`ScopedConstOk` residue, `scopedConstOkB`) —
the first certificate whose table half is constants rather than rows. -/

def egCpath : Expr := .cpath (some (.const "Float")) "INFINITY"

def egCpathJCert : JCert :=
  { deltaConsts := [("Float", .clsOf "Float")],
    deltaScopedConsts := [(("Float", "INFINITY"), .float)],
    deriv := .cpathScoped .const }

theorem egCpathJCert_validates : validateJ egCpathJCert egCpath 8 = true := by decide

theorem egCpath_data_certified :
    ∀ r, ReachableResult (Machine.init egCpath) r → ¬ typeStuck r :=
  validateJ_certifies semAxiomsOk_nil egCpathJCert_validates
    (fun r hm => by simp [egCpathJCert] at hm)
    (fun e he => by
      simp only [egCpathJCert, List.mem_singleton] at he
      subst he
      exact constOkB_sound (by decide))
    (fun e he => by
      simp only [egCpathJCert, List.mem_singleton] at he
      subst he
      exact scopedConstOkB_sound (by decide))

/-- info: 'RubyCore.Proof.Judgment.egCpath_data_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms egCpath_data_certified

/-! ## The refusal direction, observed

A checker whose accepts are proven sound still owes evidence that it *refuses* —
a validator that answered `true` everywhere would satisfy every theorem above
vacuously at the `decide` sites. One guard per refusal class, each a wrong
certificate for `egNarrow`: the plain `if` node where the branch needs the
narrowed environment (the dispatch on a nilable receiver has no row), a claimed
join that drops the nil branch (`subJb` refuses `nilT ≤ int`), a derivation whose
shape does not match the program, and a claimed row colliding with a base row
(`rowsGuarded`). The JSON boundary's refusal (`derivOfJson` on an unknown node
kind answers a decode *error*, not a crash) is exercised by evaluation rather
than here — the kernel cannot run the `Except` decoder under `#guard`. -/

-- The plain `if` node cannot certify the narrowing program.
def egNarrowBadPlain : JCert :=
  { deriv := .seq (.cons
      (.vasgnLvar (.ifElse .tru .int .nil (.nilable .int) []))
      (.single (.ifElse .varLvar (.send (.expl .varLvar) (.cons .int .nil))
        .int .int []))) }

#guard validateJ egNarrowBadPlain egNarrow 32 == false

-- A join claim that forgets the nil branch is refused.
def egNarrowBadJoin : JCert :=
  { deriv := .seq (.cons
      (.vasgnLvar (.ifElse .tru .int .nil .int []))
      (.single (.ifNarrowElse (.send (.expl .varLvar) (.cons .int .nil))
        .int .int []))) }

#guard validateJ egNarrowBadJoin egNarrow 32 == false

-- A derivation whose shape does not match the program is refused.
def egNarrowBadShape : JCert :=
  { deriv := .seq (.cons (.vasgnLvar (.send (.expl .int) .nil))
      (.single (.ifNarrowElse (.send (.expl .varLvar) (.cons .int .nil))
        .int .int []))) }

#guard validateJ egNarrowBadShape egNarrow 32 == false

-- A claimed row colliding with a base row is refused by `rowsGuarded`…
def clashRow : RowClaim :=
  { cls := "Integer", name := "+", sig := { params := [.int], ret := .int },
    why := .assumed "clash" }

#guard validateJ { deltaRows := [clashRow], deriv := egNarrowJCert.deriv }
  egNarrow 32 == false

-- …while a fresh row rides along fine.
#guard validateJ { deltaRows := [egEvenRow], deriv := egNarrowJCert.deriv }
  egNarrow 32 == true

/-! ## Axiom hygiene -/

/-- info: 'RubyCore.Proof.Judgment.validateJ_certifies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms validateJ_certifies

/-- info: 'RubyCore.Proof.Judgment.egEven_data_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms egEven_data_certified

/-- info: 'RubyCore.Proof.Judgment.egUserCall_data_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms egUserCall_data_certified

/-- info: 'RubyCore.Proof.Judgment.egNarrow_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms egNarrow_certified

end Judgment
end Proof
end RubyCore
