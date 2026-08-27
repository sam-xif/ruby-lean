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

/-- **Adequacy, all four checkers at once** — one fuel induction. -/
theorem check_sound_all : ∀ (n : Nat),
    (∀ {d D Γ e top ctx τ Γ' D'}, RubyCore.Judgment.check n d D Γ e top ctx = some (τ, Γ', D') →
       Judge D Γ e top ctx τ Γ' D') ∧
    (∀ {dr D Γ ro top ctx τ Γ' D'}, checkRecv n dr D Γ ro top ctx = some (τ, Γ', D') →
       JudgeRecv D Γ ro top ctx τ Γ' D') ∧
    (∀ {ds D Γ es top ctx τ Γ' D'}, checkSeq n ds D Γ es top ctx = some (τ, Γ', D') →
       JudgeSeq D Γ es top ctx τ Γ' D') ∧
    (∀ {da D Γ es top ctx τs Γ' D'}, checkArgs n da D Γ es top ctx = some (τs, Γ', D') →
       JudgeArgs D Γ es top ctx τs Γ' D') := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (intros; simp [RubyCore.Judgment.check, checkRecv, checkSeq, checkArgs] at *)
  | succ n ih =>
    obtain ⟨ihc, ihr, ihs, iha⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
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
              exact .defDecl hguards.1.1 (by simpa using hguards.1.2) hguards.2
                (ihc hb0) (subJb_sound hjb)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
      | .defPromote db, .def' name [] body =>
        simp only [RubyCore.Judgment.check] at h
        split at h
        · exact absurd h (by simp)
        · next hguards =>
          simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hguards
          obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hfresh, hha⟩, htop⟩, hinit⟩, hreop⟩, hgroundc⟩,
            hdf⟩, hret⟩, hloop⟩, hblk⟩ := hguards
          split at h
          · next τb Γb Db hb0 =>
            split at h
            · next hg2 =>
              simp only [beq_iff_eq] at hg2
              subst hg2
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              refine .defPromote hfresh ?_ (ihc hb0) htop ?_ ?_ hgroundc
                (defFreeB_sound (n := n) ?_) ?_ ?_ hblk
              · intro hq
                rw [hq] at hha
                simp at hha
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
        exact .single (ihc h)
      | .cons d rest, e :: e₂ :: es' =>
        simp only [checkSeq] at h
        split at h
        · next τ1 Γ₁ D₁ h1 =>
          exact .cons (ihc h1) (ihs h)
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

/-- The headline adequacy statement. -/
theorem check_sound {n : Nat} {d : Deriv} {D : Decls} {Γ : Env} {e : Expr}
    {top : Bool} {ctx : JCtx} {τ : Ty} {Γ' : Env} {D' : Decls}
    (h : RubyCore.Judgment.check n d D Γ e top ctx = some (τ, Γ', D')) :
    Judge D Γ e top ctx τ Γ' D' := (check_sound_all n).1 h

/-! ## The composed pipeline: `validateJ` accepts ⇒ no reachable type-stuck outcome -/

/-- **The J-certificate theorem** — J2's exit: a *data* certificate (rows + a
    derivation tree), one kernel-reduced `Bool`, the reachability property. The
    residue stays the one honest hypothesis, exactly as in
    `validate_sound_of_ctl`. -/
theorem validateJ_certifies {c : JCert} {p : Expr} {fuel : Nat}
    (h : validateJ c p fuel = true)
    (ha : ∀ r ∈ c.deltaRows,
      EntryOkJ (c.table p) Boot.initHeap (nomTy r.cls) r.name r.sig) :
    ∀ r, ReachableResult (Machine.init p) r → ¬ typeStuck r := by
  unfold validateJ at h
  simp only [Bool.and_eq_true, Option.isSome_iff_exists] at h
  obtain ⟨⟨⟨hg, hgr⟩, hmf⟩, ⟨τ, Γ', D'⟩, hchk⟩ := h
  have htbl : c.table p = rowFold (declsOf p) c.deltaRows := rfl
  refine judge_sound ?_ (mfragB_sound hmf) (check_sound hchk)
  rw [htbl] at ha ⊢
  refine DeclsOkJ_of_subDecls declsOkJ_declsOf (subDecls_rowFold c.deltaRows _ hg) ?_
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
  validateJ_certifies egEvenJCert_validates
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
  validateJ_certifies egUserCallJCert_validates (fun r hm => by simp [egUserCallJCert] at hm)

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

end Judgment
end Proof
end RubyCore
