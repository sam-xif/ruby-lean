import RubyCore.Proof.TypeSafety
import RubyCore.Types.Core

/-!
# P0 — static soundness on the fully-typed fragment

`docs/semantics/static-soundness-poc.md`. The claim:

    check P = .accept  →  no reachable outcome is `typeStuck`

proved by handing `Proof.invariant_sound_from` an invariant built from the
checker of `Types/Core.lean`. Nothing here re-derives reachability: the
metatheorem harness (`Proof/TypeSafety.lean:157`) is bad-state-agnostic and
already proved, and this is the first target to reuse `typeStuck`
*unmodified* — no bad-state swap at all.

Note the conclusion is `typeStuck`, not `sorbetStuck`: in a fully-typed
fragment a sig check cannot fire, so the blame carve-out of
`Proof/SorbetSafety.lean` is unnecessary and the *strong* property is what
gets proved (doc §2.1).

## Shape of the invariant

    Inv m  ≡  Flat m ∧ ∃ Γ, LocalsOk Γ m ∧ CtlOk Γ m

`CtlOk`/`KontOk` play the role the doc §4 assigns to `InFragment`: they simply
have **no constructor** for the machine shapes outside the fragment, so the
`stepFn` case analysis discharges those branches by contradiction rather than
by typing work. That is the whole tractability argument, and it is why this
file does not need a separate fragment predicate.
-/

namespace RubyCore
namespace Proof
namespace Static

open Interp
open RubyCore.Types

/-! ## 1. Values and locals -/

/-- The type of a value, where P0 has one. `.ref`/`.flt`/`.sym` have none — the
    fragment allocates no objects, so they never arise. -/
def valueTy? : Value → Option Ty
  | .int _ => some .int
  | .bool _ => some .bool
  | .nil => some .nilT
  | _ => none

def ValueTy (v : Value) (τ : Ty) : Prop := valueTy? v = some τ

/-- **Flat frames.** P0 pushes no frames (no `send`, no blocks), so the machine
    keeps the single toplevel frame `initOn` builds. Assuming it here is what
    lets `getLocal`/`setLocal` — which in general walk the `captured` chain —
    reduce to list operations on one frame. P1 pays this back when `send`
    arrives. -/
def Flat (m : Machine) : Prop :=
  m.stack = [0] ∧ m.frames.size = 1 ∧ (m.frames.getD 0 default).captured = none

/-- The locals of the one frame. -/
def theLocals (m : Machine) : List (String × Value) :=
  (m.frames.getD 0 default).locals

/-- Every variable the environment types holds a value of that type. Stated
    against `m.getLocal` — what the interpreter actually reads — not against the
    list representation. -/
def LocalsOk (Γ : Env) (m : Machine) : Prop :=
  ∀ x τ, envGet? Γ x = some τ → ValueTy (m.getLocal x) τ

/-! ### 1.1 `getLocal`/`setLocal` under `Flat` -/

theorem getLocal_flat {m : Machine} (hf : Flat m) (x : String) :
    m.getLocal x =
      match (theLocals m).find? (·.1 == x) with
      | some (_, v) => v
      | none => .nil := by
  obtain ⟨hs, hsz, hc⟩ := hf
  unfold Machine.getLocal
  rw [hs, hsz]
  unfold Machine.getLocal.go
  simp only [List.headD, theLocals, hc]
  rfl

theorem find?_filter_ne {α : Type} (l : List (String × α)) {x y : String}
    (hxy : ¬ (y = x)) :
    (l.filter (·.1 != x)).find? (·.1 == y) = l.find? (·.1 == y) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases hax : a.1 = x
    · have h1 : (a.1 != x) = false := by simp [hax]
      have h2 : (a.1 == y) = false := by
        simp only [beq_eq_false_iff_ne]; rw [hax]; exact fun h => hxy h.symm
      simp [List.filter, List.find?, h1, h2, ih]
    · have h1 : (a.1 != x) = true := by simp [hax]
      simp [List.filter, List.find?, h1, ih]

/-- With no captured chain, `setLocal`'s owner search returns the start frame on
    both branches. -/
theorem setLocal_owner_zero {m : Machine}
    (hc : (m.frames.getD 0 default).captured = none) (x : String) (fuel : Nat) :
    Machine.setLocal.owner m x 0 0 (fuel + 1) = 0 := by
  unfold Machine.setLocal.owner
  simp only [hc]
  split <;> rfl

/-- Under `Flat`, the update is a plain list prepend-and-filter on the one
    frame. -/
theorem setLocal_frame {m : Machine} (hf : Flat m) (x : String) (v : Value) :
    ((m.setLocal x v).frames.getD 0 default) =
      { (m.frames.getD 0 default) with
        locals := (x, v) :: (theLocals m).filter (·.1 != x) } := by
  obtain ⟨hs, hsz, hc⟩ := hf
  unfold Machine.setLocal
  simp only [hs, List.headD, setLocal_owner_zero hc x m.frames.size, theLocals]
  simp [Array.getD, hsz]

theorem Flat.setLocal {m : Machine} (hf : Flat m) (x : String) (v : Value) :
    Flat (m.setLocal x v) := by
  have h := setLocal_frame hf x v
  obtain ⟨hs, hsz, hc⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · simpa [Machine.setLocal] using hs
  · simpa [Machine.setLocal] using hsz
  · rw [h]; exact hc

/-- The one substantive fact about locals: assignment updates exactly `x`. -/
theorem getLocal_setLocal {m : Machine} (hf : Flat m) (x y : String) (v : Value) :
    (m.setLocal x v).getLocal y = if y = x then v else m.getLocal y := by
  rw [getLocal_flat (Flat.setLocal hf x v) y, getLocal_flat hf y]
  simp only [theLocals, setLocal_frame hf x v]
  by_cases hyx : y = x
  · subst hyx; simp [List.find?]
  · have hne : ((x, v).1 == y) = false := by
      simp only [beq_eq_false_iff_ne]; exact fun h => hyx h.symm
    simp only [List.find?, hne, if_neg hyx]
    rw [find?_filter_ne _ hyx]

/-! ## 2. Typing the machine

`KontOk Γ τ k` reads: *the in-flight value has type `τ`, the environment is
`Γ`, and `k` is a well-typed continuation.* There is one constructor per
admitted `Kont` — five out of the machine's 48 (`Machine.lean:140`) — and the
absence of the other 43 is what makes preservation's case analysis collapse.
-/

/-- A `while` whose condition and body are both **environment-stable** at `Γ`.
    The loop re-enters the condition with whatever the body leaves, so without
    stability there is no single `Γ` to index the two loop konts by. -/
def LoopOk (Γ : Env) (c body : Expr) : Prop :=
  (∃ τc, infer Γ c = some (τc, Γ)) ∧ (∃ τb, infer Γ body = some (τb, Γ))

inductive KontOk : Env → Ty → List Kont → Prop where
  /-- Empty stack: the in-flight value is the program's result. -/
  | nil {Γ τ} : KontOk Γ τ []
  /-- `seqK []` yields the in-flight value unchanged (`Interp.lean:1957`). -/
  | seqNil {Γ τ k} : KontOk Γ τ k → KontOk Γ τ (.seqK [] :: k)
  /-- `seqK (e :: es)` discards the in-flight value and runs the rest. -/
  | seqCons {Γ τ e es τ' Γ' k} :
      inferSeq Γ (e :: es) = some (τ', Γ') → KontOk Γ' τ' k →
      KontOk Γ τ (.seqK (e :: es) :: k)
  /-- Assignment binds `x` at the in-flight type and re-yields the value. -/
  | asgn {Γ τ x k} :
      KontOk (envSet Γ x τ) τ k → KontOk Γ τ (.asgnK .lvar x :: k)
  /-- The in-flight value is the condition; either branch may run next, so the
      join must be the one `inferIf` computed. -/
  | ifK {Γ τ t els τ' Γ' k} :
      inferIf Γ t els = some (τ', Γ') → KontOk Γ' τ' k →
      KontOk Γ τ (.ifK t els :: k)
  | whileCond {Γ τ c body k} :
      LoopOk Γ c body → KontOk Γ .nilT k → KontOk Γ τ (.whileCondK c body :: k)
  | whileBody {Γ τ c body k} :
      LoopOk Γ c body → KontOk Γ .nilT k → KontOk Γ τ (.whileBodyK c body :: k)

/-- The control component. `.jump` is excluded outright: `break`/`next`/`return`
    are not in the fragment, so no step can produce one. -/
def CtlOk (Γ : Env) (m : Machine) : Prop :=
  match m.ctl with
  | .eval e => ∃ τ Γ', infer Γ e = some (τ, Γ') ∧ KontOk Γ' τ m.kont
  | .value v => ∃ τ, ValueTy v τ ∧ KontOk Γ τ m.kont
  | .jump _ => False

/-- **The invariant** handed to `invariant_sound_from`. -/
def Inv (m : Machine) : Prop :=
  Flat m ∧ ∃ Γ, LocalsOk Γ m ∧ CtlOk Γ m

/-! ### 2.1 Environment update, and its agreement with `setLocal` -/

theorem envGet?_nil (y : String) : envGet? ([] : Env) y = none := rfl

theorem envGet?_cons (z : String) (σ : Ty) (Γ : Env) (y : String) :
    envGet? ((z, σ) :: Γ) y = if z = y then some σ else envGet? Γ y := by
  by_cases h : z = y
  · subst h; simp [envGet?, List.find?]
  · have hb : (z == y) = false := by simpa using h
    simp [envGet?, List.find?, hb, h]

theorem envSet_nil (x : String) (τ : Ty) : envSet [] x τ = [(x, τ)] := rfl

theorem envSet_cons (z : String) (σ : Ty) (Γ : Env) (x : String) (τ : Ty) :
    envSet ((z, σ) :: Γ) x τ =
      if z = x then (x, τ) :: Γ else (z, σ) :: envSet Γ x τ := by
  simp only [envSet, beq_iff_eq]

theorem envGet?_set (Γ : Env) (x y : String) (τ : Ty) :
    envGet? (envSet Γ x τ) y = if y = x then some τ else envGet? Γ y := by
  induction Γ with
  | nil =>
    rw [envSet_nil, envGet?_cons, envGet?_nil]
    by_cases h : y = x
    · subst h; simp
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]
  | cons a Γ ih =>
    obtain ⟨z, σ⟩ := a
    rw [envSet_cons]
    by_cases hzx : z = x
    · subst hzx
      rw [if_pos rfl, envGet?_cons, envGet?_cons]
      by_cases hyz : y = z
      · subst hyz; simp
      · rw [if_neg hyz, if_neg (fun hh => hyz hh.symm), if_neg (fun hh => hyz hh.symm)]
    · rw [if_neg hzx, envGet?_cons, envGet?_cons, ih]
      by_cases hzy : z = y
      · subst hzy
        rw [if_pos rfl, if_pos rfl, if_neg (fun hh => hzx hh)]
      · rw [if_neg hzy, if_neg hzy]

theorem LocalsOk_setLocal {m : Machine} {Γ : Env} {x : String} {τ : Ty} {v : Value}
    (hf : Flat m) (hl : LocalsOk Γ m) (hv : ValueTy v τ) :
    LocalsOk (envSet Γ x τ) (m.setLocal x v) := by
  intro y σ hg
  rw [envGet?_set] at hg
  rw [getLocal_setLocal hf x y v]
  by_cases hyx : y = x
  · rw [if_pos hyx] at hg ⊢
    rw [Option.some.injEq] at hg
    subst hg; exact hv
  · rw [if_neg hyx] at hg ⊢
    exact hl y σ hg

/-! ### 2.2 `Flat` survives the fragment's frame-preserving updates -/

theorem Flat.withCtl {m : Machine} (hf : Flat m) (c : Ctl) :
    Flat (Interp.withCtl m c) := hf

theorem Flat.withKont {m : Machine} (hf : Flat m) (c : Ctl) (k : Kont) :
    Flat (Interp.withKont m c k) := hf

theorem LocalsOk.withCtl {m : Machine} {Γ : Env} (hf : Flat m) (hl : LocalsOk Γ m)
    (c : Ctl) : LocalsOk Γ (Interp.withCtl m c) := by
  intro x τ hg
  rw [getLocal_flat (Flat.withCtl hf c) x]
  have h := hl x τ hg
  rwa [getLocal_flat hf x] at h

theorem LocalsOk.withKont {m : Machine} {Γ : Env} (hf : Flat m) (hl : LocalsOk Γ m)
    (c : Ctl) (k : Kont) : LocalsOk Γ (Interp.withKont m c k) := by
  intro x τ hg
  rw [getLocal_flat (Flat.withKont hf c k) x]
  have h := hl x τ hg
  rwa [getLocal_flat hf x] at h

/-- `Flat` and `LocalsOk` see only `stack`/`frames`, so any update that leaves
    those alone (`ctl`, `kont`) transports both. -/
theorem Flat_congr {m m' : Machine} (hs : m'.stack = m.stack)
    (hfr : m'.frames = m.frames) (hf : Flat m) : Flat m' := by
  obtain ⟨a, b, c⟩ := hf
  exact ⟨by rw [hs, a], by rw [hfr, b], by rw [hfr]; exact c⟩

theorem LocalsOk_congr {m m' : Machine} (hf : Flat m) (hf' : Flat m')
    (hfr : m'.frames = m.frames) {Γ : Env} (hl : LocalsOk Γ m) : LocalsOk Γ m' := by
  intro x τ hg
  rw [getLocal_flat hf' x, theLocals, hfr]
  have h := hl x τ hg
  rwa [getLocal_flat hf x, theLocals] at h

/-! ### 2.3 Building `Inv` for the machines the fragment steps to -/

theorem inv_eval {m : Machine} {Γ : Env} {e : Expr} {τ : Ty} {Γ' : Env}
    (hf : Flat m) (hl : LocalsOk Γ m)
    (hinf : infer Γ e = some (τ, Γ')) (hk : KontOk Γ' τ m.kont) :
    Inv (withCtl m (.eval e)) :=
  ⟨Flat.withCtl hf _, Γ, LocalsOk.withCtl hf hl _, ⟨τ, Γ', hinf, hk⟩⟩

theorem inv_value {m : Machine} {Γ : Env} {v : Value} {τ : Ty}
    (hf : Flat m) (hl : LocalsOk Γ m) (hv : ValueTy v τ) (hk : KontOk Γ τ m.kont) :
    Inv (withCtl m (.value v)) :=
  ⟨Flat.withCtl hf _, Γ, LocalsOk.withCtl hf hl _, ⟨τ, hv, hk⟩⟩

theorem inv_push {m : Machine} {Γ : Env} {e : Expr} {τ : Ty} {Γ' : Env} {k : Kont}
    (hf : Flat m) (hl : LocalsOk Γ m)
    (hinf : infer Γ e = some (τ, Γ')) (hk : KontOk Γ' τ (k :: m.kont)) :
    Inv (withKont m (.eval e) k) :=
  ⟨Flat.withKont hf _ _, Γ, LocalsOk.withKont hf hl _ _, ⟨τ, Γ', hinf, hk⟩⟩

/-! ## 3. Progress and preservation, in one case analysis

`StepOk` bundles both obligations so the 48-way `Kont` split and the ~40-way
`Expr` split are each walked **once**: `.next` carries preservation, `.done` is
a legitimate halt, and every remaining `StepResult` — crucially `.uncaught` —
is `False`, which is exactly progress.
-/

def StepOk : StepResult → Prop
  | .next m' => Inv m'
  | .done _ _ => True
  | _ => False

theorem step_ok {m : Machine} (h : Inv m) : StepOk (stepFn m) := by
  obtain ⟨hf, Γ, hl, hc⟩ := h
  unfold CtlOk at hc
  rcases hctl : m.ctl with e | v | j
  · -- ## control = eval e
    rw [hctl] at hc
    obtain ⟨τ, Γ', hinf, hk⟩ := hc
    simp only [stepFn, hctl]
    cases e <;> try (simp only [infer] at hinf; contradiction)
    case int n =>
      simp only [infer, Option.some.injEq, Prod.mk.injEq] at hinf
      obtain ⟨rfl, rfl⟩ := hinf
      exact inv_value hf hl rfl hk
    case tru =>
      simp only [infer, Option.some.injEq, Prod.mk.injEq] at hinf
      obtain ⟨rfl, rfl⟩ := hinf
      exact inv_value hf hl rfl hk
    case fls =>
      simp only [infer, Option.some.injEq, Prod.mk.injEq] at hinf
      obtain ⟨rfl, rfl⟩ := hinf
      exact inv_value hf hl rfl hk
    case nil =>
      simp only [infer, Option.some.injEq, Prod.mk.injEq] at hinf
      obtain ⟨rfl, rfl⟩ := hinf
      exact inv_value hf hl rfl hk
    case var k x =>
      cases k
      case lvar =>
        simp only [infer, Option.map_eq_some_iff] at hinf
        obtain ⟨σ, hg, heq⟩ := hinf
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact inv_value hf hl (hl x _ hg) hk
      all_goals (simp only [infer] at hinf; contradiction)
    case vasgn k x rhs =>
      cases k
      case lvar =>
        simp only [infer] at hinf
        split at hinf
        · rename_i σ Γ₁ hrhs
          simp only [Option.some.injEq, Prod.mk.injEq] at hinf
          obtain ⟨rfl, rfl⟩ := hinf
          exact inv_push hf hl hrhs (KontOk.asgn hk)
        · exact absurd hinf (by simp)
      all_goals (simp only [infer] at hinf; contradiction)
    case seq es =>
      simp only [infer] at hinf
      cases es with
      | nil =>
        simp only [inferSeq, Option.some.injEq, Prod.mk.injEq] at hinf
        obtain ⟨rfl, rfl⟩ := hinf
        exact inv_value hf hl rfl hk
      | cons e₁ rest =>
        cases rest with
        | nil =>
          simp only [inferSeq] at hinf
          exact inv_eval hf hl hinf hk
        | cons e₂ rest' =>
          simp only [inferSeq] at hinf
          split at hinf
          · rename_i σ Γ₁ h₁
            exact inv_push hf hl h₁ (KontOk.seqCons hinf hk)
          · exact absurd hinf (by simp)
    case if' c t els =>
      simp only [infer] at hinf
      split at hinf
      · rename_i σ Γ₁ hcnd
        exact inv_push hf hl hcnd (KontOk.ifK hinf hk)
      · exact absurd hinf (by simp)
    case while' c body =>
      simp only [infer] at hinf
      split at hinf
      · rename_i σ Γ₁ hcnd
        split at hinf
        · rename_i hΓ₁
          subst hΓ₁
          split at hinf
          · rename_i σb Γ₂ hbody
            split at hinf
            · rename_i hΓ₂
              subst hΓ₂
              simp only [Option.some.injEq, Prod.mk.injEq] at hinf
              obtain ⟨rfl, rfl⟩ := hinf
              exact inv_push hf hl hcnd
                (KontOk.whileCond ⟨⟨σ, hcnd⟩, ⟨σb, hbody⟩⟩ hk)
            · exact absurd hinf (by simp)
          · exact absurd hinf (by simp)
        · exact absurd hinf (by simp)
      · exact absurd hinf (by simp)
  · -- ## control = value v
    rw [hctl] at hc
    obtain ⟨τ, hv, hk⟩ := hc
    simp only [stepFn, hctl]
    unfold applyKont
    generalize hK : m.kont = K at hk ⊢
    cases hk with
    | nil => trivial
    | @seqNil Γ τ k hk' =>
      have hf' : Flat { m with kont := k } := Flat_congr rfl rfl hf
      have hl' : LocalsOk Γ { m with kont := k } := LocalsOk_congr hf hf' rfl hl
      exact inv_value hf' hl' hv hk'
    | @seqCons Γ τ e₁ es τ' Γ' k hseq hk' =>
      have hf' : Flat { m with kont := k } := Flat_congr rfl rfl hf
      have hl' : LocalsOk Γ { m with kont := k } := LocalsOk_congr hf hf' rfl hl
      cases es with
      | nil =>
        simp only [inferSeq] at hseq
        exact inv_push hf' hl' hseq (KontOk.seqNil hk')
      | cons e₂ es' =>
        simp only [inferSeq] at hseq
        split at hseq
        · rename_i σ Γ₁ h₁
          exact inv_push hf' hl' h₁ (KontOk.seqCons hseq hk')
        · exact absurd hseq (by simp)
    | @asgn Γ τ x k hk' =>
      have hf' : Flat { m with kont := k } := Flat_congr rfl rfl hf
      have hl' : LocalsOk Γ { m with kont := k } := LocalsOk_congr hf hf' rfl hl
      exact ⟨Flat.withCtl (Flat.setLocal hf' x v) _, envSet Γ x τ,
        LocalsOk.withCtl (Flat.setLocal hf' x v) (LocalsOk_setLocal hf' hl' hv) _,
        ⟨τ, hv, hk'⟩⟩
    | @ifK Γ τ t els τ' Γ' k hif hk' =>
      have hf' : Flat { m with kont := k } := Flat_congr rfl rfl hf
      have hl' : LocalsOk Γ { m with kont := k } := LocalsOk_congr hf hf' rfl hl
      cases els with
      | some e₂ =>
        simp only [inferIf] at hif
        split at hif
        · rename_i τt Γt τe Γe ht he
          split at hif
          · rename_i hagree
            obtain ⟨rfl, rfl⟩ := hagree
            simp only [Option.some.injEq, Prod.mk.injEq] at hif
            obtain ⟨rfl, rfl⟩ := hif
            by_cases hb : v.truthy
            · simp only [hb, if_true]; exact inv_eval hf' hl' ht hk'
            · simp only [hb]; exact inv_eval hf' hl' he hk'
          · exact absurd hif (by simp)
        · exact absurd hif (by simp)
      | none =>
        simp only [inferIf] at hif
        split at hif
        · rename_i τt Γt ht
          split at hif
          · rename_i hnil
            obtain ⟨rfl, rfl⟩ := hnil
            simp only [Option.some.injEq, Prod.mk.injEq] at hif
            obtain ⟨rfl, rfl⟩ := hif
            by_cases hb : v.truthy
            · simp only [hb, if_true]; exact inv_eval hf' hl' ht hk'
            · simp only [hb]; exact inv_value hf' hl' rfl hk'
          · exact absurd hif (by simp)
        · exact absurd hif (by simp)
    | @whileCond Γ τ c body k hloop hk' =>
      have hf' : Flat { m with kont := k } := Flat_congr rfl rfl hf
      have hl' : LocalsOk Γ { m with kont := k } := LocalsOk_congr hf hf' rfl hl
      obtain ⟨⟨σc, hcnd⟩, ⟨σb, hbody⟩⟩ := hloop
      by_cases hb : v.truthy
      · simp only [hb, if_true]
        exact inv_push hf' hl' hbody (KontOk.whileBody ⟨⟨σc, hcnd⟩, ⟨σb, hbody⟩⟩ hk')
      · simp only [hb]
        exact inv_value hf' hl' rfl hk'
    | @whileBody Γ τ c body k hloop hk' =>
      have hf' : Flat { m with kont := k } := Flat_congr rfl rfl hf
      have hl' : LocalsOk Γ { m with kont := k } := LocalsOk_congr hf hf' rfl hl
      obtain ⟨⟨σc, hcnd⟩, ⟨σb, hbody⟩⟩ := hloop
      exact inv_push hf' hl' hcnd (KontOk.whileCond ⟨⟨σc, hcnd⟩, ⟨σb, hbody⟩⟩ hk')
  · -- ## control = jump: excluded by `CtlOk`
    rw [hctl] at hc
    exact hc.elim

/-! ## 4. The three obligations, and the theorem -/

/-- Preservation. -/
theorem consecution (m m' : Machine) (h : Inv m) (hs : SmallStep m m') : Inv m' := by
  have hok := step_ok h
  unfold SmallStep at hs
  rw [hs] at hok
  exact hok

/-- Progress: a machine satisfying `Inv` is never one step from a type error.
    Every `StepResult` other than `.next`/`.done` is `False` under `StepOk`, so
    `.uncaught` in particular is unreachable. -/
theorem safety (m : Machine) (h : Inv m) : ¬ aboutToTypeStick m := by
  intro hbad
  have hok := step_ok h
  unfold aboutToTypeStick typeStuck at hbad
  cases hr : stepFn m with
  | next m' => rw [hr] at hbad; exact hbad
  | done v m' => rw [hr] at hbad; exact hbad
  | uncaught exc m' => rw [hr] at hok; exact hok
  | unsupported r => rw [hr] at hbad; exact hbad
  | stuck msg => rw [hr] at hbad; exact hbad

/-- Initiation, for the machine `Machine.init` builds. -/
theorem initiation {p : Expr} (h : check p = .accept) : Inv (Machine.init p) := by
  refine ⟨⟨rfl, rfl, rfl⟩, [], ?_, ?_⟩
  · intro x τ hg; exact absurd hg (by simp [envGet?])
  · unfold check at h
    show CtlOk [] (Machine.init p)
    unfold CtlOk
    split at h
    · rename_i r hr
      obtain ⟨τ, Γ'⟩ := r
      exact ⟨τ, Γ', hr, KontOk.nil⟩
    · exact absurd h (by simp)

/-- **Static soundness, from any machine satisfying the invariant.** Stated this
    way so that P1's prelude-booted start (`Prelude.initWithPrelude`, the
    starting configuration `SorbetSafety.lean:100` insists on) is an instance
    rather than a restatement. -/
theorem sound_from {m₀ : Machine} (h : Inv m₀) :
    ∀ r, ReachableResult m₀ r → ¬ typeStuck r :=
  invariant_sound_from Inv h consecution safety

/-- **The POC theorem.** `check` accepts ⇒ no reachable outcome is a type
    error. Unconditional: no rely condition, no assumed hypothesis. -/
theorem check_sound {p : Expr} (h : check p = .accept) :
    ∀ r, ReachableResult (Machine.init p) r → ¬ typeStuck r :=
  sound_from (initiation h)

/-! ## 5. Worked examples

`decide` runs the checker; the theorem then applies to the program. -/

/-- `x = 1; if true then x else 0 end` -/
def egIf : Expr :=
  .seq [ .vasgn .lvar "x" (.int 1),
         .if' .tru (.var .lvar "x") (some (.int 0)) ]

example : check egIf = .accept := by
  simp [check, egIf, infer, inferSeq, inferIf, envSet, envGet?]

theorem egIf_safe : ∀ r, ReachableResult (Machine.init egIf) r → ¬ typeStuck r :=
  check_sound (by simp [check, egIf, infer, inferSeq, inferIf, envSet, envGet?])

/-- `x = 0; while true do x = 1 end` — diverges, which safety permits: the
    property is *never type-stuck*, not *terminates*. -/
def egLoop : Expr :=
  .seq [ .vasgn .lvar "x" (.int 0),
         .while' .tru (.vasgn .lvar "x" (.int 1)) ]

example : check egLoop = .accept := by
  simp [check, egLoop, infer, inferSeq, envSet]

theorem egLoop_safe : ∀ r, ReachableResult (Machine.init egLoop) r → ¬ typeStuck r :=
  check_sound (by simp [check, egLoop, infer, inferSeq, envSet])

/-- The ratchet's default. A `send` is outside P0, so the checker abstains —
    it does **not** reject. -/
example : check (.send (some (.int 1)) "+" [.int 2] none) = .unknown := by
  simp [check, infer]

/-- A genuine type disagreement inside the fragment is `unknown` too: P0 has no
    union type, so the branches cannot be joined. -/
example : check (.if' .tru (.int 1) (some .nil)) = .unknown := by
  simp [check, infer, inferIf]

/-! ## 6. Axiom hygiene

The P0 exit criterion. Only the three standard Lean axioms — no `sorry`, and in
particular no `native_decide`/`ofReduceBool`, which is why §5's examples are
discharged by `simp` over the equation lemmas rather than by kernel reduction
(`infer` is well-founded-recursive, so `decide` does not reduce it). Same
baseline as `Proof/SorbetSafety.lean` [V]. -/

/-- info: 'RubyCore.Proof.Static.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms check_sound

end Static
end Proof
end RubyCore
