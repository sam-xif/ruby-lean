import Denote.Proto.Safety

/-!
# `Denote/Proto/Checker.lean` — a certificate checker, its soundness, and the end-to-end theorem

`Denote/Proto/Safety.lean` starts from a `PJudge` *derivation*, which is a proof term someone
has to write by hand. This file closes the last gap: a **computable checker** over a
certificate, proved sound against `PJudge`, so the top-level theorem reads

> if `pvalidate p cert = true`, then running `p` from any conformant machine reaches no
> type-stuck outcome — and whenever it returns, the value is in the type the checker computed.

Nothing is trusted. `pvalidate` is a `Bool`; `pcheck_sound` is what makes it worth reading.

## The certificate

`PHint` mirrors `PJudge`'s constructors, and the certificate is the pair `(p, hint)` — the
program plus a hint tree of the same shape. That is the real ratchet's `Deriv` shape at
four rules instead of eighty-three.

**Where the hints carry information and where they do not**, which is the interesting part:
three of the four rules are syntax-directed (a literal's type, a variable's type from `Γ`, an
assignment's from its right-hand side), so their hints are *tags* — they exist only to say
which rule was meant, and a checker could have guessed. `PJudge.brk` is not: it types `break`
at **any** `τ`, so `PHint.brk` has to carry the type, and no checker can infer it. The hint
tree is load-bearing exactly where the judgment is not syntax-directed, which is the general
reason a certificate language exists at all.

## Two routes from the certificate to safety, both proved

```
pvalidate p cert = true
        |  pcheck_sound                             (this file)
        v
   PJudge [] p τ Γ'
        |                        \
        |  pInv_init              \  psemJudge_of_pjudge      (Safety.lean §9 — adequacy)
        v                          v
   PInv τ (evalFrom m p)       PSemJudge [] p τ
        |  safety_of_invariant       |  stuckFree_of_psemJudge (this file)
        v                            v
              StuckFree m p  ... and both agree
```

The left route is `Invariant.lean`'s reduction. The right route is the one the answer type buys
and is the reason `PSemJudge` is the right *statement*: because `StepResult.uncaught` is
constructed at **one** site in the interpreter (`unwind`'s `[]` arm on `raiseJ`), every
type-stuck outcome is an `esc (.raiseJ exc)` **answer**, so a judgment that constrains answers
constrains stuck-freedom directly. `SemJudge` cannot do this — that is
`Denote/Sem/NoProgress.lean`.

## The one thing the right route needs and cannot have in general

`stuckFree_of_psemJudge` has to rule out `runA` returning `.halt` — a run that ends *without*
delivering an answer. For the fragment that is `no_halt`, proved from the invariant. In
general it needs the inversion `UncaughtInv` below: the converse of `done_inv`, saying
`.uncaught` is only ever `unwind`'s empty-continuation arm. **That theorem does not exist**
(`RubyCore/Proof/NotDone.lean` has `done_inv` and no counterpart), and it is stated here as a
named `Prop` so the gap has a target. Until it is proved, the *general* `PSemJudge → safety`
step is unavailable and the invariant route is the one that scales.
-/

set_option autoImplicit false

namespace Ratchet.Denote.Proto

open RubyCore Ratchet Ratchet.Denote

/-! ## §1 The certificate language and the checker -/

/-- One constructor per `PJudge` rule. `brk` carries a `Ty` because `PJudge.brk` is not
syntax-directed; the other three carry nothing because they are. -/
inductive PHint where
  | intLit
  | var
  | vasgn (sub : PHint)
  | brk (τ : Ty)
deriving Repr, Inhabited

/-- **The checker.** Total, computable, and `none` on anything it cannot justify. The three
side conditions on `vasgn` are `PJudge.vasgn`'s own, decided rather than assumed. -/
def pcheck (Γ : Env) (e : Ratchet.Expr) : PHint → Option (Ty × Env)
  | .intLit =>
    match e with
    | .int _ => some (.int, Γ)
    | _ => none
  | .var =>
    match e with
    | .var .lvar x =>
      match envGet? Γ x with
      | some τ => if isAliasTy τ then none else some (τ, Γ)
      | none => none
    | _ => none
  | .vasgn sub =>
    match e with
    | .vasgn .lvar x e' =>
      match pcheck Γ e' sub with
      | some (σ, Γ₁) =>
        if capStale x σ σ || capStaleCtx x σ Ratchet.ctx0 || isAliasTy σ then none
        else some (σ, envAfter Γ₁ x σ)
      | none => none
    | _ => none
  | .brk τ =>
    match e with
    | .brk none => some (τ, Γ)
    | _ => none

/-- The top-level verdict: one `Bool`, and the whole of what is checked. -/
def pvalidate (p : Ratchet.Expr) (cert : PHint) : Bool := (pcheck [] p cert).isSome

/-! ## §2 Checker soundness

`pcheck` passing produces a `PJudge` derivation. One induction on the hint, one case per
rule, and each case's work is inverting the `Option`/`if` the checker built. -/

theorem pcheck_sound : ∀ (cert : PHint) (Γ : Env) (e : Ratchet.Expr) (τ : Ty) (Γ' : Env),
    pcheck Γ e cert = some (τ, Γ') → PJudge Γ e τ Γ' := by
  intro cert
  induction cert with
  | intLit =>
    intro Γ e τ Γ' h
    unfold pcheck at h
    split at h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ (Option.some.inj h)
      exact .intLit
    · exact absurd h (by simp)
  | var =>
    intro Γ e τ Γ' h
    unfold pcheck at h
    split at h
    · rename_i x
      split at h
      · rename_i ρ hget
        split at h
        · exact absurd h (by simp)
        · rename_i halias
          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ (Option.some.inj h)
          exact .var hget (by simpa using halias)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  | vasgn sub ih =>
    intro Γ e τ Γ' h
    unfold pcheck at h
    split at h
    · rename_i x e'
      split at h
      · rename_i p hsub
        split at h
        · exact absurd h (by simp)
        · rename_i hside
          simp only [Bool.or_eq_false_iff, Bool.not_eq_true] at hside
          obtain ⟨⟨hcap, hctx⟩, halias⟩ := hside
          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ (Option.some.inj h)
          exact .vasgn (ih Γ e' _ _ hsub) hcap hctx halias
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  | brk ρ =>
    intro Γ e τ Γ' h
    unfold pcheck at h
    split at h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ (Option.some.inj h)
      exact .brk
    · exact absurd h (by simp)

theorem pvalidate_sound {p : Ratchet.Expr} {cert : PHint} (h : pvalidate p cert = true) :
    ∃ (τ : Ty) (Γ' : Env), PJudge [] p τ Γ' := by
  simp only [pvalidate, Option.isSome_iff_exists] at h
  obtain ⟨⟨τ, Γ'⟩, hp⟩ := h
  exact ⟨τ, Γ', pcheck_sound cert [] p τ Γ' hp⟩

/-! ## §3 The end-to-end theorem, left route (via the invariant)

Stated **at an arbitrary incoming environment** and specialised to `[]` afterwards, not the
other way round. `pcheck_sound` was always `∀ Γ`; it is `pvalidate` — the whole-program
verdict — that is at `[]`, and conflating the two is what made the first version of this
file's theorems weaker than their proofs. See `Safety.lean`'s `pInv_init`. -/

/-- **The final theorem, general form.** A checked `(program, certificate)` pair is safe at
every machine conformant with the environment it was checked in: no run reaches a
`NoMethodError`/`ArgumentError`/`TypeError`, at any fuel. -/
theorem checkedAt_implies_safe {p : Ratchet.Expr} {cert : PHint} {Γ : Env} {τ : Ty} {Γ' : Env}
    (h : pcheck Γ p cert = some (τ, Γ'))
    {m : Machine} (hm : StateOk Ratchet.ctx0 Γ .ivar0 m) : StuckFree m p :=
  certificate_implies_safe (pcheck_sound cert Γ p τ Γ' h) hm

/-- …and the whole-program specialisation, which is what `pvalidate`'s `Bool` means: a program
starts with no locals. -/
theorem checked_implies_safe {p : Ratchet.Expr} {cert : PHint} (h : pvalidate p cert = true)
    {m : Machine} (hm : StateOk Ratchet.ctx0 [] .ivar0 m) : StuckFree m p := by
  simp only [pvalidate, Option.isSome_iff_exists] at h
  obtain ⟨⟨τ, Γ'⟩, hp⟩ := h
  exact checkedAt_implies_safe hp hm

/-- …and the type claim, which is the other half of what a checker is for: the type `pcheck`
computed really does describe the value, whenever there is one. -/
theorem checked_types_the_value {p : Ratchet.Expr} {cert : PHint} {Γ : Env} {τ : Ty} {Γ' : Env}
    (h : pcheck Γ p cert = some (τ, Γ'))
    {m : Machine} (hm : StateOk Ratchet.ctx0 Γ .ivar0 m)
    (fuel : Nat) (v : Value) (m₀ : Machine) (rest : Nat)
    (hr : runA fuel (evalFrom m p) = .ans (.val v) m₀ rest) : denM τ m₀ v :=
  certificate_types_the_value (pcheck_sound cert Γ p τ Γ' h) hm fuel v m₀ rest hr

/-- The checker's verdict composed with adequacy: the answer-typed semantic judgment, straight
from a `Bool`. -/
theorem psemJudge_of_pcheck {p : Ratchet.Expr} {cert : PHint} {Γ : Env} {τ : Ty} {Γ' : Env}
    (h : pcheck Γ p cert = some (τ, Γ')) : PSemJudge Γ p τ :=
  psemJudge_of_pjudge (pcheck_sound cert Γ p τ Γ' h)

/-! ## §4 The right route: `PSemJudge` implies stuck-freedom directly

The payoff of answer-typing, spelled out. It needs one fragment-local fact — that a run never
ends *without* delivering an answer — and §5 says what the general version of that costs. -/

/-- At a non-answer point a `PInv` machine always steps. One case per invariant arm; the
`value` and `jump` arms are where a non-empty continuation is forced to be an `asgnK`. -/
theorem step_next_of_none {τa : Ty} {m : Machine} (hinv : PInv τa m)
    (hap : answerPoint m = none) : ∃ m', Interp.stepFn m = .next m' := by
  rcases hinv with ⟨e₀, Γ, Γ', τ, hc, -, hj, -⟩ | ⟨v, Γ, τ, hc, -, -, hk⟩ |
    ⟨j, Γ, τ, hc, hjo, hk⟩
  · cases hj with
    | intLit => exact ⟨_, step_int (by simpa [toRuby] using hc)⟩
    | var _ _ => exact ⟨_, step_var (by simpa [toRuby, toRubyVarKind] using hc)⟩
    | vasgn _ _ _ _ => exact ⟨_, step_vasgn (by simpa [toRuby, toRubyVarKind] using hc)⟩
    | brk => exact ⟨_, step_brk (by simpa [toRuby, toRubyOpt] using hc)⟩
  · -- a value in flight: the continuation cannot be empty, or this were an answer point
    cases hkn : m.kont with
    | nil => rw [answerPoint, hkn] at hap; simp only at hap; rw [hc] at hap; simp at hap
    | cons k rest =>
      rw [hkn] at hk
      cases hk with
      | asgnK _ _ _ _ => exact ⟨_, step_asgnK_val hc hkn⟩
  · cases hkn : m.kont with
    | nil => rw [answerPoint, hkn] at hap; simp only at hap; rw [hc] at hap; simp at hap
    | cons k rest =>
      rw [hkn] at hk
      cases hk with
      | asgnK _ _ _ _ => exact ⟨_, step_asgnK_jump hc hkn⟩

/-- **A `PInv` run always delivers an answer.** It never halts: `.unsupported` and `.stuck`
are unreachable from the fragment at a non-answer point, and `.uncaught` is unreachable
outright. -/
theorem no_halt (τa : Ty) : ∀ (fuel : Nat) (m : Machine) (h : Halt),
    PInv τa m → runA fuel m ≠ .halt h := by
  intro fuel
  induction fuel with
  | zero =>
    intro m h hinv
    cases hap : answerPoint m with
    | some a => rw [runA_ans hap]; simp
    | none => rw [runA_zero hap]; simp
  | succ n ih =>
    intro m h hinv
    cases hap : answerPoint m with
    | some a => rw [runA_ans hap]; simp
    | none =>
      obtain ⟨m', hnext⟩ := step_next_of_none hinv hap
      rw [runA_succ hap, hnext]
      exact ih m' h (preserved τa m m' hinv hnext)

/-- **The right route.** `PSemJudge` implies stuck-freedom — the statement
`Denote/Sem/NoProgress.lean` refutes for `SemJudge`, true here because the hypothesis is an
*answer* rather than a value.

`PInv` appears only to supply `no_halt`; every use of the *typing* content goes through
`PSemJudge`. -/
theorem stuckFree_of_psemJudge {p : Ratchet.Expr} {τ : Ty} {Γ Γ' : Env}
    (hj : PJudge Γ p τ Γ') (hsem : PSemJudge Γ p τ)
    {m : Machine} (hm : StateOk Ratchet.ctx0 Γ .ivar0 m) : StuckFree m p := by
  intro fuel
  rw [run_eq_out_nil fuel (evalFrom m p)]
  cases hr : runA fuel (evalFrom m p) with
  | halt h => exact absurd hr (no_halt τ fuel _ h (pInv_init hj hm))
  | oof m₀ => simp [ARes.out, Semantics.typeStuck]
  | ans a m₀ rest =>
    have hok := hsem m hm fuel a m₀ rest hr
    have hap : answerPoint m₀ = some a :=
      answerPoint_of_ans fuel (evalFrom m p) a m₀ rest hr
    simp only [ARes.out, deliverA_nil_self hap]
    cases a with
    | val v =>
      -- a value at the empty continuation: `.done`, then `.value`, which is not type-stuck
      obtain ⟨hc, hk⟩ := ctl_kont_of_val hap
      match rest with
      | 0 => simp [run_zero, Semantics.typeStuck]
      | r + 1 => rw [run_succ, step_value_nil hc hk]; simp [Semantics.typeStuck]
    | esc j =>
      -- the escape clause of `AnsOk` is exactly `typeStuck`'s own predicate
      have hc := ctl_of_esc hap
      have hk : m₀.kont = [] := by
        cases hkn : m₀.kont with
        | nil => rfl
        | cons k r => rw [answerPoint, hkn] at hap; simp at hap
      match rest with
      | 0 => simp [run_zero, Semantics.typeStuck]
      | r + 1 =>
        cases j with
        | raiseJ exc =>
          rw [run_succ, show Interp.stepFn m₀ = .uncaught exc m₀ by
            simp only [Interp.stepFn, hc, Interp.unwind, hk]]
          simpa [Semantics.typeStuck, AnsOk, EscOk] using hok
        | brkJ w => rw [run_succ, step_brkJ_nil hc hk]; simp [Semantics.typeStuck]
        | nxtJ w =>
          rw [run_succ, show Interp.stepFn m₀ = .stuck
                "jump escaped the program (break/next/retry at toplevel)" by
            simp only [Interp.stepFn, hc, Interp.unwind, hk]]
          simp [Semantics.typeStuck]
        | redoJ =>
          rw [run_succ, show Interp.stepFn m₀ = .stuck
                "jump escaped the program (break/next/retry at toplevel)" by
            simp only [Interp.stepFn, hc, Interp.unwind, hk]]
          simp [Semantics.typeStuck]
        | retryJ =>
          rw [run_succ, show Interp.stepFn m₀ = .stuck
                "jump escaped the program (break/next/retry at toplevel)" by
            simp only [Interp.stepFn, hc, Interp.unwind, hk]]
          simp [Semantics.typeStuck]
        | retJ v t => exact absurd hok (by simp [AnsOk, EscOk])
        | throwJ t v => exact absurd hok (by simp [AnsOk, EscOk])

/-- **The two routes agree**, which is the check worth having: the same `Bool` yields the same
theorem through the invariant and through adequacy. -/
theorem checked_implies_safe' {p : Ratchet.Expr} {cert : PHint} {Γ : Env} {τ : Ty} {Γ' : Env}
    (h : pcheck Γ p cert = some (τ, Γ'))
    {m : Machine} (hm : StateOk Ratchet.ctx0 Γ .ivar0 m) : StuckFree m p :=
  stuckFree_of_psemJudge (pcheck_sound cert Γ p τ Γ' h) (psemJudge_of_pcheck h) hm

/-! ## §5 What the general right route needs, stated -/

/-- **The missing inversion**: `.uncaught` is constructed at one site in the interpreter
(`unwind`'s empty-continuation arm on a `raiseJ`), so a step that answers `.uncaught` must
have been that state. This is `done_inv`'s counterpart and it **does not exist**
(`RubyCore/Proof/NotDone.lean` has the one and not the other).

With it, `no_halt`'s `.uncaught` case is general rather than fragment-local, and
`stuckFree_of_psemJudge` scales to the real judgment. Without it, the invariant route is the
one that scales. Stated, not proved, and nothing here assumes it. -/
def UncaughtInv : Prop :=
  ∀ (m : Machine) (exc : Value) (m' : Machine), Interp.stepFn m = .uncaught exc m' →
    m.ctl = .jump (.raiseJ exc) ∧ m.kont = [] ∧ m' = m

/-! ## §6 Non-vacuity: the checker accepts, and rejects

`#guard`s, so they fail the build. Three positives and four negative controls — the negatives
matter more: a checker that accepts everything would satisfy §2 just as well. -/

/-- `x = (y = 1)` and its certificate. -/
def certNested : PHint := .vasgn (.vasgn .intLit)

/-- `x = break`, certified at `Integer` — a type claim that is *meaningless* as a value claim,
which is the point: the escape clause is what carries the content. -/
def certBreak : PHint := .vasgn (.brk .int)

#guard pvalidate progNested certNested
#guard pvalidate progBreak certBreak
#guard pvalidate (.int 7) .intLit

-- **Negative controls.**
-- the hint does not match the syntax
#guard ! pvalidate (.int 7) .var
-- an unbound variable has no type in `Γ = []`
#guard ! pvalidate (.var .lvar "x") .var
-- the hint tree is too shallow for the program
#guard ! pvalidate progNested (.vasgn .intLit)
-- …and too deep
#guard ! pvalidate (.int 7) (.vasgn .intLit)

/-- The end-to-end statement at a real program and a real machine, with every hypothesis
discharged: `x = (y = 1)`, checked by `pvalidate`, safe at the prelude-booted machine. -/
theorem nested_checked_safe (hb : bootOkB = true) :
    StuckFree bootMachine progNested :=
  checked_implies_safe (cert := certNested) (by decide) (stateOk_boot hb)

theorem break_checked_safe (hb : bootOkB = true) :
    StuckFree bootMachine progBreak :=
  checked_implies_safe (cert := certBreak) (by decide) (stateOk_boot hb)

/-! ## §7 The generalisation is not vacuous: a non-empty incoming environment

`Γ` being universally quantified is worth nothing unless `StateOk ctx0 Γ .ivar0 m` is
satisfiable for a `Γ` that is not `[]` — and at the booted machine it is not, because `EnvOk`
is *complete* (a name `Γ` does not mention reads as `nil`) and the booted machine has no
locals. The satisfiable non-empty environments are the ones that arise **mid-run**, which is
exactly the case the generalisation exists for.

So the witness is built the way the machine builds it: write a local, and `stateOk_write` hands
back conformance at the environment the write produced. Then a derivation *at that
environment* — `PJudge.var`, which cannot be stated at `[]` at all, since `envGet? [] x` is
`none` — is checked, and both the safety and the typing claims follow. -/

/-- The environment after `x = 1`, and the machine that matches it. -/
def envX : Env := envAfter [] "x" .int

def machX : Machine := bootMachine.setLocal "x" (.int 1)

theorem stateOk_machX (hb : bootOkB = true) : StateOk Ratchet.ctx0 envX .ivar0 machX :=
  stateOk_write (stateOk_boot hb) (by simp [denM, isIntV]) (by decide) (by decide) (by decide)

-- `x` really is bound to `Integer` there, so `PHint.var` is checkable and the whole chain runs
-- at a non-empty environment…
#guard pcheck envX (.var .lvar "x") .var == some (.int, envX)
-- …and the same pair is rejected at the empty environment, which is the contrast.
#guard ! pvalidate (.var .lvar "x") .var

theorem readX_safe (hb : bootOkB = true) : StuckFree machX (.var .lvar "x") :=
  checkedAt_implies_safe (Γ := envX) (cert := .var) (τ := .int) (Γ' := envX)
    (by decide) (stateOk_machX hb)

/-- The typing claim at a non-empty environment: reading `x` yields an `Integer`. -/
theorem readX_types (hb : bootOkB = true) :
    ∀ (fuel : Nat) (v : Value) (m₀ : Machine) (rest : Nat),
      runA fuel (evalFrom machX (.var .lvar "x")) = .ans (.val v) m₀ rest → denM .int m₀ v :=
  fun fuel v m₀ rest hr =>
    checked_types_the_value (Γ := envX) (cert := .var) (Γ' := envX) (by decide)
      (stateOk_machX hb) fuel v m₀ rest hr

/-- And the typing claim is not vacuous either: the run does return, and it returns `1`. -/
def readXValue : Bool :=
  match Interp.run 8 (evalFrom machX (.var .lvar "x")) with
  | .value (.int n) _ => n == 1
  | _ => false

#guard readXValue

#print axioms pcheck_sound
#print axioms checkedAt_implies_safe
#print axioms checked_implies_safe
#print axioms checked_types_the_value
#print axioms stuckFree_of_psemJudge
#print axioms checked_implies_safe'
#print axioms nested_checked_safe
#print axioms readX_safe
#print axioms readX_types

end Ratchet.Denote.Proto
