/-
**Sorbet safety**: the three-outcome runtime statement, as a formal object.

`../../docs/semantics/types-and-preservation.md` §C.1 argues that the honest
soundness target for Sorbet is not a static subject-reduction theorem — the
static half is unsound by design — but the *runtime* three-outcome statement
(§B.5, the gradual-typing shape):

> a well-typed program runs to a value, **or raises a `TypeError` at a runtime
> sig boundary** (blame), or diverges — never reaching a genuinely stuck state.

This file makes "or blames" a formal object and proves the two directions of
the reachability machinery for it, reusing `TypeSafety.lean` unchanged. It is
deliberately the *same* development with **the bad-state predicate weakened**:
`typeStuck` minus the outcomes that are Sorbet's runtime enforcement doing its
job. That is the running thesis of `type-safety-by-reachability.md` — one
engine, one metatheorem, a swappable bad state — applied once more.

## What is and is not proved here

Proved: `sorbet_invariant_sound` (Direction B — any inductive invariant ruling
out non-blame type-stuck states certifies Sorbet-safety) and the Direction-A
execution certificates. These are about the **runtime** half only.

NOT proved, and not claimed anywhere below: "srb accepts P ⇒ P is Sorbet-safe".
That needs a formalization of Sorbet's *static* judgment (`Δ; Γ ⊢ e : τ`, the
T1–T3 staging of `type-judgments.md`), which does not exist yet. The scope such
a theorem could have is pinned separately and executably by
`RubyCore/Types/Fragment.lean`; this file supplies the property that theorem
would conclude.

## Blame is only visible in the message

sorbet-runtime raises a plain `::TypeError` for an enforcement failure, so blame
is **indistinguishable by class** from a genuine Ruby `TypeError` (`1 + "a"`).
That is Sorbet's design choice, not a modeling shortcut, and it forces the
predicate below to look at the message — exactly as the difftest classifier has
to (difftest implementation-notes N28). The prefixes mirror the prelude shim's
`T.__check!` and the gem's `T::Private::Methods::CallValidation`, which the
Sorbet corpus pins byte-for-byte.
-/
import RubyCore.Proof.TypeSafety
import RubyCore.PreludeBoot

namespace RubyCore
namespace Proof

open Interp

/-! ## 1. Blame: an enforcement failure, not a stuck program -/

/-- Message prefixes emitted by sorbet-runtime's enforcement (and by the
    prelude shim, which reproduces them byte-for-byte). -/
def blamePrefixes : List String :=
  ["Parameter '", "Return value:", "T.let:", "T.cast:", "T.bind:",
   "T.assert_type!:", "Passed `nil` into T.must"]

/-- The message carried by an exception object (empty when there is none) —
    the same projection `Obs.observe` reports. -/
def excMessage (h : Heap) : Value → String
  | .ref o => match (h.get o).payload with
    | .exc s => s
    | _ => ""
  | _ => ""

/-- **Blame**: a `TypeError` raised by Sorbet's runtime enforcement at a sig or
    assertion boundary. This is the *licensed* failure of the three-outcome
    statement — the type system's backstop firing, which is what it is for. -/
def isBlame (h : Heap) (exc : Value) : Prop :=
  isA h exc Boot.typeErrorId = true ∧
  ∃ p ∈ blamePrefixes, p.isPrefixOf (excMessage h exc)

/-- The weakened bad state: type-stuck **and not** blame. A `NoMethodError`
    escaping to toplevel is still bad; a sig-boundary `TypeError` is not. -/
def sorbetStuck : StepResult → Prop
  | .uncaught exc m => isTypeError m.heap exc ∧ ¬ isBlame m.heap exc
  | _ => False

/-- A config one step away from a non-blame type-stuck outcome. -/
def aboutToSorbetStick (m : Machine) : Prop := sorbetStuck (stepFn m)

/-- **The property**, from a given starting configuration. Every reachable
    outcome is a value, a divergence, or blame — never a genuinely stuck state.
    This is the conclusion a Sorbet soundness theorem would have. -/
def SorbetSafeFrom (m₀ : Machine) : Prop :=
  ∀ r, ReachableResult m₀ r → ¬ sorbetStuck r

/-- **Sorbet safety of a program, as actually executed.**

    Note the starting configuration: the **prelude-booted** heap, not
    `Machine.init program`. This is not a technicality. Sig enforcement lives in
    the `T` shim, which is part of the prelude (`prelude/prelude.rb`, L80), so a
    statement over `Machine.init` would be about a program running with no core
    library and no `T` at all — under which every Sorbet program raises
    `NameError` and the theorem says nothing about Sorbet. Anything proved here
    must be proved about the machine the interpreter really starts from.

    (A prelude that fails to boot is a model bug, not a program outcome — the
    hypothesis is vacuous in that case, exactly as `PreludeBoot` treats it.) -/
def SorbetSafe (program : Expr) : Prop :=
  ∀ m₀, Prelude.initWithPrelude program = .ok m₀ → SorbetSafeFrom m₀

/-! ## 2. The bad state really is weaker (blame is carved out, nothing else) -/

/-- Sorbet-stuck implies type-stuck: the weakened predicate only ever removes
    outcomes. So a program already proved type-safe by `invariant_sound` is
    Sorbet-safe for free (`typeSafe_sorbetSafe` below) — the two developments
    cannot disagree about anything except blame. -/
theorem sorbetStuck_typeStuck {r : StepResult} (h : sorbetStuck r) : typeStuck r := by
  cases r with
  | uncaught exc m => exact h.1
  | done _ _ => exact h.elim
  | unsupported _ => exact h.elim
  | stuck _ => exact h.elim
  | next _ => exact h.elim

/-- Type safety is the stronger claim, as it should be: no type errors at all
    implies none that are not blame. -/
theorem typeSafe_sorbetSafe {m₀ : Machine}
    (h : ∀ r, ReachableResult m₀ r → ¬ typeStuck r) :
    SorbetSafeFrom m₀ :=
  fun r hr hs => h r hr (sorbetStuck_typeStuck hs)

/-! ## 3. Direction B — the metatheorem (`type-safety-by-reachability.md` §4)

    Identical in shape to `invariant_sound`, over the weakened bad state: an
    untrusted engine supplies a concrete inductive invariant `I` per program and
    the trusted validator re-checks three local conditions. Proved by the same
    induction, reusing `invariant_reaches`. -/

theorem sorbet_invariant_sound_from {m₀ : Machine} (I : Machine → Prop)
    (init : I m₀)
    (cons : ∀ m m', I m → SmallStep m m' → I m')
    (safe : ∀ m, I m → ¬ aboutToSorbetStick m) :
    ∀ r, ReachableResult m₀ r → ¬ sorbetStuck r := by
  rintro r ⟨m, hr, hstep⟩ hss
  have hIm : I m := invariant_reaches cons init hr
  exact safe m hIm (by unfold aboutToSorbetStick; rw [hstep]; exact hss)

/-- **Sorbet safety by invariant.** Per program, an untrusted engine emits `I`;
    Lean re-checks Initiation / Consecution / Safety for that `I`, and this
    theorem does the rest — for all inputs, unbounded fuel. -/
theorem sorbet_invariant_sound {program : Expr} (I : Machine → Prop)
    (init : ∀ m₀, Prelude.initWithPrelude program = .ok m₀ → I m₀)
    (cons : ∀ m m', I m → SmallStep m m' → I m')
    (safe : ∀ m, I m → ¬ aboutToSorbetStick m) :
    SorbetSafe program :=
  fun m₀ hb => sorbet_invariant_sound_from I (init m₀ hb) cons safe

/-- The obligation is *easier* than the type-safety one, which is the point of
    weakening: an invariant good enough for type safety is good enough here, so
    existing certificates transfer. -/
theorem aboutToSorbetStick_of_typeStick {m : Machine}
    (h : ¬ aboutToTypeStick m) : ¬ aboutToSorbetStick m :=
  fun hs => h (sorbetStuck_typeStuck hs)

/-! ## 4. Direction A — execution certificates (§3)

    A concrete run is a self-certifying witness *for that input*: no invariant,
    no SMT, the trace is the proof. Two outcomes are licensed, and the second is
    the one this file adds — a run that ends in blame is Sorbet-safe, because
    blame is enforcement working. -/

/-- A value outcome is never Sorbet-stuck. -/
theorem done_not_sorbetStuck {v : Value} {m : Machine} : ¬ sorbetStuck (.done v m) :=
  fun h => h

/-- **A run that blames is Sorbet-safe on that input.** The distinguishing
    certificate of this file: the same outcome that `typeStuck` counts as a
    failure is, for Sorbet, the type system doing its job. -/
theorem blame_not_sorbetStuck {exc : Value} {m : Machine} (h : isBlame m.heap exc) :
    ¬ sorbetStuck (.uncaught exc m) :=
  fun hs => hs.2 h

/-- Execution certificate, value case: a terminating run witnesses a reachable
    non-Sorbet-stuck outcome. -/
theorem run_value_sorbet_safe {m₀ : Machine} {fuel : Nat} {v : Value} {mf : Machine}
    (h : run fuel m₀ = .value v mf) :
    ∃ r, ReachableResult m₀ r ∧ ¬ sorbetStuck r :=
  ⟨.done v mf, run_value_reaches_done h, done_not_sorbetStuck⟩

/-- Execution certificate, blame case. -/
theorem run_blame_sorbet_safe {m₀ : Machine} {fuel : Nat} {exc : Value} {mf : Machine}
    (h : run fuel m₀ = .uncaught exc mf)
    (hb : isBlame mf.heap exc) :
    ∃ r, ReachableResult m₀ r ∧ ¬ sorbetStuck r :=
  ⟨.uncaught exc mf, run_uncaught_reaches h, blame_not_sorbetStuck hb⟩

/-- **Counterexample certificate.** A run ending in an uncaught type-family
    exception that is *not* blame refutes Sorbet-safety for that program: the
    trace is the witness. This is the shape a search engine reports — and note
    what it excludes, which is the whole content of the weakening: finding a
    program whose only failure is blame proves nothing against Sorbet. -/
theorem run_sorbetStuck_unsafe {m₀ : Machine} {fuel : Nat} {exc : Value} {mf : Machine}
    (h : run fuel m₀ = .uncaught exc mf)
    (hte : isTypeError mf.heap exc) (hnb : ¬ isBlame mf.heap exc) :
    ¬ SorbetSafeFrom m₀ :=
  fun hsafe =>
    hsafe (.uncaught exc mf) (run_uncaught_reaches h) ⟨hte, hnb⟩

end Proof
end RubyCore
