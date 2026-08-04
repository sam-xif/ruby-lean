/-
Smoke-test demonstrations for the control-core `Step` relation: the relation is
non-vacuous, it *computes*, and adequacy applies to real initial configs. These
`example`s double as regression tests that the constructors actually fire.
-/
import RubyCore.Proof.Adequacy
import RubyCore.Proof.TypeSafety

namespace RubyCore
namespace Proof

open Interp

/-- Reflexive-transitive closure of `Step` — "reduces in finitely many steps"
    (defined locally; this project doesn't depend on Mathlib). -/
inductive Steps : Machine → Machine → Prop where
  | refl {m} : Steps m m
  | head {m₁ m₂ m₃} : Step m₁ m₂ → Steps m₂ m₃ → Steps m₁ m₃

/-- The toplevel config of any fragment program is in the fragment
    (`self = main`, empty kont, fragment head). -/
theorem init_InFrag {e : Expr} (he : FragExpr e) : InFrag (Machine.init e) := by
  refine ⟨⟨Boot.mainId, rfl⟩, ?_, ?_, ?_⟩
  · intro k hk; simp [Machine.init, Machine.initOn] at hk
  · intro e' he'
    have : (Machine.init e).ctl = .eval e := rfl
    rw [this] at he'; injection he' with h; subst h; exact he
  · intro j hj
    have : (Machine.init e).ctl = .eval e := rfl
    rw [this] at hj; exact Ctl.noConfusion hj

/-- Non-vacuity: the relation fires on a concrete config. -/
example : Step (Machine.init (.int 7)) (withCtl (Machine.init (.int 7)) (.value (.int 7))) :=
  .intLit rfl

/-- Adequacy specialized to a real initial config: `Step` from `init (1;2)`
    coincides exactly with the executable stepper. -/
example (m' : Machine) :
    Step (Machine.init (.seq [.int 1, .int 2])) m'
      ↔ stepFn (Machine.init (.seq [.int 1, .int 2])) = .next m' :=
  Step.adequacy (init_InFrag (by simp [FragExpr]))

/-- The semantics *computes*: `1; 2` reduces under `Step` to the value `2`
    with an empty continuation (a terminal config), one `Step` at a time. -/
example : ∃ mf, Steps (Machine.init (.seq [.int 1, .int 2])) mf
            ∧ mf.ctl = .value (.int 2) ∧ mf.kont = [] := by
  have chain : Steps (Machine.init (.seq [.int 1, .int 2])) _ :=
    .head (.seqCons rfl)        <|  -- eval (1;2)  → eval 1,  [seqK [2]]
    .head (.intLit rfl)         <|  -- eval 1      → value 1, [seqK [2]]
    .head (.seqKCons rfl rfl)   <|  -- value 1     → eval 2,  [seqK []]
    .head (.intLit rfl)         <|  -- eval 2      → value 2, [seqK []]
    .head (.seqKNil rfl rfl)    <|  -- value 2     → value 2, []
    .refl
  exact ⟨_, chain, rfl, rfl⟩

/-! ## Type-safety demonstrations (`type-safety-by-reachability.md` §3–4)

    The metatheory of `TypeSafety.lean` applied end-to-end. -/

/-- **Direction A (execution certificate, §3).** A concrete terminating run *is*
    the type-safety proof for that input: `1; 2` runs to the value `2`, a `done`
    outcome, which `done_not_typeStuck` shows is not type-stuck. No invariant.
    This is the shape of the certificate `bin/demo-qlearning --extended` produces
    for `q_learning_extended.rb` (whose run the model executes to completion,
    matching CRuby) — the general lemma is `run_value_type_safe`. -/
example :
    ∃ r, ReachableResult (Machine.init (.seq [.int 1, .int 2])) r ∧ ¬ typeStuck r :=
  run_value_type_safe (fuel := 6) (by rfl)

/-! ### Direction B (verification, §4): an inductive invariant, proved end-to-end

    `while true do nil end` — an *infinite* loop, so no fuel bound and no input
    can make it terminate, let alone type-stick. We prove it type-safe for
    **unbounded fuel and all inputs** by exhibiting a five-state inductive
    invariant and discharging Initiation / Consecution (preservation) / Safety
    (progress) — then `invariant_sound` does the rest. This is the whole
    Direction-B pipeline in miniature; for real programs the (untrusted) engine
    supplies the invariant and the trusted validator re-checks these three. -/

/-- The looping program's reachable configs, as constraints on `(ctl, kont)`
    (the heap/frames never change here). Five shapes; the last four cycle. -/
def loopInv (m : Machine) : Prop :=
  (m.ctl = .eval (.while' .tru .nil) ∧ m.kont = []) ∨
  (m.ctl = .eval .tru ∧ m.kont = [.whileCondK .tru .nil]) ∨
  (m.ctl = .value (.bool true) ∧ m.kont = [.whileCondK .tru .nil]) ∨
  (m.ctl = .eval .nil ∧ m.kont = [.whileBodyK .tru .nil]) ∨
  (m.ctl = .value .nil ∧ m.kont = [.whileBodyK .tru .nil])

theorem loop_init : loopInv (Machine.init (.while' .tru .nil)) := Or.inl ⟨rfl, rfl⟩

theorem loop_cons : ∀ m m', loopInv m → SmallStep m m' → loopInv m' := by
  intro m m' hI hstep
  rcases hI with ⟨hc, hk⟩ | ⟨hc, hk⟩ | ⟨hc, hk⟩ | ⟨hc, hk⟩ | ⟨hc, hk⟩ <;>
    simp [SmallStep, stepFn, hc, hk, evalExpr, applyKont, withKont, withCtl,
          Value.truthy] at hstep <;>
    subst hstep <;>
    simp [loopInv]

theorem loop_safe : ∀ m, loopInv m → ¬ aboutToTypeStick m := by
  intro m hI
  rcases hI with ⟨hc, hk⟩ | ⟨hc, hk⟩ | ⟨hc, hk⟩ | ⟨hc, hk⟩ | ⟨hc, hk⟩ <;>
    simp [aboutToTypeStick, typeStuck, stepFn, hc, hk, evalExpr, applyKont, withKont,
          withCtl, Value.truthy]

/-- **`while true do nil end` is type-safe** — no reachable outcome is
    type-stuck, for unbounded fuel and all inputs. The payoff of `invariant_sound`
    applied to a hand-supplied inductive invariant. -/
theorem loop_type_safe :
    ∀ r, ReachableResult (Machine.init (.while' .tru .nil)) r → ¬ typeStuck r :=
  invariant_sound loopInv loop_init loop_cons loop_safe

end Proof
end RubyCore
