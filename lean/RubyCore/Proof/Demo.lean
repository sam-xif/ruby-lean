/-
Smoke-test demonstrations for the control-core `Step` relation: the relation is
non-vacuous, it *computes*, and adequacy applies to real initial configs. These
`example`s double as regression tests that the constructors actually fire.
-/
import RubyCore.Proof.Adequacy

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
  · intro k hk; simp [Machine.init] at hk
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

end Proof
end RubyCore
