import RubyCore.Interp
import Books.Metatheory.Machine.NotDoneAttr

set_option maxHeartbeats 40000000 in
/-!
# `Books/Metatheory/Machine/NotDone.lean` — `.done` comes from exactly one place

`StepResult.done` is constructed at **one** site in the interpreter (`applyKont`'s empty-
continuation arm), and `applyKont` is called from **one** place (`stepFn`). So no helper can
produce it — and that fact, mechanical as it is, is what lets a run be *inverted*:

    stepFn m = .done v m'  →  m.ctl = .value v ∧ m.kont = [] ∧ m' = m

which is the inversion the run-level decomposition needs. Without it, "the isolated sub-run
stopped here" says nothing about *where* here is, and the pushed run cannot be continued from
the corresponding state.

The chain is the framing chain again, minus `Builtins` (which returns `BRes`, not
`StepResult`) and minus the two-sided matching that made framing expensive: every goal here
has one side.
-/

set_option autoImplicit true
set_option maxRecDepth 400000

namespace RubyCore
namespace Proof

open Builtins
open Interp

set_option maxHeartbeats 40000000 in
/-- Is this step result the run's own end? -/
def isDone : StepResult → Bool
  | .done _ _ => true
  | _ => false

/-- …lifted to the `try*` family's `Option StepResult` (`none` = "not mine, fall through").
A `Bool` on the *goal* side rather than a `∀ sr, … = some sr → …`, because then the walker's
`split` works on the goal and needs no `at h` — which is what the first attempt got wrong. -/
def isDoneO : Option StepResult → Bool
  | some sr => isDone sr
  | none => false

/-- …and to `cpathContainer`, whose *error* side is a step result. -/
def isDoneE {α : Type} : Except StepResult α → Bool
  | .error sr => isDone sr
  | .ok _ => false

/-! ### The reduction lemmas, and why they are lemmas

Passing `isDone` itself to `simp` **unfolds it into its matcher**, which destroys the head
symbol every callee's lemma is keyed on — the goal becomes
`(match callClosure … with | .done _ _ => true | _ => false) = false` and nothing matches it.
So `isDone` is never in a simp set here; these nine `rfl`s are, and the walker runs a bare
`simp`. -/

@[simp, ndLem] theorem isDone_next (m : Machine) : isDone (.next m) = false := rfl
@[simp, ndLem] theorem isDone_done (v : Value) (m : Machine) : isDone (.done v m) = true := rfl
@[simp, ndLem] theorem isDone_uncaught (v : Value) (m : Machine) : isDone (.uncaught v m) = false := rfl
@[simp, ndLem] theorem isDone_unsupported (r : String) : isDone (.unsupported r) = false := rfl
@[simp, ndLem] theorem isDone_stuck (r : String) : isDone (.stuck r) = false := rfl
@[simp, ndLem] theorem isDoneO_none : isDoneO none = false := rfl
@[simp, ndLem] theorem isDoneO_some (sr : StepResult) : isDoneO (some sr) = isDone sr := rfl
@[simp, ndLem] theorem isDoneE_ok {α : Type} (a : α) : isDoneE (Except.ok a : Except StepResult α) = false := rfl
@[simp, ndLem] theorem isDoneE_error {α : Type} (sr : StepResult) :
    isDoneE (Except.error sr : Except StepResult α) = isDone sr := rfl

@[simp, ndLem] theorem isDone_ite (p : Prop) [Decidable p] (a b : StepResult) :
    isDone (if p then a else b) = if p then isDone a else isDone b := by
  split <;> rfl

@[simp, ndLem] theorem isDoneO_ite (p : Prop) [Decidable p] (a b : Option StepResult) :
    isDoneO (if p then a else b) = if p then isDoneO a else isDoneO b := by
  split <;> rfl

@[simp, ndLem] theorem isDoneE_ite {α : Type} (p : Prop) [Decidable p] (a b : Except StepResult α) :
    isDoneE (if p then a else b) = if p then isDoneE a else isDoneE b := by
  split <;> rfl

/-- The bridge for the `try*` family's callers. `split` on `match tryReflect … with | some sr
=> sr | none => …` leaves the goal `isDone sr = false` and the *hypothesis*
`tryReflect … = some sr`; the callee's lemma is about `isDoneO (tryReflect …)`, a term the goal
no longer contains. Taking the hypothesis **first** lets `assumption` find it and fix `o`, and
then `simp` proves the callee's lemma at that `o`. One walker alternative covers every caller
in the file. -/
theorem isDone_of_optNotDone {o : Option StepResult} {sr : StepResult}
    (h : o = some sr) (hnd : isDoneO o = false) : isDone sr = false := by
  rw [h] at hnd; exact hnd

/-- …and the same for `cpathContainer`'s error side. -/
theorem isDone_of_excNotDone {α : Type} {e : Except StepResult α} {sr : StepResult}
    (h : e = .error sr) (hnd : isDoneE e = false) : isDone sr = false := by
  rw [h] at hnd; exact hnd

@[simp, ndLem] theorem isDoneO_or {a b : Option StepResult}
    (ha : isDoneO a = false) (hb : isDoneO b = false) : isDoneO (a.or b) = false := by
  cases a <;> simp_all

@[simp, ndLem] theorem isDoneO_orElse {a : Option StepResult} {b : Unit → Option StepResult}
    (ha : isDoneO a = false) (hb : ∀ u, isDoneO (b u) = false) :
    isDoneO (a.orElse b) = false := by
  cases a <;> simp_all [Option.orElse]

@[ndLem] theorem isDoneO_orElse_const {a b : Option StepResult}
    (ha : isDoneO a = false) (hb : isDoneO b = false) :
    isDoneO (a.orElse (fun _ => b)) = false := by
  exact isDoneO_orElse ha (fun _ => hb)

@[simp, ndLem] theorem isDone_getD {a : Option StepResult} {fallback : StepResult}
    (ha : isDoneO a = false) (hf : isDone fallback = false) :
    isDone (a.getD fallback) = false := by
  cases a <;> simp_all

/-- The walker. One side, so `split` cannot desynchronise anything, and `simp` closes each arm
against the callees' lemmas — all tagged `@[simp, ndLem]`, which is why the order of this file is the
call graph's. -/
elab "nd_unfold_private" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  let some (_, lhs, _) := target.eq? | Lean.throwError "no private helper at the goal head"
  let .app _ arg := lhs | Lean.throwError "no private helper at the goal head"
  let .const name _ := arg.getAppFn | Lean.throwError "no private helper at the goal head"
  unless name.toString.startsWith "_private." do Lean.throwError "no private helper at the goal head"
  Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $(Lean.mkIdent name)))

syntax "nd_walk" : tactic
macro_rules
  | `(tactic| nd_walk) =>
    `(tactic| ((try dsimp only) <;> (try simp only [ndLem, ite_self]) <;>
              first
                | assumption
                | (nd_unfold_private; nd_walk)
                | exact isDone_of_optNotDone (by assumption) (by simp only [ndLem, ite_self])
                | exact isDone_of_excNotDone (by assumption) (by nd_walk)
                | (split <;> nd_walk)))



end Proof
end RubyCore
