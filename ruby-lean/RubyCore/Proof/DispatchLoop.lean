/-
Direction-B (invariant) type-safety of an **unbounded dispatch loop**, fully
axiom-clean — the first `invariant_sound` proof over a program that (a) never
terminates and (b) dispatches a method every iteration (`type-safety-by-
reachability.md` §4). Unlike the Direction-A certificates (`T5Concrete`,
`QLearningTypeSafe`, which *run* the program via `native_decide`), this proof
does NOT run the program: it exhibits a finite inductive invariant over the
loop's configuration shapes and discharges init / consecution / safety.

Program:  `while true do 1.succ end`  — diverges, dispatching `Integer#succ`
forever. The machine is constant except `(ctl, kont)` (succ allocates nothing,
pushes no frame), so the reachable set is seven config shapes. The one dispatch
shape (`sF`) is handled by unfolding the (now well-founded, L52) `invoke` and
resolving `Integer#succ` in `Boot.initHeap` — a fact that is `decide`-able and
axiom-clean since `initHeap` was made kernel-reducible (L55). Hence NO
`native_decide`: this is the object-model invariant reasoning the design doc
calls the substantive obligation, over the real interpreter.

Scaling to the user-class T5 loop adds method-frame shapes (and the frame-store
grows across calls, so the invariant loosens to "frames[0] fixed, active frame
characterized"); the dispatch shape there uses `T5.dispatch_progress`. No new
blockers — this file establishes the assembly.
-/
import RubyCore.Proof.TypeSafety

namespace RubyCore
namespace Proof
namespace DispatchLoop

open Interp

-- Reducing `stepFn` over the concrete (now kernel-reducible, L55) `initHeap`
-- needs a deep recursion budget.
set_option maxRecDepth 100000

/-- `1.succ` -/
def body : Expr := .send (some (.int 1)) "succ" [] .none
/-- `while true do 1.succ end` -/
def prog : Expr := .while' .tru body
/-- The initial machine (heap = `initHeap`, one toplevel frame). -/
def base : Machine := Machine.init prog

/-- The seven reachable configuration shapes — everything but `(ctl, kont)` is
    `base` (constant: no allocation, no frame push). -/
def sA : Machine := base
def sB : Machine := { base with ctl := .eval .tru, kont := [.whileCondK .tru body] }
def sC : Machine := { base with ctl := .value (.bool true), kont := [.whileCondK .tru body] }
def sD : Machine := { base with ctl := .eval body, kont := [.whileBodyK .tru body] }
def recvKont : List Kont := [.recvK "succ" [] .none .explicit, .whileBodyK .tru body]
def sE : Machine := { base with ctl := .eval (.int 1), kont := recvKont }
def sF : Machine := { base with ctl := .value (.int 1), kont := recvKont }
def sG : Machine := { base with ctl := .value (.int 2), kont := [.whileBodyK .tru body] }

/-- The loop invariant: the config is one of the seven shapes. -/
def I (m : Machine) : Prop :=
  m = sA ∨ m = sB ∨ m = sC ∨ m = sD ∨ m = sE ∨ m = sF ∨ m = sG

/-! ### The seven transitions (each `stepFn sX = .next sY`) -/

theorem step_A : stepFn sA = .next sB := by rfl
theorem step_B : stepFn sB = .next sC := by rfl
theorem step_C : stepFn sC = .next sD := by rfl
theorem step_D : stepFn sD = .next sE := by rfl
theorem step_E : stepFn sE = .next sF := by rfl
theorem step_G : stepFn sG = .next sB := by rfl

/-- The dispatch step: `1.succ` resolves `Integer#succ` in `initHeap` and returns
    `2`. Needs the well-founded `invoke` unfolded (`invoke.eq_def`); the lookup /
    builtin computation over the reducible `initHeap` then closes by `simp`. -/
theorem step_F : stepFn sF = .next sG := by
  simp only [stepFn, sF, sG, recvKont, applyKont, startArgs, finishSend]
  rw [invoke.eq_def]
  rfl

/-! ### The inductive invariant (init / consecution / safety) -/

/-- Initiation: the initial config is shape `sA` (`= base`). -/
theorem init_I : I (Machine.init prog) := Or.inl rfl

/-- Consecution (preservation): every step maps a shape to a shape. -/
theorem cons_I : ∀ m m', I m → SmallStep m m' → I m' := by
  intro m m' hI hstep
  unfold SmallStep at hstep
  rcases hI with h | h | h | h | h | h | h <;> subst h <;>
    simp only [step_A, step_B, step_C, step_D, step_E, step_F, step_G,
               StepResult.next.injEq] at hstep <;>
    subst hstep <;> simp [I]

/-- Safety (progress): no shape is one step from a type-family `uncaught` — each
    shape steps (`.next`), and `typeStuck` holds only of `.uncaught`. -/
theorem safe_I : ∀ m, I m → ¬ aboutToTypeStick m := by
  intro m hI
  rcases hI with h | h | h | h | h | h | h <;> subst h <;>
    simp only [aboutToTypeStick, typeStuck, step_A, step_B, step_C, step_D,
               step_E, step_F, step_G, not_false_iff]

/-- **`while true do 1.succ end` is type-safe** — no reachable outcome is a
    type-family `uncaught`, for unbounded fuel — proved by an inductive invariant
    over the object model (Direction B), NOT by running the program. Axiom-clean:
    the dispatch resolution (`Integer#succ` in `initHeap`) is `decide`/`rfl`-level
    now that `initHeap` reduces (L55). -/
theorem loop_type_safe :
    ∀ r, ReachableResult (Machine.init prog) r → ¬ typeStuck r :=
  invariant_sound I init_I cons_I safe_I

end DispatchLoop
end Proof
end RubyCore
