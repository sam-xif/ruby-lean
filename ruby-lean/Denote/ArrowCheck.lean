import Denote.Arrow
import Denote.DenB

/-!
# `Denote/ArrowCheck.lean` — refuting an arrow by running it

`ArrowFlat` (`Denote/Arrow.lean`) quantifies over every argument in the domain and every
fuel, so no `Bool` decides it — `Denote/DenB.lean` answers `false` on both arrow arms for
exactly that reason. What *is* computable is the **refutation**: pick some arguments, run the
proc, look at what came back. If the result is outside the codomain, the arrow is false, and
the argument tuple is the counterexample.

That is the same shape as the rest of this project's checking story — the bounded-effect-checking note's
bounded model checker and `AGENTS.md` §Type safety as reachability's witness-finding direction both
run the semantics to *find* a bad state rather than to prove there is none — applied to
arrows. `arrowCheck` is therefore stated and proved in the only direction that is honest:

* `arrowCheck_of_arrowFlat` — a true arrow passes every sample. So a **failing sample refutes
  the arrow** (the contrapositive, `not_arrowFlat_of_arrowCheck_false`), and the sample that
  failed is the witness.
* There is deliberately **no** converse. Passing samples say nothing; a fuel-limited run that
  did not finish says nothing either. Both are recorded in `arrowCheck`'s own definition as
  *skips*, not as passes.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-- Do these argument values satisfy the declared domain, as far as the computable core can
tell? `denB`'s one-sidedness means a `false` here only *skips* the sample. -/
def domOkB (ps : List Ty) (h : Heap) : List Value → Bool
  | [] => ps.isEmpty
  | v :: vs => match ps with
    | [] => false
    | p :: ps' => denB p h v && domOkB ps' h vs

/-- One sample. `true` means "no counterexample here", which covers three genuinely
different situations and it is worth naming them:

* the arguments are not (provably) in the domain — nothing was promised, **skip**;
* the call did not return a value within `fuel` (raised, diverged, gated, jumped) — the arrow
  says nothing about such a run (`Denote/Den.lean` §The arrow arm, point 1), **skip**;
* the call returned a value and `denB` accepts it at the *post* heap — a real, if bounded,
  **pass**.

Only the fourth case, "returned a value `denB` rejects", answers `false`. -/
def arrowSample (fuel : Nat) (ps : List Ty) (r : Ty) (m : Machine) (f : Value)
    (args : List Value) : Bool :=
  if domOkB ps m.heap args then
    match Interp.run fuel (applyIn m f args) with
    | .value v m' => denB r m'.heap v
    | _ => true
  else true

/-- The bounded check: `f` is a Proc and no sample refutes the arrow. -/
def arrowCheck (fuel : Nat) (ps : List Ty) (r : Ty) (m : Machine) (f : Value)
    (samples : List (List Value)) : Bool :=
  isProcV m.heap f && samples.all (fun args => arrowSample fuel ps r m f args)

/-- `denB`-provable domain membership really is domain membership — `denB_soundM` lifted to an
argument list, which is what lets a sample's precondition discharge `ArrowFlat`'s hypothesis. -/
theorem denAll_of_domOkB : ∀ (ps : List Ty) (m : Machine) (args : List Value),
    domOkB ps m.heap args = true → DenAll ps m args
  | [], _, [], _ => trivial
  | [], _, _ :: _, hd => by simp [domOkB] at hd
  | _ :: _, _, [], hd => by simp [domOkB] at hd
  | p :: ps, m, v :: vs, hd => by
    simp only [domOkB, Bool.and_eq_true] at hd
    exact ⟨denB_soundM m v hd.1, denAll_of_domOkB ps m vs hd.2⟩

/-- **A true arrow passes every sample.** The codomain hypothesis `FirstOrder r` is where the
computable core's limit shows up: `denB` can only *confirm* a first-order result type, so a
higher-order codomain has nothing to check against and this theorem would be vacuous. -/
theorem arrowCheck_of_arrowFlat {fuel : Nat} {ps : List Ty} {r : Ty} {m : Machine}
    {f : Value} {samples : List (List Value)} (hr : FirstOrder r = true)
    (ha : ArrowFlat ps r m f) : arrowCheck fuel ps r m f samples = true := by
  simp only [arrowCheck, Bool.and_eq_true, List.all_eq_true]
  refine ⟨ha.1, fun args _ => ?_⟩
  simp only [arrowSample]
  split
  · next hd =>
    split
    · next v m' hrun =>
      exact (denB_iff hr m'.heap v).mpr
        ((den_iff_denM hr m' v).mpr (ha.2 args (denAll_of_domOkB ps m args hd) v m' ⟨fuel, hrun⟩))
    · rfl
  · rfl

/-- **The usable direction**: a failed check refutes the arrow. The `samples` list that
produced the `false` *is* the counterexample — which sample failed is read off by re-running
`arrowSample`, exactly as `AGENTS.md` §Type safety as reachability's witness direction reads its
trace off the run that found it. -/
theorem not_arrowFlat_of_arrowCheck_false {fuel : Nat} {ps : List Ty} {r : Ty} {m : Machine}
    {f : Value} {samples : List (List Value)} (hr : FirstOrder r = true)
    (hc : arrowCheck fuel ps r m f samples = false) : ¬ ArrowFlat ps r m f := by
  intro ha
  rw [arrowCheck_of_arrowFlat hr ha] at hc
  exact Bool.noConfusion hc

#print axioms denAll_of_domOkB
#print axioms arrowCheck_of_arrowFlat
#print axioms not_arrowFlat_of_arrowCheck_false

end Ratchet.Denote
