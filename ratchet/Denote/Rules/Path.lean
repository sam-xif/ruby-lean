import Denote.Sem.Send
import Denote.Sem.Obligations

/-!
# `Denote/Rules/Path.lean` — `A::B`

`Judge.constPath` types `A::B` from the **keyed** entry `constKeyIn owner n` of the context's
constant table, where `owner` is the name behind the base's `.clsOf` type. `ConstPathsOk`
(`../Sem/State.lean`, clink 54) is the component that says the machine agrees, and it is the
one thing this rung needed that was not already on file.

## The three ways the run can go, and why only one of them types anything

`applyKont`'s `.cpathK` arm resolves the constant *inside* the container class, and the other
two outcomes cost nothing:

* the lookup **succeeds** — the value is the one `ConstPathsOk` types;
* the base is not a class, or `const_missing` is defined — `.unsupported`, so the run does not
  return and the obligation's hypothesis is unsatisfiable;
* the constant is **missing or private** — `raiseErr`, i.e. a jump at an empty continuation,
  which `../Sem/Decompose.lean`'s `jump_empty_never_value` says never returns a value.

The private case is the interesting one: the rule's premise is that the *context* does not mark
the key private, and `PrivConstsOk` deliberately claims nothing about the machine
("hiding a constant can only make the checker refuse a program"). So this rung does not learn
that the machine agrees — it does not need to, because a machine that hides it raises.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

theorem stepFn_cpath_push (m : Machine) (base : Ratchet.Expr) (n : String) :
    Interp.stepFn (evalFrom m (.cpath (some base) n))
      = .next (pushK [.cpathK n] (evalFrom m base)) := rfl

theorem catchFree_cpathK (n : String) : RubyCore.Proof.CatchFree [.cpathK n] :=
  catchFree_singleton (by intro t h; exact absurd h (by simp))

theorem jumpOpaque_cpathK (n : String) : JumpOpaque [.cpathK n] :=
  jumpOpaque_passthrough (fun _ _ => rfl)

/-! ## The rung -/

/-! ## Where this rung stands

The ingredients above are proved; the tail is not, and what is left is plumbing rather than
content. `applyKont`'s `.cpathK` arm has three outcomes and the rung needs one fact about each:

* **hit** — `constLookupFrom` answers, and `ConstPathsOk` (`../Sem/State.lean`) types the
  value. That component is the piece this rung was actually missing, and it is in.
* **gate** — the base defines `const_missing`, so the step is `.unsupported` and the run does
  not return.
* **miss or private** — `raiseErr`, i.e. a jump at an empty continuation, which
  `../Sem/Decompose.lean`'s `jump_empty_never_value` says never returns a value. Note the
  private case needs no machine-side conformance: `PrivConstsOk` deliberately claims nothing
  ("hiding a constant can only make the checker refuse a program"), and a machine that hides
  the constant *raises*, which is outside the obligation.

What stalled is stepping `applyKont`'s arm: the arm's `hasCM` is a `let`, its `isPrivate` is a
`let`, and the resulting `if`s sit inside the scrutinee of `run`'s five-arm match — so `split`
picks the wrong one, `rw [if_pos …]` does not find the pattern the source's elaboration
produced, and the `simp only [...]; rfl` that closes the *whole-arm* equation does not survive
being specialised to one branch. The fix is a `cases hcm : …` on each condition *in the
hypothesis* rather than in the goal; the shape is the same as `Decompose.lean`'s `throwJ` arm.
-/

#print axioms jumpOpaque_cpathK

end Ratchet.Denote
