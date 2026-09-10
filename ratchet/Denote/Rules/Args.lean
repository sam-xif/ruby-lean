import Denote.Rules.Core
import Denote.Join
import Denote.Sem.Obligations

/-!
# `Denote/Rules/Args.lean` — the two list `cons` rungs, and why they never needed the wall

`JudgeAll.cons` and `JudgeKw.pair` are the inductive step of an argument list: type the head,
then the tail, threading the state. Both were filed behind the **fifth** stall point (the
continuation wall) and both are here, because that filing was wrong in the direction that
costs rungs — and the correction is worth stating, since it is the same mistake `Nil.lean`
records for `JudgeSeq.last`.

**`EvalsAll` is compositional.** Its `cons` arm reads

```
EvalsAll m (e :: es) (v :: vs) m' = ∃ m₁, Evals m e v m₁ ∧ EvalsAll m₁ es vs m'
```

so each element's run is an `Evals` — under an **empty** continuation, at successive machines
— and a hypothesis of that shape *is* the two premises' hypotheses. Nothing here has to relate
a run under a pushed `argsK` to a run under `[]`, which is what the wall is about. The wall
does block the *consumer* (`Judge.arrayLit`'s own run pushes `arrK` per element, `Judge.prim`'s
pushes `argsK`), and that is where it belongs.

**What did block them is the seventh stall point**, and clink 53 fixed it in the definition:
`SemJudgeAll` used to conclude `DenAll τs m' vs` — every argument's type at the machine the
*whole list* left behind — so this rung would have had to transport `denM τ m₁ v` across the
evaluation of every later argument, and no such transport exists. `DenAllAt`
(`Denote/Sem/Judge.lean`) states each element's type at its own post-machine instead, which is
what an argument list's evaluation actually establishes; the transport moves to the rules that
use the values, where `PrimSig`'s no-mutator property can be argued explicitly rather than
depended on invisibly.

With that, each rung is four lines: destructure the value list (a length mismatch makes
`EvalsAll` `False`), spend the head premise at `m`, spend the tail premise at `m₁`, and
compose. The `m'.stack = m.stack` conjunct is the two halves' transitivity — the first place
on the ladder where frame balance is *composed* rather than read off one step.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## Positional arguments -/

theorem Sem.JudgeAll.cons : Obl.JudgeAll.cons := by
  intro κ Γ Γ₁ Γ₂ I I₁ I₂ e es τ τs hhead htail
  -- plainness of the list is the head's own (from `SemJudge`) plus the tail's
  refine ⟨fun e' he' => by
    rcases List.mem_cons.mp he' with h | h
    · exact h ▸ hhead.1
    · exact htail.1 e' h, ?_⟩
  intro m hm vs m' hev
  cases vs with
  | nil => exact absurd hev (by simp [EvalsAll])
  | cons v vs =>
    obtain ⟨m₁, hEv, hRest⟩ := hev
    obtain ⟨hst, hden, hok₁, -⟩ := hhead.2 m hm v m₁ hEv
    obtain ⟨hst', hall, hok₂⟩ := htail.2 m₁ hok₁ vs m' hRest
    exact ⟨hst.trans hst', ⟨m₁, hEv, hden, hall⟩, hok₂⟩

/-! ## Keyword arguments

`JudgeKw`'s step is called `pair` rather than `cons` (only `KwEntry.pair` has a rule — see
that inductive's docstring for the two recorded gaps), and its expression list is *recovered*
from the entries by `kwExprs`, so the one extra move is unfolding that at a `.pair` head. -/

theorem Sem.JudgeKw.pair : Obl.JudgeKw.pair := by
  intro κ Γ Γ₁ Γ₂ I I₁ I₂ k v τ es kws hhead htail
  first
    | refine ⟨by first | trivial | simp [PlainAll, Plain]
                       | simp_all [PlainAll, Plain], ?_⟩
    | skip
  intro m hm vs m' hev
  rw [kwExprs] at hev
  cases vs with
  | nil => exact absurd hev (by simp [EvalsAll])
  | cons w vs =>
    obtain ⟨m₁, hEv, hRest⟩ := hev
    obtain ⟨hst, hden, hok₁, -⟩ := hhead.2 m hm w m₁ hEv
    obtain ⟨hst', hall, hok₂⟩ := htail m₁ hok₁ vs m' hRest
    refine ⟨hst.trans hst', ?_, hok₂⟩
    rw [kwExprs]
    exact ⟨m₁, hEv, hden, hall⟩

/-! ## Hash pairs

`JudgePairs.cons` threads key, then value, then the rest, and its conclusion widens both types
to a **join** — so this rung is the two list moves above plus the join's upper-bound property
(`Denote/Join.lean`), twice, and once more under an induction: the tail premise gives
`DenPairsAt` at `(kr, vr)` while the conclusion asks for it at `(joinT σ kr, joinT ν vr)`, and
weakening the types of an already-established walk is `denPairsAt_mono`.

The interleaved order is what makes it go through at all; see `SemJudgePairs`. -/

/-- Widening both type indices of an established pair walk. One induction; every step is
`denM_joinT_right`, because the *tail*'s types are the join's right branch. -/
theorem denPairsAt_mono {σ ν : Ty} : ∀ (ps : List (Ratchet.Expr × Ratchet.Expr))
    {kr vr : Ty} {m m' : Machine} {vals : List Value},
    DenPairsAt m ps kr vr vals m' → DenPairsAt m ps (joinT σ kr) (joinT ν vr) vals m'
  | [], _, _, _, _, vals, h => by
    cases vals with
    | nil => exact h
    | cons a as => exact absurd h (by simp [DenPairsAt])
  | (k, v) :: ps, kr, vr, m, m', vals, h => by
    match vals with
    | [] => exact absurd h (by simp [DenPairsAt])
    | [_] => exact absurd h (by simp [DenPairsAt])
    | kv :: vv :: vals =>
      obtain ⟨m₁, hk, hkd, m₂, hv, hvd, hrest⟩ := h
      exact ⟨m₁, hk, denM_joinT_right hkd, m₂, hv, denM_joinT_right hvd,
             denPairsAt_mono ps hrest⟩

theorem Sem.JudgePairs.cons : Obl.JudgePairs.cons := by
  intro κ Γ Γ₁ Γ₂ Γ₃ I I₁ I₂ I₃ k v ps σ ν kr vr hkey hval htail
  first
    | refine ⟨by first | trivial | simp [PlainAll, Plain]
                       | simp_all [PlainAll, Plain], ?_⟩
    | skip
  intro m hm vals m' hev
  rw [pairExprs] at hev
  match vals with
  | [] => exact absurd hev (by simp [EvalsAll])
  | [_] =>
    obtain ⟨m₁, _, hrest⟩ := hev
    exact absurd hrest (by simp [EvalsAll])
  | kv :: vv :: vals =>
    obtain ⟨m₁, hEk, m₂, hEv, hRest⟩ := hev
    obtain ⟨hst₁, hkd, hok₁, -⟩ := hkey.2 m hm kv m₁ hEk
    obtain ⟨hst₂, hvd, hok₂, -⟩ := hval.2 m₁ hok₁ vv m₂ hEv
    obtain ⟨hst₃, hall, hok₃⟩ := htail m₂ hok₂ vals m' hRest
    refine ⟨(hst₁.trans hst₂).trans hst₃, ?_, hok₃⟩
    rw [DenPairsAt]
    exact ⟨m₁, hEk, denM_joinT_left hkd, m₂, hEv, denM_joinT_left hvd,
           denPairsAt_mono ps hall⟩

#print axioms Sem.JudgeAll.cons
#print axioms Sem.JudgeKw.pair
#print axioms Sem.JudgePairs.cons

end Ratchet.Denote
