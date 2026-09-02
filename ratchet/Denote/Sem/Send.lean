import Denote.Sem.Decompose

/-!
# `Denote/Sem/Send.lean` — decomposing a call's run

`Denote/Sem/Decompose.lean`'s `run_split` handles **one** pushed continuation. A call pushes a
chain of them: `.recvK` for the receiver, then one `.argsK` per argument, and only then does
`invoke` dispatch. This file walks that chain, which is what turns a run of

```
send (some recv) mname [a₁, …, aₙ] none
```

into `Evals` for the receiver, `EvalsAll` for the arguments, and a run of whatever
`finishSend` does next — i.e. into exactly the premises the call rules carry.

## The two ingredients per link

Each link needs `CatchFree K` and `JumpOpaque K` for its own literal continuation. Both are
mechanical here and for the same reason: none of these frames is a `catchK`, and `unwind`'s
**default arm** passes a jump straight through with the frame popped, which lands on
`jump_empty_never_value`. `catchFree_singleton` and `jumpOpaque_passthrough` are those two
facts once each, parameterised by the frame.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## The two ingredients, once -/

/-- A one-frame continuation that is not a `catchK` is catch-free. -/
theorem catchFree_singleton {k : Kont} (h : ∀ t, k ≠ .catchK t) :
    RubyCore.Proof.CatchFree [k] := by
  intro k' hk' t
  rcases List.mem_singleton.mp hk' with rfl
  exact h t

/-- A one-frame continuation whose `unwind` arm is the **default** one — pass the jump on with
the frame popped — is jump-opaque. The hypothesis is that arm, stated as an equation so each
use discharges it by `rfl`. -/
theorem jumpOpaque_passthrough {k : Kont}
    (h : ∀ (m : Machine) (j : Jump),
      Interp.stepFn { m with ctl := .jump j, kont := [k] }
        = .next (Interp.withCtl { m with ctl := .jump j, kont := [] } (.jump j))) :
    JumpOpaque [k] := by
  intro m j fuel v m' hrun
  match fuel with
  | 0 => exact absurd hrun (by simp [Interp.run])
  | f + 1 =>
    rw [Interp.run, h m j] at hrun
    exact jump_empty_never_value f _ v m' ⟨j, rfl⟩ rfl hrun

/-! ## The receiver link -/

/-- A call's first step: push `.recvK` and turn to the receiver — and the machine it turns to
is `evalFrom m recv` under that one frame, which is what `run_split` consumes. `rfl`. -/
theorem stepFn_send_push (m : Machine) (recv : Ratchet.Expr) (mname : String)
    (args : List Ratchet.Expr) :
    Interp.stepFn (evalFrom m (.send (some recv) mname args none))
      = .next (pushK [.recvK mname (toRubyList args) .none
          (match toRuby recv with | .self' => .selfRecv | _ => .explicit)]
        (evalFrom m recv)) := rfl

theorem catchFree_recvK (mname : String) (args : List RubyCore.Expr) (pblk : PendingBlk)
    (site : SendSite) : RubyCore.Proof.CatchFree [.recvK mname args pblk site] :=
  catchFree_singleton (by intro t h; exact absurd h (by simp))

theorem jumpOpaque_recvK (mname : String) (args : List RubyCore.Expr) (pblk : PendingBlk)
    (site : SendSite) : JumpOpaque [.recvK mname args pblk site] :=
  jumpOpaque_passthrough (fun _ _ => rfl)

theorem catchFree_argsK (recv : Value) (site : SendSite) (mname : String) (acc : List Value)
    (rest : List RubyCore.Expr) (pblk : PendingBlk) :
    RubyCore.Proof.CatchFree [.argsK recv site mname acc rest pblk] :=
  catchFree_singleton (by intro t h; exact absurd h (by simp))

theorem jumpOpaque_argsK (recv : Value) (site : SendSite) (mname : String) (acc : List Value)
    (rest : List RubyCore.Expr) (pblk : PendingBlk) :
    JumpOpaque [.argsK recv site mname acc rest pblk] :=
  jumpOpaque_passthrough (fun _ _ => rfl)

/-! ## The argument walk

`startArgs` pushes one `.argsK` per argument and `applyKont` pops it, so the chain is an
induction with `run_split` at each link. Two things the statement needs.

**`StepRunsTo`.** The states in the chain are `StepResult`s (`startArgs`/`finishSend` answer
one), not machines, so "and the rest of the run returns `v`" is phrased over a step result.
Only a `.next` can lead anywhere, which is why the definition says so rather than casing on
all five constructors.

**No splats.** `startArgs` routes a `.splat` argument through `.argsSplatK` and `spreadA`,
which delivers *several* values for one syntactic argument — and `EvalsAll`, which is what the
call rules' premise is about, pairs one value with one expression. So the walk is stated for
plain arguments, and `PlainArgs` is that hypothesis. A call rule that needs it for splats is
not a gap in this lemma; it is a question about the rule. -/

/-- The rest of the run, from a step result. -/
def StepRunsTo (r : StepResult) (v : Value) (m' : Machine) : Prop :=
  ∃ m₂, r = .next m₂ ∧ ∃ f, Interp.run f m₂ = .value v m'

/-- Turning "the run continued and returned" into `StepRunsTo`. Phrased over
`Interp.run (f+1) m` rather than over the `match` that unfolds to, because that `match` is a
matcher constant belonging to `Interp.run`'s declaration and cannot be written down here (the
lesson from `Proof/KontFrame.lean`, met from the other side). The `.done` arm is excluded by
`RubyCore.Proof`'s `.done`-comes-from-one-place chain. -/
theorem stepRunsTo_of_run {m : Machine} {f : Nat} {v : Value} {m' : Machine}
    (hnd : RubyCore.Proof.isDone (Interp.stepFn m) = false)
    (h : Interp.run (f + 1) m = .value v m') :
    StepRunsTo (Interp.stepFn m) v m' := by
  rw [Interp.run] at h
  cases hs : Interp.stepFn m with
  | next m₂ => exact ⟨m₂, rfl, f, by rw [hs] at h; exact h⟩
  | done w m₂ => rw [hs] at hnd; exact absurd hnd (by simp [RubyCore.Proof.isDone])
  | uncaught ex m₂ => rw [hs] at h; exact absurd h (by simp)
  | unsupported r => rw [hs] at h; exact absurd h (by simp)
  | stuck r => rw [hs] at h; exact absurd h (by simp)

/-- No argument is a splat, keyword bundle, or `...` forwarding — the shapes `startArgs`
routes somewhere other than one `.argsK` per argument. -/
def PlainArg : Ratchet.Expr → Prop
  | .splat _ => False
  | .kwargs _ => False
  | .fwd => False
  | _ => True

def PlainArgs (es : List Ratchet.Expr) : Prop := ∀ e ∈ es, PlainArg e

/-- **The argument walk.** From a run that starts where `applyKont` leaves the previous
delivery and returns a value: the remaining arguments each return, and the run continues from
`finishSend` with all of them. -/
theorem run_args (site : SendSite) (mname : String) (recv : Value) (pblk : PendingBlk) :
    ∀ (rest : List Ratchet.Expr) (acc : List Value) (m : Machine) (v : Value) (m' : Machine),
      m.kont = [] → PlainArgs rest →
      StepRunsTo (Interp.startArgs m recv site mname acc (toRubyList rest) pblk) v m' →
      ∃ (vs : List Value) (m₁ : Machine),
        EvalsAll m rest vs m₁ ∧ m₁.kont = [] ∧
        StepRunsTo (Interp.finishSend m₁ recv site mname (acc ++ vs) pblk) v m' := by
  intro rest
  induction rest with
  | nil =>
    intro acc m v m' hk _ h
    refine ⟨[], m, rfl, hk, ?_⟩
    have heq : Interp.startArgs m recv site mname acc (toRubyList []) pblk
        = Interp.finishSend m recv site mname acc pblk := rfl
    rw [heq] at h
    simpa using h
  | cons e rest ih =>
    intro acc m v m' hk hplain h
    -- the step: one `.argsK` for `e`, and the machine it turns to is `evalFrom m e` under it
    have hstep : Interp.startArgs m recv site mname acc (toRubyList (e :: rest)) pblk
        = .next (pushK [.argsK recv site mname acc (toRubyList rest) pblk]
            (evalFrom m e)) := by
      have hpe : PlainArg e := hplain e List.mem_cons_self
      cases e <;> first
        | exact False.elim hpe
        | (simp only [toRubyList, Interp.startArgs, Interp.withKont, pushK, evalFrom, hk,
             List.nil_append]; rfl)
        | (simp only [toRubyList, Interp.startArgs, Interp.withKont, pushK, evalFrom, hk,
             List.nil_append])
    obtain ⟨m₂, hm₂, f, hf⟩ := h
    rw [hstep] at hm₂
    cases hm₂
    -- the decomposition of `e`'s run
    obtain ⟨n, v₀, m₀, hin, hc₀, hk₀, hout⟩ :=
      run_split _ (catchFree_argsK recv site mname acc (toRubyList rest) pblk)
        (jumpOpaque_argsK recv site mname acc (toRubyList rest) pblk) f (evalFrom m e) v m' hf
    -- one step to deliver it, which pops the frame and lands back in `startArgs`
    obtain ⟨f₂, hf₂⟩ := hout
    have hdel : Interp.stepFn (deliver m₀ v₀ [.argsK recv site mname acc (toRubyList rest) pblk])
        = Interp.startArgs { m₀ with ctl := .value v₀, kont := [] } recv site mname
            (acc ++ [v₀]) (toRubyList rest) pblk := rfl
    match f₂ with
    | 0 => rw [run_zero] at hf₂; exact absurd hf₂ (by simp)
    | f₃ + 1 =>
      have hsr : StepRunsTo (Interp.stepFn
          (deliver m₀ v₀ [.argsK recv site mname acc (toRubyList rest) pblk])) v m' := by
        refine stepRunsTo_of_run ?_ hf₂
        exact RubyCore.Proof.applyKont_notDone
          (deliver m₀ v₀ [.argsK recv site mname acc (toRubyList rest) pblk]) v₀
          (by simp [deliver])
      rw [hdel] at hsr
      -- **the delivered machine *is* `m₀`**: `run_split` reports that the inner run stopped
      -- with its value in flight under an empty continuation, so the record update is `rfl`
      have hm₀ : ({ m₀ with ctl := .value v₀, kont := [] } : Machine) = m₀ := by
        rw [← hc₀, ← hk₀]
      rw [hm₀] at hsr
      obtain ⟨vs, m₁, hall, hk₁, hfin⟩ :=
        ih (acc ++ [v₀]) m₀ v m' hk₀
          (fun e' he' => hplain e' (List.mem_cons_of_mem _ he')) hsr
      refine ⟨v₀ :: vs, m₁, ⟨m₀, ⟨n, hin⟩, hall⟩, hk₁, ?_⟩
      simpa using hfin

#print axioms run_args
#print axioms jumpOpaque_recvK
#print axioms jumpOpaque_argsK

end Ratchet.Denote
