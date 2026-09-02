import Denote.Rules.Never
import Denote.Sem.Query

/-!
# `Denote/Rules/Raise.lean` — `raise C` / `raise C, "msg"`

`Judge.raiseCls` concludes **`Ty.never`**, so this rung is in the family
`Denote/Rules/Never.lean` opened: the obligation is discharged by *contradicting the run*
rather than by typing a value. What makes it a different amount of work from `callNever` is
that the contradiction is not about the arguments — they type fine — but about the dispatch: a
`raise` that reaches `Kernel#raise` cannot return, and this file is the proof of that for every
path out of it.

`raiseImpl` has five arms and **none of them answers `.ok`**: `.throwV` for an exception object
or class, `.err` for a `TypeError`/`RuntimeError`, `.unsupported` past arity two. So the
builtin's own contribution is one `cases`. The interesting path is the other one.

## `raiseNewK`, and why the interception is not a hole

`raise C` where `C` has a **user `initialize`** cannot be finished by a builtin: CRuby builds
the exception with `C.new(…)`, so the initializer has to run, and that is a frame
`Builtins.run` cannot push. `Interp/Send.lean` therefore allocates the instance, pushes a
`.raiseNewK inst` continuation and enters the method — so a value *does* come back, from an
arbitrary user body.

It still cannot escape, and the reason is the shape of the kont: `applyKont` at `.raiseNewK`
turns whatever value arrives into `.jump (.raiseJ inst)`. So `raiseNewK` is **value-opaque**,
and the two lemmas below say exactly that — one for a value arriving (it becomes a jump, and a
jump at an empty continuation never returns) and one for a jump arriving (`unwind` passes it
through). With `run_split` those cover the whole activation without knowing anything about the
`initialize` body, which is what keeps this rung out of the call family's way.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## `raiseNewK` is value-opaque -/

/-- The `.raiseNewK` continuation contains no catcher, so `run_split` applies to it. -/
theorem catchFree_raiseNewK (inst : Value) :
    RubyCore.Proof.CatchFree [Kont.raiseNewK inst] := by
  intro k hk
  simp only [List.mem_singleton] at hk
  rw [hk]
  intro t
  simp

/-- …and it does not turn an escaping jump into a value: `unwind`'s default arm pops it and
lands on `jump_empty_never_value`, exactly as `asgnK` does. -/
theorem jumpOpaque_raiseNewK (inst : Value) : JumpOpaque [Kont.raiseNewK inst] := by
  intro m j fuel v m' h
  match fuel with
  | 0 => exact absurd h (by simp [Interp.run])
  | f + 1 =>
    rw [Interp.run] at h
    have hs : Interp.stepFn { m with ctl := .jump j, kont := [Kont.raiseNewK inst] }
        = .next (Interp.withCtl { m with ctl := .jump j, kont := [] } (.jump j)) := rfl
    rw [hs] at h
    exact jump_empty_never_value f _ v m' ⟨j, rfl⟩ rfl h

/-- **A value delivered to `raiseNewK` becomes a raise**, and a raise at an empty continuation
never returns. This is the arm that makes the user `initialize` irrelevant. -/
theorem raiseNewK_no_value (inst : Value) (m : Machine) (hk : m.kont = [])
    (w : Value) (fuel : Nat) (v : Value) (m' : Machine) :
    Interp.run fuel (deliver m w [Kont.raiseNewK inst]) ≠ .value v m' := by
  match fuel with
  | 0 => simp [Interp.run]
  | f + 1 =>
    rw [Interp.run]
    have hs : Interp.stepFn (deliver m w [Kont.raiseNewK inst])
        = .next (Interp.withCtl (deliver m w []) (.jump (.raiseJ inst))) := rfl
    rw [hs]
    exact jump_empty_never_value f _ v m' ⟨_, rfl⟩ rfl


/-! ## `Kernel#raise` never answers with a value

`Builtins.run`'s prologue is the usual three gates, and `Object#raise`'s own arm is
`raiseImpl`, whose five arms are `.throwV`, `.err` and `.unsupported` — no `.ok` anywhere. So
the statement is a *negative* one, which is what the rung wants. -/

theorem runObjects_raise (m : Machine) (recv : Value) (args : List Value) :
    Builtins.runObjects "Object#raise" recv args m = Builtins.raiseImpl m args := rfl

/-- `raiseClass` — the `raise C[, msg]` core — with the same three outcomes: a class outside
`Exception`'s chain is a `TypeError`, and otherwise the exception is allocated and **thrown**.
`allocExc` only grows the heap, so the continuation is untouched. -/
theorem raiseClass_outcome (m : Machine) (cls : ObjId) (msg : Option Value) :
    (∃ c s m₂, Builtins.raiseClass m cls msg = .err c s m₂ ∧ m₂.kont = m.kont) ∨
    (∃ w m₂, Builtins.raiseClass m cls msg = .throwV w m₂ ∧ m₂.kont = m.kont) ∨
    (∃ r, Builtins.raiseClass m cls msg = .unsupported r) := by
  rw [Builtins.raiseClass.eq_def]
  split
  · exact Or.inl ⟨_, _, _, rfl, rfl⟩
  · cases msg with
    | none => exact Or.inr (Or.inl ⟨_, _, rfl, rfl⟩)
    | some w =>
      dsimp only
      cases h : Builtins.toSP m w with
      | ok s => exact Or.inr (Or.inl ⟨_, _, rfl, rfl⟩)
      | error e => exact Or.inr (Or.inr ⟨_, rfl⟩)

/-- **The three outcomes of `Kernel#raise`, with the continuation carried along.** Stated as
one disjunction rather than as "never `.ok`" plus two preservation lemmas, because all three
facts come out of the same walk — and the continuation is needed: `jump_empty_never_value`
asks for it, and `Builtins.run`'s own frame lemma (`RubyCore.Proof.run_frame`) gives
commutation with a *push*, not preservation. -/
theorem run_raise_outcome (m : Machine) (recv : Value) (args : List Value) :
    (∃ c s m₂, Builtins.run "Object#raise" recv args m = .err c s m₂ ∧ m₂.kont = m.kont) ∨
    (∃ w m₂, Builtins.run "Object#raise" recv args m = .throwV w m₂ ∧ m₂.kont = m.kont) ∨
    (∃ r, Builtins.run "Object#raise" recv args m = .unsupported r) := by
  rw [Builtins.run.eq_def]
  dsimp only
  split
  · exact Or.inr (Or.inr ⟨_, rfl⟩)
  split
  · exact Or.inl ⟨_, _, _, rfl, rfl⟩
  split
  · rename_i hd
    exact absurd hd (by simp [Builtins.dupBids, Builtins.cloneBids])
  rw [runObjects_raise, Builtins.raiseImpl.eq_def]
  rcases args with _ | ⟨a, rest⟩
  · dsimp only
    cases m.currentExc with
    | none => exact Or.inl ⟨_, _, _, rfl, rfl⟩
    | some e => exact Or.inr (Or.inl ⟨_, _, rfl, rfl⟩)
  · rcases rest with _ | ⟨b, rest2⟩
    · cases a with
      | ref o =>
        cases hp : (m.heap.get o).payload <;> simp only [hp] <;>
          first
            | exact raiseClass_outcome m o none
            | exact Or.inr (Or.inl ⟨_, _, rfl, rfl⟩)
            | exact Or.inl ⟨_, _, _, rfl, rfl⟩
      | _ => exact Or.inl ⟨_, _, _, rfl, rfl⟩
    · rcases rest2 with _ | ⟨c, rest3⟩
      · cases a with
        | ref o =>
          cases hp : (m.heap.get o).payload <;> simp only [hp] <;>
            first
              | exact raiseClass_outcome m o (some b)
              | exact Or.inl ⟨_, _, _, rfl, rfl⟩
        | _ => exact Or.inl ⟨_, _, _, rfl, rfl⟩
      · exact Or.inr (Or.inr ⟨_, rfl⟩)

#print axioms run_raise_outcome



/-- **A machine whose continuation *ends* with `Kout` is a `pushK` of one that does not.**
The trick that keeps `run_split` usable here: the `raiseNewK` path's machine comes out of
`enterUserMethod`, which pushes a frame, folds the parameter locals in and sets `ctl` — writing
that machine down to feed `pushK` would be transcribing the whole definition. This lemma reads
it off the continuation instead. -/
theorem pushK_of_kont_append {m : Machine} {K Kout : List Kont} (h : m.kont = K ++ Kout) :
    m = pushK Kout { m with kont := K } := by
  simp only [pushK]
  rw [← h]

/-! ## The dispatch: every path out of `invokeDispatch` at `raise` is jump- or gate-shaped

Four outcomes, and the rung needs all four to produce **no value**:

* the builtin runs and answers `.err`/`.throwV`/`.unsupported` — a `raiseErr`, a raise-jump, or
  a gate (`run_raise_not_ok` is what excludes the fifth possibility);
* the `raiseNewK` interception runs a user `initialize` — handled by the two opacity lemmas
  above rather than by looking at the body;
* the lookup misses — `dispatchMiss`, which `QueryOk`'s second clause makes a `raiseErr`;
* a visibility or shadow gate — `.unsupported`.

Stated as "the step is not `.next` of a machine with a value in flight at an empty
continuation", which is the form the rung's `Evals` inversion consumes. -/

theorem deferTwin?_raise (h : Heap) (recv : Value) (args : List Value) :
    Builtins.deferTwin? h "Object#raise" recv args = none := by
  simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
    Builtins.toAryDefer?, Builtins.coerceTwin?]
  rcases args with _ | ⟨a, rest⟩
  · rfl
  · cases rest <;> rfl

theorem invoke_raise (m : Machine) (recv : Value) (site : SendSite) (args : List Value)
    (kw : List (Value × Value)) :
    Interp.invoke m recv site "raise" args none kw
      = Interp.invoke.invokeDispatch m recv site "raise" args none kw := by
  rw [Interp.invoke.eq_def]
  cases recv with
  | ref o =>
    cases hp : (m.heap.get o).payload <;> simp only [hp] <;>
      first
        | rfl
        | (split <;> simp_all [Interp.invoke.invokeMaybeNew.eq_def])
        | simp_all [Interp.invoke.invokeMaybeNew.eq_def]
  | _ => rfl


/-- **A run that starts under a continuation ending in `raiseNewK` never returns a value.**
`run_split` does the work: either the inner activation reaches a value at an empty
continuation — and then the delivery to `raiseNewK` turns it into a raise
(`raiseNewK_no_value`) — or it never does. Nothing about the user `initialize` body is
needed, which is the point. -/
theorem run_raiseNew_no_value (inst : Value) (X : Machine) (fuel : Nat) (v : Value)
    (m' : Machine) :
    Interp.run fuel (pushK [Kont.raiseNewK inst] X) ≠ .value v m' := by
  intro h
  obtain ⟨n, v₀, m₀, hin, hc₀, hk₀, f₂, hf₂⟩ :=
    run_split [Kont.raiseNewK inst] (catchFree_raiseNewK inst) (jumpOpaque_raiseNewK inst)
      fuel X v m' h
  exact raiseNewK_no_value inst m₀ hk₀ v₀ f₂ v m' hf₂

#print axioms run_raiseNew_no_value




#print axioms invoke_raise

#print axioms catchFree_raiseNewK
#print axioms jumpOpaque_raiseNewK
#print axioms raiseNewK_no_value



/-- **The `raiseNewK` activation never returns a value.** `enterUserMethod` is not inspected:
`RubyCore.Proof.enterUserMethod_frame` is an *equation* — entering a method under an appended
continuation is entering it and appending — so the whole activation is a `pushK
[raiseNewK inst]` of one that knows nothing about it, and `run_raiseNew_no_value` closes it.

This is the payoff of clink 54's frame layer arriving in a rung that is not about frames. -/
theorem enterUserMethod_raiseNew_no_value (inst : Value) (M : Machine) (recv : Value)
    (md : MethodDef) (args : List Value) (hk : M.kont = [Kont.raiseNewK inst])
    (v : Value) (m' : Machine) :
    ¬ StepRunsTo (Interp.enterUserMethod M recv "initialize" md args none) v m' := by
  intro hsr
  obtain ⟨m₂, hstep, f, hf⟩ := hsr
  have hM : M = pushK [Kont.raiseNewK inst] { M with kont := [] } :=
    pushK_of_kont_append (K := []) (Kout := [Kont.raiseNewK inst]) (by simpa using hk)
  -- `Denote`'s `pushK` and `RubyCore.Proof`'s are the same function (`pushK_eq`), and the
  -- frame lemma is stated over the latter
  rw [hM, pushK_eq, RubyCore.Proof.enterUserMethod_frame] at hstep
  cases hr : Interp.enterUserMethod { M with kont := [] } recv "initialize" md args none with
  | next N =>
    rw [hr] at hstep
    simp only [RubyCore.Proof.frameR] at hstep
    injection hstep with hstep
    rw [← hstep] at hf
    exact run_raiseNew_no_value inst N f v m' hf
  | done w N => rw [hr] at hstep; exact absurd hstep (by simp [RubyCore.Proof.frameR])
  | unsupported r => rw [hr] at hstep; exact absurd hstep (by simp [RubyCore.Proof.frameR])
  | uncaught w N => rw [hr] at hstep; exact absurd hstep (by simp [RubyCore.Proof.frameR])
  | stuck r => rw [hr] at hstep; exact absurd hstep (by simp [RubyCore.Proof.frameR])

#print axioms enterUserMethod_raiseNew_no_value

/-- **The builtin outcome produces no value.** Written as a lemma over the *four* `BRes` arms
rather than inline, because the `match` in `Interp/Send.lean` belongs to that declaration and
cannot be written down here — so the arms are reached by `cases` on the result and the four
goals are closed uniformly. -/
theorem builtin_raise_no_value (m : Machine) (recv : Value) (args : List Value)
    (hk : m.kont = []) (v : Value) (m' : Machine) :
    ¬ StepRunsTo (match Builtins.run "Object#raise" recv args m with
        | .ok w m₂ => .next (Interp.withCtl m₂ (.value w))
        | .err cls msg m₂ => .next (Interp.raiseErr m₂ cls msg)
        | .throwV w m₂ => .next (Interp.withCtl m₂ (.jump (.raiseJ w)))
        | .unsupported r => .unsupported r) v m' := by
  intro hsr
  rcases run_raise_outcome m recv args with ⟨c, str, m₂, hr, hkm⟩ | ⟨w, m₂, hr, hkm⟩ | ⟨r, hr⟩
  · rw [hr] at hsr
    obtain ⟨m₃, hstep, f, hf⟩ := hsr
    injection hstep with hstep
    rw [← hstep] at hf
    exact jump_empty_never_value f _ v m' ⟨_, raiseErr_ctl _ _ _⟩
      (by rw [raiseErr_kont, hkm, hk]) hf
  · rw [hr] at hsr
    obtain ⟨m₃, hstep, f, hf⟩ := hsr
    injection hstep with hstep
    rw [← hstep] at hf
    exact jump_empty_never_value f _ v m' ⟨_, rfl⟩ (by
      show m₂.kont = []
      rw [hkm, hk]) hf
  · rw [hr] at hsr; obtain ⟨m₃, hstep, _⟩ := hsr; exact absurd hstep (by simp)

/-- **`invokeDispatch` at `raise`, given the dispatch precondition: no value comes out.** The
four outcomes are in the section note above; `run_raise_not_ok` is what excludes a fifth. -/
theorem invokeDispatch_raise_no_value {m : Machine} {recv : Value} {site : SendSite}
    {args : List Value} {owner : ObjId} {md : MethodDef}
    (hk : m.kont = [])
    (hfound : Interp.methodOn m.heap (classOf m.heap recv) "raise" = some (owner, md))
    (hb : md.builtin = some "Object#raise") (hu : md.undefined = false)
    (hv : md.visibility = .pub) (hp : md.fromPrelude = false)
    (hsh : Interp.crubyShadow m.heap
      ((ancestors m.heap (classOf m.heap recv)).takeWhile (fun x => x != owner)) "raise"
      = none) (v : Value) (m' : Machine) :
    ¬ StepRunsTo (Interp.invoke.invokeDispatch m recv site "raise" args none []) v m' := by
  intro hsr
  rw [Interp.invoke.invokeDispatch.eq_def, lookup_eq_methodOn, hfound] at hsr
  simp only [hu, hp, if_false, Bool.false_eq_true, hsh, visError?_pub hv, hb,
    deferTwin?_raise, appendKwHash_nil] at hsr
  -- the `bid == "Object#raise"` interception fires, and then the argument shapes
  rw [if_pos (by simp : ("Object#raise" == "Object#raise") = true)] at hsr
  -- every arm is either the builtin (which never answers `.ok`) or the `raiseNewK` push
  rcases args with _ | ⟨a, rest⟩
  · exact builtin_raise_no_value m recv [] hk v m' hsr
  · cases a with
    | ref k =>
      dsimp only at hsr
      cases hcp : m.heap.classPayload? k with
      | none => rw [hcp] at hsr; exact builtin_raise_no_value m recv _ hk v m' hsr
      | some c =>
        rw [hcp] at hsr
        cases hui : Interp.userInit? m.heap k with
        | none => rw [hui] at hsr; exact builtin_raise_no_value m recv _ hk v m' hsr
        | some md' =>
          rw [hui] at hsr
          dsimp only at hsr
          split at hsr
          · exact builtin_raise_no_value m recv _ hk v m' hsr
          · -- the interception: allocate, push `raiseNewK`, enter `initialize`
            exact enterUserMethod_raiseNew_no_value
              (Value.ref (m.heap.alloc { klass := k, payload := Payload.exc "" }).fst)
              _ _ md' rest (by simp [hk]) v m' hsr
    | _ => exact builtin_raise_no_value m recv _ hk v m' hsr

/-- **`invokeDispatch` when `raise` resolves nowhere**: `dispatchMiss`, whose last question is
`method_missing` — and `QueryOk`'s second clause says any binding there is a builtin, so what
is left is `missNoMethod`, which raises. -/
theorem dispatchMiss_raise_no_value (m : Machine) (recv : Value) (site : SendSite)
    (args : List Value)
    (hmm : ∀ o md, Interp.methodOn m.heap (classOf m.heap recv) "method_missing"
        = some (o, md) → md.builtin.isSome = true) :
    (∃ r, Interp.dispatchMiss m recv site "raise" args none = .unsupported r) ∨
    (∃ cls msg, Interp.dispatchMiss m recv site "raise" args none
      = .next (Interp.raiseErr m cls msg)) := by
  unfold Interp.dispatchMiss
  simp only [Interp.tryIterator, Interp.tryMixin, Interp.tryReflect]
  repeat' split
  all_goals (try (simp only [Interp.missNoMethod]))
  all_goals (try split)
  all_goals first
    | (right; exact ⟨_, _, rfl⟩)
    | (left; exact ⟨_, rfl⟩)
    | simp_all [Interp.missNoMethod]

theorem invokeDispatch_raise_miss_no_value {m : Machine} {recv : Value} {site : SendSite}
    {args : List Value} (hk : m.kont = [])
    (hnone : Interp.methodOn m.heap (classOf m.heap recv) "raise" = none)
    (hmm : ∀ o md, Interp.methodOn m.heap (classOf m.heap recv) "method_missing"
        = some (o, md) → md.builtin.isSome = true) (v : Value) (m' : Machine) :
    ¬ StepRunsTo (Interp.invoke.invokeDispatch m recv site "raise" args none []) v m' := by
  intro hsr
  rw [Interp.invoke.invokeDispatch.eq_def, lookup_eq_methodOn, hnone] at hsr
  simp only [appendKwHash_nil] at hsr
  rcases dispatchMiss_raise_no_value m recv site args hmm with ⟨r, hd⟩ | ⟨cls, msg, hd⟩
  · rw [hd] at hsr; obtain ⟨m₃, hstep, _⟩ := hsr; exact absurd hstep (by simp)
  · rw [hd] at hsr
    obtain ⟨m₃, hstep, f, hf⟩ := hsr
    injection hstep with hstep
    rw [← hstep] at hf
    exact jump_empty_never_value f _ v m' ⟨_, raiseErr_ctl _ _ _⟩
      (by rw [raiseErr_kont, hk]) hf

/-! ## The rung -/

theorem Sem.Judge.raiseCls : Obl.Judge.raiseCls := by
  intro κ Γ Γ' I I' args argTys n hall _hshape _hexc hrs _hmmfree
  refine ⟨trivial, ?_⟩
  intro m hm v m' hev
  exfalso
  obtain ⟨fuel, hrun⟩ := hev
  match fuel with
  | 0 => rw [run_zero] at hrun; exact absurd hrun (by simp)
  | f + 1 =>
    -- the argument walk, exactly as `callNever`'s
    have hsr : StepRunsTo (Interp.stepFn (evalFrom m (.send none "raise" args none))) v m' := by
      refine stepRunsTo_of_run ?_ hrun
      have he : Interp.stepFn (evalFrom m (.send none "raise" args none))
          = Interp.evalExpr (evalFrom m (.send none "raise" args none))
              (toRuby (.send none "raise" args none)) := rfl
      rw [he]
      exact RubyCore.Proof.evalExpr_notDone
    rw [stepFn_vcall_send] at hsr
    obtain ⟨vs, m₁, hallEv, hk₁, hfin⟩ :=
      run_args .implicit "raise" (evalFrom m (.send none "raise" args none)).currentFrame.self
        .none args [] (evalFrom m (.send none "raise" args none)) v m' rfl hall.1 hsr
    obtain ⟨_, _, hok₁⟩ := hall.2 (evalFrom m (.send none "raise" args none))
      (StateOk_reCtl hm _ _) vs m₁ hallEv
    -- **the dispatch**: whatever `raise` resolves to, no value comes back
    simp only [List.nil_append] at hfin
    rw [show Interp.finishSend m₁ _ _ "raise" vs .none
          = Interp.invoke m₁ _ _ "raise" vs none [] from rfl, invoke_raise] at hfin
    cases hlk : Interp.methodOn m₁.heap
        (classOf m₁.heap (evalFrom m (.send none "raise" args none)).currentFrame.self) "raise"
      with
    | some p =>
      obtain ⟨owner, md⟩ := p
      obtain ⟨hq1, _⟩ := hok₁.query "raise" "Object#raise" (by simp [queryBuiltins]) hrs _
      obtain ⟨hb, hu, hv, hp, hsh⟩ := hq1 owner md hlk
      exact invokeDispatch_raise_no_value hk₁ hlk hb hu hv hp hsh v m' hfin
    | none =>
      obtain ⟨_, hq2⟩ := hok₁.query "raise" "Object#raise" (by simp [queryBuiltins]) hrs _
      exact invokeDispatch_raise_miss_no_value hk₁ hlk (hq2 hlk) v m' hfin

#print axioms Sem.Judge.raiseCls

end Ratchet.Denote
