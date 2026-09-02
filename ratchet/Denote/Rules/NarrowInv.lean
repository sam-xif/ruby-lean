import Denote.Rules.Query
import Denote.Rules.Read
import Denote.Rules.Lit
import Denote.Rules.Const
import Denote.Sem.NarrowState

/-!
# `Denote/Rules/NarrowInv.lean` — narrowing soundness, the run half

`Denote/Sem/Narrow.lean` says what a refined type denotes; `NarrowState.lean` says how the
refinement moves through `StateOk`. This file supplies the missing input: **the branch's own
fact**, read out of the condition's run.

Three of the four shapes `narrowCond?` recognises are a *send to a variable read*
(`x.nil?`, `x.is_a?(C)`, `C === x`), so the skeleton is shared and factored once
(`send_zeroarg_inv` / `send_onearg_inv`): the receiver's one step, `run_split` at the `recvK`,
the argument walk, and out at `finishSend`. What differs per shape is the dispatch chain, and
those are already proved in `Sem/Query.lean`.

The fourth shape is `.var k x` itself, where the condition's value *is* the variable's, and the
fifth (`&&`) needs nothing: its refinement is `thenOnly`, so the **else** side — the only side
these lemmas serve — is the unrefined environment.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-- The value a `narrowCond?` shape reads, by kind. `.cvar`/`.gvar` never reach a refinement —
`narrowEnvs` matches `.lvar` and `narrowSpine` matches `.ivar` — so the answer there is
immaterial and stated as `nil`. -/
def readVar (k : Ratchet.VarKind) (x : String) (m : Machine) : Value :=
  match k with
  | .lvar => m.getLocal x
  | .ivar => ivarOf m.heap m.currentFrame.self x
  | _ => .nil

/-- One `stepFn` step from a variable read of either narrowable kind. Both halves are already
proved (`Lit.lean`, `Read.lean`); this is the pair, so the send skeleton can be stated once. -/
theorem stepFn_readVar (m : Machine) (k : Ratchet.VarKind) (x : String)
    (hk : k = .lvar ∨ k = .ivar) :
    Interp.stepFn (evalFrom m (.var k x)) = .next (reCtl m (.value (readVar k x m)) []) := by
  rcases hk with rfl | rfl
  · exact stepFn_var m x
  · exact stepFn_ivar m x

/-- **The zero-argument send skeleton.** `x.nil?`'s run, taken apart down to `finishSend` — and
the machine there is `m` itself with its control word moved, which is what makes the branch's
fact transfer to the *post*-condition machine. -/
theorem send_zeroarg_inv {m : Machine} {k : Ratchet.VarKind} {x : String} {mname : String}
    {v : Value} {m' : Machine} (hk : k = .lvar ∨ k = .ivar)
    (hev : Evals m (.send (some (.var k x)) mname [] none) v m') :
    StepRunsTo (Interp.finishSend (reCtl m (.value (readVar k x m)) []) (readVar k x m)
      (match toRuby (.var k x) with | .self' => .selfRecv | _ => .explicit)
      mname [] .none) v m' := by
  obtain ⟨fuel, hrun⟩ := hev
  rcases fuel with _ | f
  · rw [run_zero] at hrun; exact absurd hrun (by simp)
  · rw [run_succ, stepFn_send_push] at hrun
    dsimp only at hrun
    obtain ⟨nb, v₀, m₀, hin, hc₀, hk₀, hout⟩ :=
      run_split _ (catchFree_recvK mname (toRubyList []) .none _)
        (jumpOpaque_recvK mname (toRubyList []) .none _) f (evalFrom m (.var k x)) v m' hrun
    obtain ⟨hveq, hmeq⟩ := evals_pure (stepFn_readVar m k x hk) ⟨nb, hin⟩
    subst hveq; subst hmeq
    obtain ⟨f₂, hf₂⟩ := hout
    revert hf₂
    rcases f₂ with _ | f₃
    · intro hf₂; rw [run_zero] at hf₂; exact absurd hf₂ (by simp)
    · intro hf₂
      have hsr : StepRunsTo (Interp.stepFn
          (deliver (reCtl m (.value (readVar k x m)) []) (readVar k x m)
            [.recvK mname (toRubyList []) .none
              (match toRuby (.var k x) with | .self' => .selfRecv | _ => .explicit)])) v m' := by
        refine stepRunsTo_of_run ?_ hf₂
        exact RubyCore.Proof.applyKont_notDone
          (deliver (reCtl m (.value (readVar k x m)) []) (readVar k x m)
            [.recvK mname (toRubyList []) .none
              (match toRuby (.var k x) with | .self' => .selfRecv | _ => .explicit)])
          (readVar k x m) (by simp [deliver])
      rw [stepFn_recvK] at hsr
      have hm₀ : ({ reCtl m (.value (readVar k x m)) [] with
          ctl := .value (readVar k x m), kont := [] } : Machine)
          = reCtl m (.value (readVar k x m)) [] := rfl
      rw [hm₀] at hsr
      obtain ⟨vs, m₁, hallEv, hk₁, hfin⟩ :=
        run_args _ mname (readVar k x m) .none [] [] (reCtl m (.value (readVar k x m)) []) v m'
          rfl (by intro e he; exact absurd he (by simp)) hsr
      have hvs : vs = [] ∧ m₁ = reCtl m (.value (readVar k x m)) [] := by
        cases vs with
        | nil => exact ⟨rfl, hallEv⟩
        | cons a as => exact absurd hallEv (by simp [EvalsAll])
      obtain ⟨hvs1, hvs2⟩ := hvs
      subst hvs1; subst hvs2
      simpa using hfin

#print axioms stepFn_readVar
#print axioms send_zeroarg_inv

/-! ## `x.nil?` — the fact the branch gives

`Object#nil?`/`NilClass#nil?` answer `.bool (recv == nil)` and leave the machine alone, so the
inversion is short once the skeleton is in place. The two bids are why `NilQueryOk` exists
(`../Sem/State.lean`): `QueryOk` pairs a name with *one* bid, and `nil?` has two identical
implementations at different owners. -/

theorem invoke_nilq (m : Machine) (recv : Value) (site : SendSite) (args : List Value)
    (kw : List (Value × Value)) :
    Interp.invoke m recv site "nil?" args none kw
      = Interp.invoke.invokeDispatch m recv site "nil?" args none kw := by
  rw [Interp.invoke.eq_def]
  cases recv with
  | ref o =>
    cases hp : (m.heap.get o).payload <;> simp only [hp] <;>
      first
        | rfl
        | (split <;> simp_all [Interp.invoke.invokeMaybeNew.eq_def])
        | simp_all [Interp.invoke.invokeMaybeNew.eq_def]
  | _ => rfl

theorem deferTwin?_nilq (h : Heap) (bid : String) (recv : Value) (args : List Value)
    (hb : bid = "Object#nil?" ∨ bid = "NilClass#nil?") :
    Builtins.deferTwin? h bid recv args = none := by
  rcases hb with rfl | rfl <;>
    (simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
      Builtins.toAryDefer?, Builtins.coerceTwin?]
     rcases args with _ | ⟨a, rest⟩
     · rfl
     · cases rest <;> rfl)

theorem run_nilq (m : Machine) (recv : Value) (bid : String)
    (hb : bid = "Object#nil?" ∨ bid = "NilClass#nil?") :
    Builtins.run bid recv [] m = .ok (.bool (isNilV recv)) m ∨
      ∃ r, Builtins.run bid recv [] m = .unsupported r := by
  rcases hb with rfl | rfl <;>
    (rw [Builtins.run.eq_def]
     dsimp only
     split
     · exact Or.inr ⟨_, rfl⟩
     split
     · rename_i hz; exact absurd hz (by simp)
     split
     · rename_i hd
       exact absurd hd (by simp [Builtins.dupBids, Builtins.cloneBids])
     refine Or.inl ?_
     rw [Builtins.runObjects.eq_def]
     simp only [Builtins.zeroArgBids, Builtins.dupBids, Builtins.cloneBids]
     cases recv <;> simp [isNilV])

#print axioms invoke_nilq
#print axioms run_nilq

/-- **`invokeDispatch` at `nil?`, given `NilQueryOk`'s facts**: one step to the boolean. -/
theorem invokeDispatch_nilq {m : Machine} {recv : Value} {site : SendSite}
    {owner : ObjId} {md : MethodDef}
    (hfound : Interp.methodOn m.heap (classOf m.heap recv) "nil?" = some (owner, md))
    (hb : md.builtin = some "Object#nil?" ∨ md.builtin = some "NilClass#nil?")
    (hu : md.undefined = false) (hv : md.visibility = .pub) (hp : md.fromPrelude = false)
    (hsh : Interp.crubyShadow m.heap
      ((ancestors m.heap (classOf m.heap recv)).takeWhile (fun x => x != owner)) "nil?"
      = none) :
    Interp.invoke.invokeDispatch m recv site "nil?" [] none []
        = .next (Interp.withCtl m (.value (.bool (isNilV recv)))) ∨
      ∃ r, Interp.invoke.invokeDispatch m recv site "nil?" [] none [] = .unsupported r := by
  rw [Interp.invoke.invokeDispatch.eq_def, lookup_eq_methodOn, hfound]
  rcases hb with hb | hb
  · simp only [hu, hp, if_false, Bool.false_eq_true, hsh, visError?_pub hv, hb,
      deferTwin?_nilq m.heap "Object#nil?" recv [] (Or.inl rfl), appendKwHash_nil]
    rcases run_nilq m recv "Object#nil?" (Or.inl rfl) with hr | ⟨r, hr⟩
    · exact Or.inl (by rw [hr]; simp)
    · exact Or.inr ⟨r, by rw [hr]; simp⟩
  · simp only [hu, hp, if_false, Bool.false_eq_true, hsh, visError?_pub hv, hb,
      deferTwin?_nilq m.heap "NilClass#nil?" recv [] (Or.inr rfl), appendKwHash_nil]
    rcases run_nilq m recv "NilClass#nil?" (Or.inr rfl) with hr | ⟨r, hr⟩
    · exact Or.inl (by rw [hr]; simp)
    · exact Or.inr ⟨r, by rw [hr]; simp⟩

theorem dispatchMiss_nilq_no_value (m : Machine) (recv : Value) (site : SendSite)
    (args : List Value)
    (hmm : ∀ o md, Interp.methodOn m.heap (classOf m.heap recv) "method_missing"
        = some (o, md) → md.builtin.isSome = true) :
    (∃ r, Interp.dispatchMiss m recv site "nil?" args none = .unsupported r) ∨
    (∃ cls msg, Interp.dispatchMiss m recv site "nil?" args none
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

theorem invokeDispatch_nilq_miss {m : Machine} {recv : Value} {site : SendSite}
    (hnone : Interp.methodOn m.heap (classOf m.heap recv) "nil?" = none)
    (hmm : ∀ o md, Interp.methodOn m.heap (classOf m.heap recv) "method_missing"
        = some (o, md) → md.builtin.isSome = true) :
    (∃ r, Interp.invoke.invokeDispatch m recv site "nil?" [] none [] = .unsupported r) ∨
    (∃ cls msg, Interp.invoke.invokeDispatch m recv site "nil?" [] none []
      = .next (Interp.raiseErr m cls msg)) := by
  rw [Interp.invoke.invokeDispatch.eq_def, lookup_eq_methodOn, hnone]
  simp only [appendKwHash_nil]
  exact dispatchMiss_nilq_no_value m recv site [] hmm

/-- **The `x.nil?` inversion.** The condition's value is the nil-test of the variable's, and the
machine is `m` with its control word moved — so the fact holds at the *post*-condition machine,
which is what the refinement is applied at. -/
theorem nilq_inv {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {k : Ratchet.VarKind} {x : String}
    {v : Value} {m' : Machine} (hok : StateOk κ Γ I m)
    (hfree : Ratchet.nameFree κ "nil?" = true) (hk : k = .lvar ∨ k = .ivar)
    (hev : Evals m (.send (some (.var k x)) "nil?" [] none) v m') :
    v = .bool (isNilV (readVar k x m)) ∧ readVar k x m' = readVar k x m := by
  have hsr := send_zeroarg_inv hk hev
  rw [show Interp.finishSend (reCtl m (.value (readVar k x m)) []) (readVar k x m) _ "nil?" []
        .none = Interp.invoke (reCtl m (.value (readVar k x m)) []) (readVar k x m) _ "nil?" []
        none [] from rfl, invoke_nilq] at hsr
  obtain ⟨m₂, hstep, f, hf⟩ := hsr
  have hheap : (reCtl m (.value (readVar k x m)) []).heap = m.heap := rfl
  cases hlk : Interp.methodOn (reCtl m (.value (readVar k x m)) []).heap
      (classOf (reCtl m (.value (readVar k x m)) []).heap (readVar k x m)) "nil?" with
  | some p =>
    obtain ⟨owner, md⟩ := p
    obtain ⟨hq1, _⟩ := hok.nilQuery hfree
      (classOf (reCtl m (.value (readVar k x m)) []).heap (readVar k x m))
    obtain ⟨hb, hu, hv, hp, hsh⟩ := hq1 owner md hlk
    rcases invokeDispatch_nilq hlk hb hu hv hp hsh with hd | ⟨r, hd⟩
    · rw [hd] at hstep
      injection hstep with hstep
      rw [← hstep] at hf
      -- the value is in flight at an empty continuation: one more step ends the run
      revert hf
      rcases f with _ | f₅
      · intro hf; rw [run_zero] at hf; exact absurd hf (by simp)
      · intro hf
        rw [run_succ, show Interp.stepFn (Interp.withCtl (reCtl m
              (.value (readVar k x m)) []) (.value (.bool (isNilV (readVar k x m)))))
            = .done (.bool (isNilV (readVar k x m))) (Interp.withCtl (reCtl m
              (.value (readVar k x m)) []) (.value (.bool (isNilV (readVar k x m)))))
            from stepFn_value_nil _ _] at hf
        dsimp only at hf
        cases hf
        -- `withCtl`/`reCtl` touch only `ctl`/`kont`, which neither read sees
        refine ⟨rfl, ?_⟩
        cases k <;> simp [readVar, Interp.withCtl, reCtl, getLocal_reCtl, ivarOf]
    · rw [hd] at hstep; exact absurd hstep (by simp)
  | none =>
    obtain ⟨_, hq2⟩ := hok.nilQuery hfree
      (classOf (reCtl m (.value (readVar k x m)) []).heap (readVar k x m))
    rcases invokeDispatch_nilq_miss hlk (hq2 hlk) with ⟨r, hd⟩ | ⟨cls, msg, hd⟩
    · rw [hd] at hstep; exact absurd hstep (by simp)
    · rw [hd] at hstep
      injection hstep with hstep
      rw [← hstep] at hf
      exact absurd hf (jump_empty_never_value f _ v m'
        ⟨_, raiseErr_ctl _ _ _⟩ (by rw [raiseErr_kont]))

#print axioms nilq_inv

/-! ## `x.is_a?(C)` and `C === x` — the nominal shapes

Two more shapes, and between them they need one thing the `nil?` inversion did not: the
**constant's** run inverted, because the tested class arrives as a `.const` and the fact the
refinement needs is about the class `classNamed?` finds. `ConstScopeOk` is what makes those the
same value; without it the machine's lexical resolution and the toplevel table are unrelated.
-/

/-- **The `.const` inversion.** A constant that resolves nowhere raises `NameError` — a jump at
an empty continuation — so a run that *returns* tells you the resolution succeeded. -/
theorem evals_const_inv {m : Machine} {cn : String} {v : Value} {m' : Machine}
    (hev : Evals m (.const cn) v m') :
    constResolveAt m cn = some v ∧ m' = reCtl m (.value v) [] := by
  cases hc : constResolveAt m cn with
  | some w =>
    obtain ⟨hveq, hmeq⟩ := evals_pure (stepFn_const hc) hev
    subst hveq
    exact ⟨rfl, hmeq⟩
  | none => exact (const_miss_no_value hc hev).elim


/-- **The one-argument send skeleton, with the argument a constant.** `x.is_a?(C)`'s run down
to `finishSend`. The machine there is `m` with its control word moved — twice, once per
evaluation — and `reCtl` collapses, which is why the fact still transfers. -/
theorem send_const_arg_inv {m : Machine} {k : Ratchet.VarKind} {x : String} {mname : String}
    {cn : String} {v : Value} {m' : Machine} (hk : k = .lvar ∨ k = .ivar)
    (hev : Evals m (.send (some (.var k x)) mname [.const cn] none) v m') :
    ∃ w, constResolveAt m cn = some w ∧
      StepRunsTo (Interp.finishSend (reCtl m (.value w) []) (readVar k x m)
        (match toRuby (.var k x) with | .self' => .selfRecv | _ => .explicit)
        mname [w] .none) v m' := by
  obtain ⟨fuel, hrun⟩ := hev
  rcases fuel with _ | f
  · rw [run_zero] at hrun; exact absurd hrun (by simp)
  · rw [run_succ, stepFn_send_push] at hrun
    dsimp only at hrun
    obtain ⟨nb, v₀, m₀, hin, hc₀, hk₀, hout⟩ :=
      run_split _ (catchFree_recvK mname (toRubyList [.const cn]) .none _)
        (jumpOpaque_recvK mname (toRubyList [.const cn]) .none _) f (evalFrom m (.var k x))
        v m' hrun
    obtain ⟨hveq, hmeq⟩ := evals_pure (stepFn_readVar m k x hk) ⟨nb, hin⟩
    subst hveq; subst hmeq
    obtain ⟨f₂, hf₂⟩ := hout
    revert hf₂
    rcases f₂ with _ | f₃
    · intro hf₂; rw [run_zero] at hf₂; exact absurd hf₂ (by simp)
    · intro hf₂
      have hsr : StepRunsTo (Interp.stepFn
          (deliver (reCtl m (.value (readVar k x m)) []) (readVar k x m)
            [.recvK mname (toRubyList [.const cn]) .none
              (match toRuby (.var k x) with | .self' => .selfRecv | _ => .explicit)])) v m' := by
        refine stepRunsTo_of_run ?_ hf₂
        exact RubyCore.Proof.applyKont_notDone
          (deliver (reCtl m (.value (readVar k x m)) []) (readVar k x m)
            [.recvK mname (toRubyList [.const cn]) .none
              (match toRuby (.var k x) with | .self' => .selfRecv | _ => .explicit)])
          (readVar k x m) (by simp [deliver])
      rw [stepFn_recvK] at hsr
      have hm₀ : ({ reCtl m (.value (readVar k x m)) [] with
          ctl := .value (readVar k x m), kont := [] } : Machine)
          = reCtl m (.value (readVar k x m)) [] := rfl
      rw [hm₀] at hsr
      obtain ⟨vs, m₁, hallEv, hk₁, hfin⟩ :=
        run_args _ mname (readVar k x m) .none [.const cn] []
          (reCtl m (.value (readVar k x m)) []) v m' rfl
          (by intro e he; simp only [List.mem_singleton] at he; rw [he]; trivial) hsr
      -- one argument: the constant, whose run is inverted
      cases vs with
      | nil => exact absurd hallEv (by simp [EvalsAll])
      | cons w rest =>
        cases rest with
        | cons a as => exact absurd hallEv (by simp [EvalsAll])
        | nil =>
          obtain ⟨ma, hEv, hrest⟩ := hallEv
          have hma : ma = m₁ := (hrest : m₁ = ma).symm
          subst hma
          obtain ⟨hres, hmeq⟩ := evals_const_inv hEv
          refine ⟨w, ?_, ?_⟩
          · -- `constResolveAt` reads `currentFrame`, which `reCtl` does not touch
            rw [← hres]
            simp only [constResolveAt, currentFrame_reCtl, heap_reCtl]
          · rw [hmeq] at hfin
            simpa using hfin

#print axioms evals_const_inv
#print axioms send_const_arg_inv


/-- **`Object#is_a?`'s three outcomes.** The arm is small enough to read off directly: a live
class argument answers the ancestor test and leaves the machine *identical*, anything else is a
`TypeError` at the same machine, and a wrong arity gates. Stated as an outcome disjunction
rather than an inversion of the `.ok` case because the `.err` arm's machine is needed too — it
is where `jump_empty_never_value` gets its continuation.

The forward lemma (`run_isA`) *assumes* the argument is a class, because the rung had that from
the argument's type; here there is no typing to lean on. -/
theorem run_isA_outcome (m : Machine) (recv av : Value) :
    (∃ ka, av = .ref ka ∧ (m.heap.classPayload? ka).isSome = true ∧
       Builtins.run "Object#is_a?" recv [av] m = .ok (.bool (isA m.heap recv ka)) m) ∨
    (∃ c str, Builtins.run "Object#is_a?" recv [av] m = .err c str m) ∨
    (∃ r, Builtins.run "Object#is_a?" recv [av] m = .unsupported r) := by
  rw [Builtins.run.eq_def]
  dsimp only
  split
  · exact Or.inr (Or.inr ⟨_, rfl⟩)
  split
  · rename_i hz; exact absurd hz (by simp [Builtins.zeroArgBids])
  split
  · rename_i hd; exact absurd hd (by simp [Builtins.dupBids, Builtins.cloneBids])
  rw [Builtins.runObjects.eq_def]
  simp only
  cases av with
  | ref ka =>
    dsimp only
    cases hp : m.heap.classPayload? ka with
    | none =>
      refine Or.inr (Or.inl ⟨Boot.typeErrorId, "class or module required", ?_⟩)
      simp
    | some c => exact Or.inl ⟨ka, rfl, by rw [hp]; rfl, by simp⟩
  | _ => exact Or.inr (Or.inl ⟨_, _, rfl⟩)

/-- **The `x.is_a?(C)` inversion.** The condition's value is the ancestor test at the class the
name resolves to, and both the read and the resolution are unchanged at the post-condition
machine. `ConstScopeOk` is what turns the machine's lexical resolution into `classNamed?`. -/
theorem isaq_inv {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {k : Ratchet.VarKind} {x : String}
    {cn : String} {v : Value} {m' : Machine} (hok : StateOk κ Γ I m)
    (hfree : Ratchet.nameFree κ "is_a?" = true) (hk : k = .lvar ∨ k = .ivar)
    (hev : Evals m (.send (some (.var k x)) "is_a?" [.const cn] none) v m') :
    ∃ j, classNamed? m.heap cn = some j ∧
      v = .bool (isA m.heap (readVar k x m) j) ∧ readVar k x m' = readVar k x m ∧
      m'.heap = m.heap := by
  obtain ⟨w, hres, hsr⟩ := send_const_arg_inv hk hev
  rw [show Interp.finishSend (reCtl m (.value w) []) (readVar k x m) _ "is_a?" [w] .none
        = Interp.invoke (reCtl m (.value w) []) (readVar k x m) _ "is_a?" [w] none [] from rfl,
     invoke_isA] at hsr
  obtain ⟨m₂, hstep, f, hf⟩ := hsr
  rw [Interp.invoke.invokeDispatch.eq_def, lookup_eq_methodOn] at hstep
  cases hlk : Interp.methodOn (reCtl m (.value w) []).heap
      (classOf (reCtl m (.value w) []).heap (readVar k x m)) "is_a?" with
  | none =>
    rw [hlk] at hstep
    obtain ⟨_, hq2⟩ := hok.query "is_a?" "Object#is_a?" (by simp [queryBuiltins]) hfree _
    simp only [appendKwHash_nil] at hstep
    rcases dispatchMiss_isA_no_value (reCtl m (.value w) []) (readVar k x m) _ [w]
      (hq2 hlk) with ⟨r, hd⟩ | ⟨cls, msg, hd⟩
    · rw [hd] at hstep; exact absurd hstep (by simp)
    · rw [hd] at hstep
      injection hstep with hstep
      rw [← hstep] at hf
      exact absurd hf (jump_empty_never_value f _ v m'
        ⟨_, raiseErr_ctl _ _ _⟩ (by rw [raiseErr_kont]))
  | some p =>
    obtain ⟨owner, md⟩ := p
    obtain ⟨hq1, _⟩ := hok.query "is_a?" "Object#is_a?" (by simp [queryBuiltins]) hfree _
    obtain ⟨hb, hu, hv, hp, hsh⟩ := hq1 owner md hlk
    rw [hlk] at hstep
    simp only [hu, hp, if_false, Bool.false_eq_true, hsh, visError?_pub hv, hb,
      deferTwin?_isA, appendKwHash_nil] at hstep
    -- the builtin ran; take its outcome
    rcases run_isA_outcome (reCtl m (.value w) []) (readVar k x m) w with
      ⟨ka, hav, hka, hr⟩ | ⟨c, str, hr⟩ | ⟨r, hr⟩
    · rw [hr] at hstep
      injection hstep with hstep
      rw [← hstep] at hf
      revert hf
      rcases f with _ | f₅
      · intro hf; rw [run_zero] at hf; exact absurd hf (by simp)
      · intro hf
        rw [run_succ, show Interp.stepFn (Interp.withCtl (reCtl m (Ctl.value w) [])
              (Ctl.value (Value.bool (isA (reCtl m (Ctl.value w) []).heap
                (readVar k x m) ka))))
            = .done (.bool (isA (reCtl m (Ctl.value w) []).heap (readVar k x m) ka))
              (Interp.withCtl (reCtl m (Ctl.value w) [])
                (Ctl.value (Value.bool (isA (reCtl m (Ctl.value w) []).heap
                  (readVar k x m) ka)))) from stepFn_value_nil _ _] at hf
        dsimp only at hf
        cases hf
        refine ⟨ka, ?_, ?_, ?_, ?_⟩
        · have hcl : constLookup m.heap cn = some w := by rw [← hok.constScope cn]; exact hres
          simp only [classNamed?, hcl, hav]
          simp only [heap_reCtl] at hka
          simp only [hka, if_pos]
        · rfl
        · cases k <;> simp [readVar, Interp.withCtl, reCtl, getLocal_reCtl, ivarOf]
        · rfl
    · rw [hr] at hstep
      injection hstep with hstep
      rw [← hstep] at hf
      exact absurd hf (jump_empty_never_value f _ v m'
        ⟨_, raiseErr_ctl _ _ _⟩ (by rw [raiseErr_kont]))
    · rw [hr] at hstep; exact absurd hstep (by simp)

#print axioms run_isA_outcome
#print axioms isaq_inv

end Ratchet.Denote
