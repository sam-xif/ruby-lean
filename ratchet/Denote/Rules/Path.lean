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

/-! ## The delivery, as one equation

`applyKont`'s `.cpathK` arm, with the container already known to be a class. One equation for
the whole arm, so the rung can take its conditions apart with `cases … :` **in the
hypothesis** — which is the technique `../Sem/Decompose.lean`'s `throwJ` arm needed, for the
same reason: the conditions are built with `let`s and the resulting `if`s sit inside the
scrutinee of `run`'s five-arm match, so `split` picks the wrong one and `rw [if_pos …]` does
not match the elaboration the source produced. -/
theorem stepFn_cpathK {m : Machine} {k : ObjId} (n : String)
    (hp : (m.heap.classPayload? k).isSome = true) :
    Interp.stepFn (deliver m (.ref k) [.cpathK n]) =
      (match (if Interp.isPrivateConst m.heap k n then none
              else constLookupFrom m.heap k n) with
       | some cv => .next (reCtl m (.value cv) [])
       | none =>
         if (match (m.heap.get k).eigen with
             | some e => (Interp.methodOn m.heap e "const_missing").isSome
             | none => false) then .unsupported "const_missing hook"
         else if Interp.isPrivateConst m.heap k n then
           .next (Interp.raiseErr (reCtl m (.value (.ref k)) []) Boot.nameErrorId
             s!"private constant {className m.heap k}::{n} referenced")
         else .next (Interp.raiseErr (reCtl m (.value (.ref k)) []) Boot.nameErrorId
           s!"uninitialized constant {className m.heap k}::{n}")) := by
  simp only [deliver, Interp.stepFn, Interp.applyKont, Interp.cpathContainer, hp, if_pos]
  rfl

/-! ## The rung -/

theorem Sem.Judge.constPath : Obl.Judge.constPath := by
  intro κ Γ Γ₁ I I₁ base owner n τ hbase hkey _hpriv
  refine ⟨trivial, ?_⟩
  intro m hm v m' hev
  obtain ⟨fuel, hrun⟩ := hev
  rcases fuel with _ | f
  · rw [run_zero] at hrun; exact absurd hrun (by simp)
  · rw [run_succ, stepFn_cpath_push] at hrun
    dsimp only at hrun
    obtain ⟨nb, v₀, m₀, hin, hc₀, hk₀, hout⟩ :=
      run_split _ (catchFree_cpathK n) (jumpOpaque_cpathK n) f (evalFrom m base) v m' hrun
    obtain ⟨hstack, hdenBase, hok₁, -⟩ := hbase.2 m hm v₀ m₀ ⟨nb, hin⟩
    -- the base's value is the class named `owner`
    have hcls : ∃ k, classNamed? m₀.heap owner = some k ∧ v₀ = .ref k := by
      simp only [denM, isClassRefNamed] at hdenBase
      cases hcn : classNamed? m₀.heap owner with
      | none => rw [hcn] at hdenBase; exact absurd hdenBase (by cases v₀ <;> simp)
      | some k =>
        rw [hcn] at hdenBase
        cases v₀ with
        | ref o => exact ⟨k, rfl, by simp only [beq_iff_eq] at hdenBase; rw [hdenBase]⟩
        | _ => exact absurd hdenBase (by simp)
    obtain ⟨k, hcn, rfl⟩ := hcls
    -- `classNamed?` only answers at a class, which is what `cpathContainer` needs
    have hp : (m₀.heap.classPayload? k).isSome = true := by
      simp only [classNamed?] at hcn
      cases hcl : constLookup m₀.heap owner with
      | none => rw [hcl] at hcn; exact absurd hcn (by simp)
      | some w =>
        rw [hcl] at hcn
        cases w with
        | ref o =>
          simp only at hcn
          split at hcn
          · rename_i hpo
            have hok : o = k := by simpa using hcn
            rw [← hok]; exact hpo
          · exact absurd hcn (by simp)
        | _ => exact absurd hcn (by simp)
    obtain ⟨f₂, hf₂⟩ := hout
    revert hf₂
    rcases f₂ with _ | f₃
    · intro hf₂; rw [run_zero] at hf₂; exact absurd hf₂ (by simp)
    · intro hf₂
      rw [run_succ, stepFn_cpathK n hp] at hf₂
      cases hlk : (if Interp.isPrivateConst m₀.heap k n then (none : Option Value)
                   else constLookupFrom m₀.heap k n) with
      | some cv =>
        rw [hlk] at hf₂
        dsimp only at hf₂
        -- the value is in flight under an empty continuation, so one more step ends the run
        revert hf₂
        rcases f₃ with _ | f₄
        · intro hf₂; rw [run_zero] at hf₂; exact absurd hf₂ (by simp)
        · intro hf₂
          rw [run_succ, stepFn_value_nil] at hf₂
          dsimp only at hf₂
          -- the injection substitutes the value away, so the rest is in terms of `v`
          cases hf₂
          have hfound : constLookupFrom m₀.heap k n = some v := by
            split at hlk
            · exact absurd hlk (by simp)
            · exact hlk
          refine ⟨?_, ?_, ?_, ?_⟩
          · exact hstack.trans (Framed_reCtl _ _ _)
          · exact denM_reCtl.mpr (hok₁.constPaths owner n τ k hkey hcn v hfound)
          · exact StateOk_reCtl hok₁ _ _
          · exact StateOk_reCtl hok₁ _ _
      | none =>
        -- the two miss paths: the gate, and the raise
        rw [hlk] at hf₂
        dsimp only at hf₂
        exfalso
        cases hcm : (match (m₀.heap.get k).eigen with
                     | some e => (Interp.methodOn m₀.heap e "const_missing").isSome
                     | none => false) with
        | true => rw [hcm] at hf₂; exact absurd hf₂ (by simp)
        | false =>
          rw [hcm] at hf₂
          cases hpriv : Interp.isPrivateConst m₀.heap k n with
          | true =>
            rw [hpriv] at hf₂
            exact jump_empty_never_value f₃ _ v m' ⟨_, raiseErr_ctl _ _ _⟩ rfl hf₂
          | false =>
            rw [hpriv] at hf₂
            exact jump_empty_never_value f₃ _ v m' ⟨_, raiseErr_ctl _ _ _⟩ rfl hf₂

/-- The sibling: `A::B` where `B` names a **nested class**. The same three outcomes; only the
hit case differs, and it is `NestedClassesOk` (`../Sem/State.lean`) rather than
`ConstPathsOk` — the clause saying that looking `B` up *inside* `A` finds the class the
toplevel path `"A::B"` names. -/
theorem Sem.Judge.constPathCls : Obl.Judge.constPathCls := by
  intro κ Γ Γ₁ I I₁ base owner n c hbase hcls _hno
  refine ⟨trivial, ?_⟩
  intro m hm v m' hev
  obtain ⟨fuel, hrun⟩ := hev
  rcases fuel with _ | f
  · rw [run_zero] at hrun; exact absurd hrun (by simp)
  · rw [run_succ, stepFn_cpath_push] at hrun
    dsimp only at hrun
    obtain ⟨nb, v₀, m₀, hin, hc₀, hk₀, hout⟩ :=
      run_split _ (catchFree_cpathK n) (jumpOpaque_cpathK n) f (evalFrom m base) v m' hrun
    obtain ⟨hstack, hdenBase, hok₁, -⟩ := hbase.2 m hm v₀ m₀ ⟨nb, hin⟩
    have hcl : ∃ k, classNamed? m₀.heap owner = some k ∧ v₀ = .ref k := by
      simp only [denM, isClassRefNamed] at hdenBase
      cases hcn : classNamed? m₀.heap owner with
      | none => rw [hcn] at hdenBase; exact absurd hdenBase (by cases v₀ <;> simp)
      | some k =>
        rw [hcn] at hdenBase
        cases v₀ with
        | ref o => exact ⟨k, rfl, by simp only [beq_iff_eq] at hdenBase; rw [hdenBase]⟩
        | _ => exact absurd hdenBase (by simp)
    obtain ⟨k, hcn, rfl⟩ := hcl
    have hp : (m₀.heap.classPayload? k).isSome = true := by
      simp only [classNamed?] at hcn
      cases hcl2 : constLookup m₀.heap owner with
      | none => rw [hcl2] at hcn; exact absurd hcn (by simp)
      | some w =>
        rw [hcl2] at hcn
        cases w with
        | ref o =>
          simp only at hcn
          split at hcn
          · rename_i hpo
            have hok : o = k := by simpa using hcn
            rw [← hok]; exact hpo
          · exact absurd hcn (by simp)
        | _ => exact absurd hcn (by simp)
    obtain ⟨f₂, hf₂⟩ := hout
    revert hf₂
    rcases f₂ with _ | f₃
    · intro hf₂; rw [run_zero] at hf₂; exact absurd hf₂ (by simp)
    · intro hf₂
      rw [run_succ, stepFn_cpathK n hp] at hf₂
      cases hlk : (if Interp.isPrivateConst m₀.heap k n then (none : Option Value)
                   else constLookupFrom m₀.heap k n) with
      | some cv =>
        rw [hlk] at hf₂
        dsimp only at hf₂
        revert hf₂
        rcases f₃ with _ | f₄
        · intro hf₂; rw [run_zero] at hf₂; exact absurd hf₂ (by simp)
        · intro hf₂
          rw [run_succ, stepFn_value_nil] at hf₂
          dsimp only at hf₂
          cases hf₂
          have hfound : constLookupFrom m₀.heap k n = some v := by
            split at hlk
            · exact absurd hlk (by simp)
            · exact hlk
          refine ⟨?_, ?_, ?_, ?_⟩
          · exact hstack.trans (Framed_reCtl _ _ _)
          · refine denM_reCtl.mpr ?_
            simp only [denM]
            exact hok₁.nested owner n c hcls k v hcn hfound
          · exact StateOk_reCtl hok₁ _ _
          · exact StateOk_reCtl hok₁ _ _
      | none =>
        rw [hlk] at hf₂
        dsimp only at hf₂
        exfalso
        cases hcm : (match (m₀.heap.get k).eigen with
                     | some e => (Interp.methodOn m₀.heap e "const_missing").isSome
                     | none => false) with
        | true => rw [hcm] at hf₂; exact absurd hf₂ (by simp)
        | false =>
          rw [hcm] at hf₂
          cases hpriv : Interp.isPrivateConst m₀.heap k n with
          | true =>
            rw [hpriv] at hf₂
            exact jump_empty_never_value f₃ _ v m' ⟨_, raiseErr_ctl _ _ _⟩ rfl hf₂
          | false =>
            rw [hpriv] at hf₂
            exact jump_empty_never_value f₃ _ v m' ⟨_, raiseErr_ctl _ _ _⟩ rfl hf₂

#print axioms Sem.Judge.constPath
#print axioms Sem.Judge.constPathCls
#print axioms jumpOpaque_cpathK

end Ratchet.Denote
