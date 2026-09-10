import Denote.Rules.Vasgn
import Denote.Sem.Mut

/-!
# `Denote/Rules/IvarAsgn.lean` — `@x = e`, and the mutation transport

`Judge.ivarAsgn` is the first rung whose step **mutates an object already in the heap**, and
that is the whole difficulty. Every transport the ladder had before this one was `Ext`
(allocation: the heap grows, old ids read back identically) or `setLocal` (a frame rebinding:
the heap is untouched). Neither covers a write to an object's `ivars`, and `Ext` in particular
is *false* of it — `Ext.get` says every old id reads back identically, and this step is
precisely an old id not reading back identically.

`Denote/Sem/Mut.lean` is the relation that does cover it, and the two halves of its statement
are the two halves of the argument:

* **the shape is unmoved** — `classPayload?`, the ancestor walk, `klass`, `eigen`, `frozen` —
  which transports the twenty-two `StateOk` components that read only the heap's shape, and
* **exactly one object's `ivars` changed, at exactly one name**, which is what a claim mentioning
  `@x` has to survive.

Nothing makes the second half survive by itself, and that is `found-issues.md` §F17: the rule
as written let a `Judge` derivation carry a spine `C[@x : Integer]` across `@x = "s"`. The fix
is the premise `ivarAsgnOk`, which checks **agreement** rather than absence — every type the
context (or the inferred `self` spine) holds either does not mention `@x` or claims exactly the
type being written. Absence would have been the wrong check twice over: it rejects
`self`-typed methods, since `κ.selfTy` mentions every ivar the class has, and it rejects
type-changing reassignment.

## The three arms of the step

`applyKont`'s `.asgnK .ivar` arm is not one case but three, and the rule has premises for none
of them:

```
self = .ref o, not frozen  ⟶  bindIvar: the write                 -- `stepFn_asgnK_ivar`
self = .ref o, frozen      ⟶  raise FrozenError                   -- `stepFn_asgnK_ivar_stuck`
self immediate (1, :a, …)  ⟶  raise FrozenError (immediates are)   -- idem
```

The last two need no premise because they produce **no value**: `Evals` asks for
`.value v m'`, a raise with an empty continuation never reaches one (`jump_empty_never_value`),
and an `.unsupported` is not a value either. So the obligation is discharged at those two arms
by having no case, exactly as `Judge.constExc`'s is at `"IOError"`.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## The two ends of the run -/

/-- The push, as at `.lvar` (`Denote/Rules/Vasgn.lean`) — `stepFn` does not look at the kind. -/
theorem stepFn_ivarAsgn_push (m : Machine) (x : String) (e : Ratchet.Expr) :
    Interp.stepFn (evalFrom m (.vasgn .ivar x e))
      = .next (pushK [.asgnK .ivar x] (evalFrom m e)) := rfl

theorem catchFree_asgnK_ivar (x : String) :
    RubyCore.Proof.CatchFree [.asgnK .ivar x] := by
  intro k hk t
  rcases List.mem_singleton.mp hk with rfl
  simp

/-- **The write arm.** `split` rather than `rfl`: the arm is chosen by a `match` on
`self` and then an `if` on `frozen`, and both scrutinees are facts about the machine rather
than about the syntax. -/
theorem stepFn_asgnK_ivar {m : Machine} {x : String} {v : Value} {o : ObjId}
    (hs : m.currentFrame.self = .ref o) (hfr : (m.heap.get o).frozen = false) :
    Interp.stepFn (reCtl m (.value v) [.asgnK .ivar x])
      = .next (Interp.withCtl (Interp.bindIvar (reCtl m (.value v) []) x v) (.value v)) := by
  dsimp only [Interp.stepFn, Interp.applyKont]
  split
  · rename_i o' heq
    have hso : m.currentFrame.self = .ref o' := heq
    rw [hs] at hso
    have ho : o' = o := by injection hso with h; exact h.symm
    subst ho
    rw [if_neg (by simp [hfr])]
  · rename_i _ hno
    exact absurd hs (fun h => hno o h)

/-- **The other two arms, together.** Both raise, and what the rung needs of them is only that
they do not produce a value — so they are stated as the disjunction of the two shapes a
non-value step result can have. -/
theorem stepFn_asgnK_ivar_stuck {m : Machine} {x : String} {v : Value}
    (h : ∀ o, m.currentFrame.self = .ref o → (m.heap.get o).frozen = true) :
    (∃ e, Interp.stepFn (reCtl m (.value v) [.asgnK .ivar x]) = .unsupported e) ∨
    (∃ M : Machine, Interp.stepFn (reCtl m (.value v) [.asgnK .ivar x]) = .next M ∧
      (∃ j, M.ctl = .jump j) ∧ M.kont = []) := by
  dsimp only [Interp.stepFn, Interp.applyKont]
  split
  · rename_i o' heq
    have hso : m.currentFrame.self = .ref o' := heq
    rw [if_pos (by simp [h o' hso])]
    split
    · exact Or.inr ⟨_, rfl, ⟨_, raiseErr_ctl _ _ _⟩, by rw [raiseErr_kont]⟩
    · exact Or.inl ⟨_, rfl⟩
  · split
    · exact Or.inr ⟨_, rfl, ⟨_, raiseErr_ctl _ _ _⟩, by rw [raiseErr_kont]⟩
    · exact Or.inl ⟨_, rfl⟩

/-! ## `bindIvar` **is** an `IvarWrite`

The one place `Heap.set` is unfolded. Four facts about `Array.set!`
(`RubyCore/Proof/HeapFacts.lean`) plus `find?_filter_ne` do all of it: the written object
differs from the old one in `ivars` only, so every shape field is either read at another id
(`objs_getD_set!_ne`) or copied by the record update.
-/

theorem bindIvar_stack (m : Machine) (x : String) (v : Value) :
    (Interp.bindIvar m x v).stack = m.stack := by
  unfold Interp.bindIvar; split <;> rfl

theorem bindIvar_frames (m : Machine) (x : String) (v : Value) :
    (Interp.bindIvar m x v).frames = m.frames := by
  unfold Interp.bindIvar; split <;> rfl

theorem bindIvar_globals (m : Machine) (x : String) (v : Value) :
    (Interp.bindIvar m x v).globals = m.globals := by
  unfold Interp.bindIvar; split <;> rfl

theorem bindIvar_kont (m : Machine) (x : String) (v : Value) :
    (Interp.bindIvar m x v).kont = m.kont := by
  unfold Interp.bindIvar; split <;> rfl

theorem bindIvar_heap_ref {m : Machine} {x : String} {v : Value} {o : ObjId}
    (hs : m.currentFrame.self = .ref o) :
    (Interp.bindIvar m x v).heap = m.heap.set o
      { m.heap.get o with ivars := (x, v) :: (m.heap.get o).ivars.filter (·.1 != x) } := by
  unfold Interp.bindIvar
  split
  · rename_i o' heq
    have hso : m.currentFrame.self = .ref o' := heq
    rw [hs] at hso
    have ho : o' = o := by injection hso with h; exact h.symm
    subst ho
    rfl
  · rename_i _ hno
    exact absurd hs (fun h => hno o h)

theorem heap_set_get_ne {h : Heap} {o o' : ObjId} (obj : Object) (hne : o' ≠ o) :
    (h.set o obj).get o' = h.get o' := by
  simp only [Heap.set, Heap.get]
  exact RubyCore.Proof.objs_getD_set!_ne _ _ _ _ hne

theorem heap_set_get_self {h : Heap} {o : ObjId} (obj : Object) (ho : o < h.objs.size) :
    (h.set o obj).get o = obj := by
  simp only [Heap.set, Heap.get]
  exact RubyCore.Proof.objs_getD_set!_self _ _ _ ho

theorem heap_set_size {h : Heap} {o : ObjId} (obj : Object) :
    (h.set o obj).objs.size = h.objs.size := by
  simp [Heap.set, Array.set!]

/-- **The write, as the relation the transport wants.** -/
theorem ivarWrite_bindIvar {m : Machine} {x : String} {v : Value} {o : ObjId}
    (hs : m.currentFrame.self = .ref o) (ho : o < m.heap.objs.size) :
    IvarWrite x v (.ref o) m (Interp.bindIvar m x v) := by
  have hh := bindIvar_heap_ref (m := m) (x := x) (v := v) hs
  refine
    { frames := bindIvar_frames m x v
      stack := bindIvar_stack m x v
      globals := bindIvar_globals m x v
      size := by rw [hh]; exact heap_set_size _
      klass := ?_, eigen := ?_, payloadObj := ?_, frozen := ?_
      self := ?_, other := ?_ }
  all_goals rw [hh]
  · intro o'
    by_cases hne : o' = o
    · subst hne; rw [heap_set_get_self _ ho]
    · rw [heap_set_get_ne _ hne]
  · intro o'
    by_cases hne : o' = o
    · subst hne; rw [heap_set_get_self _ ho]
    · rw [heap_set_get_ne _ hne]
  · intro o'
    by_cases hne : o' = o
    · subst hne; rw [heap_set_get_self _ ho]
    · rw [heap_set_get_ne _ hne]
  · intro o'
    by_cases hne : o' = o
    · subst hne; rw [heap_set_get_self _ ho]
    · rw [heap_set_get_ne _ hne]
  · intro y
    rw [ivarOf, heap_set_get_self _ ho]
    by_cases hy : y = x
    · subst hy
      rw [if_pos rfl]
      simp [List.find?]
    · rw [if_neg hy, ivarOf]
      have hb : ((x, v).1 == y) = false := by simpa using (fun h => hy h.symm : ¬ (x = y))
      rw [show ((x, v) :: (m.heap.get o).ivars.filter (·.1 != x)).find? (·.1 == y)
            = ((m.heap.get o).ivars.filter (·.1 != x)).find? (·.1 == y) from
          List.find?_cons_of_neg (by simpa using hb),
        RubyCore.Proof.find?_filter_ne _ hy]
  · intro w hw y
    cases w with
    | ref o' =>
      have hne : o' ≠ o := by
        intro h; exact absurd (by rw [h] : (Value.ref o' : Value) = .ref o) hw
      rw [ivarOf, ivarOf, heap_set_get_ne _ hne]
    | _ => rfl

/-! ## The rung -/

theorem Sem.Judge.ivarAsgn : Obl.Judge.ivarAsgn := by
  intro κ Γ Γ' I I' x e τ hprem hst
  first
    | refine ⟨by first | trivial | simp [PlainAll, Plain]
                       | simp_all [PlainAll, Plain], ?_⟩
    | skip
  intro m hm v m' hev
  obtain ⟨fuel, hrun⟩ := hev
  -- **Step 1**: peel the push.
  have hpush : ∃ f, Interp.run f (pushK [.asgnK .ivar x] (evalFrom m e)) = .value v m' := by
    match fuel with
    | 0 => rw [run_zero] at hrun; exact absurd hrun (by simp)
    | f + 1 =>
      refine ⟨f, ?_⟩
      simpa only [run_succ, stepFn_ivarAsgn_push] using hrun
  obtain ⟨f, hf⟩ := hpush
  obtain ⟨n, v₀, m₀, hin, hc₀, hk₀, hout⟩ :=
    run_split [.asgnK .ivar x] (catchFree_asgnK_ivar x) (jumpOpaque_asgnK .ivar x) f
      (evalFrom m e) v m' hf
  -- **The premise**, at the sub-run.
  obtain ⟨hframe, hden, hSt', -⟩ := hprem.2 m hm v₀ m₀ ⟨n, hin⟩
  -- `M` is the delivery state with the continuation already popped: the machine the write
  -- happens at.
  have hMok : StateOk κ Γ' I' (reCtl m₀ (.value v₀) []) := StateOk_reCtl hSt' _ _
  have hdenM : denM τ (reCtl m₀ (.value v₀) []) v₀ := denM_reCtl.mpr hden
  -- **The arm**: is `self` a live, unfrozen reference?
  by_cases hcase : ∃ o, m₀.currentFrame.self = .ref o ∧ (m₀.heap.get o).frozen = false
  · obtain ⟨o, hs, hfr⟩ := hcase
    have hlive : o < m₀.heap.objs.size := hSt'.selfLive o hs
    -- the write, and its transport
    have hs' : (reCtl m₀ (.value v₀) [] : Machine).currentFrame.self = .ref o := hs
    have hw : IvarWrite x v₀ (.ref o) (reCtl m₀ (.value v₀) [])
        (Interp.bindIvar (reCtl m₀ (.value v₀) []) x v₀) := ivarWrite_bindIvar hs' hlive
    have hmut : Mut (reCtl m₀ (.value v₀) []) _ := hw.toMut
    -- **the tail**: the write step, then the end of the run
    have hstep : Interp.stepFn (reCtl m₀ (.value v₀) [.asgnK .ivar x])
        = .next (reCtl (Interp.bindIvar (reCtl m₀ (.value v₀) []) x v₀) (.value v₀) []) := by
      rw [stepFn_asgnK_ivar hs' (by simpa using hfr)]
      congr 1
      simp only [Interp.withCtl, reCtl]
      rw [show (Interp.bindIvar (reCtl m₀ (.value v₀) []) x v₀).kont = [] from
        bindIvar_kont _ _ _]
    obtain ⟨hveq, hmeq⟩ := run_two hstep hout
    subst hmeq
    subst hveq
    refine ⟨?_, ?_, ?_⟩
    · exact ((hframe.trans (Framed_reCtl m₀ _ _)).trans hmut.framed).trans (Framed_reCtl _ _ _)
    · exact denM_reCtl.mpr (denM_ivarWrite_post hw hMok.sat
        (by rw [Ratchet.ivarAsgnOk, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
              Bool.and_eq_true, Bool.and_eq_true] at hst
            exact hst.1.1.1.1.2) hdenM)
    -- Both outgoing conjuncts (`SemJudge`'s §Outgoing conformance); an ivar assignment
    -- declares nothing, so the reported context is the incoming one.
    · exact ⟨StateOk_reCtl (StateOk_ivarWrite hMok (hs' ▸ hw) hdenM hst) _ _,
             StateOk_reCtl (StateOk_ivarWrite hMok (hs' ▸ hw) hdenM hst) _ _⟩
  · -- **the two raising arms**: no value, so nothing to prove
    exfalso
    have hstuck : ∀ o, m₀.currentFrame.self = .ref o → (m₀.heap.get o).frozen = true := by
      intro o hs
      by_cases hfr : (m₀.heap.get o).frozen = true
      · exact hfr
      · exact absurd ⟨o, hs, by simpa using hfr⟩ hcase
    obtain ⟨f₂, hf₂⟩ := hout
    match f₂ with
    | 0 => rw [run_zero] at hf₂; exact absurd hf₂ (by simp)
    | f₃ + 1 =>
      rcases stepFn_asgnK_ivar_stuck (v := v₀) (x := x) hstuck with ⟨err, hu⟩ | ⟨M, hn, hj, hkm⟩
      · rw [run_succ, hu] at hf₂; exact absurd hf₂ (by simp)
      · rw [run_succ, hn] at hf₂
        exact jump_empty_never_value f₃ M v m' hj hkm hf₂

#print axioms Sem.Judge.ivarAsgn

end Ratchet.Denote
