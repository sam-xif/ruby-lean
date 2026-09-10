import Denote.Sem.StepAct

/-!
# `Denote/Sem/StepDispatch.lean` — stage 2 of the walk: `Interp/Dispatch.lean`

Stage 1 is `StepSupport.lean` (plus `StepAct.lean`, which holds stage 2's hardest helper,
`enterUserMethod`). This is the rest of the layer above it, in the bottom-up order
`StepEval.lean` records.

`eigenclassOf` is the one with structure: a fuel recursion that walks the superclass chain and,
at each level that has no eigenclass yet, **allocates one and writes the attachee's `eigen`
field**. That is `MCap.push_free_then_set`'s shape — a capture-free `.cls` push (empty method
table) followed by a payload-preserving `set` — and the induction is on the fuel, which is why
`Interp.eigenclassOf` is fuel-bounded rather than `partial` in the first place.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Ratchet.Denote

open RubyCore

/-- **`eigenclassOf.go`**, by induction on the fuel. -/
theorem Step.eigenclassOf_go {b : FrameId} :
    ∀ (fuel : Nat) (m : Machine) (o : ObjId), StepInv b m →
      Step b m (Interp.eigenclassOf.go m o fuel).2
  | 0, m, o, h => Step.refl h
  | fuel + 1, m, o, h => by
    rw [Interp.eigenclassOf.go]
    split
    · exact Step.refl h
    · -- compute the metaclass superclass (possibly recursing), then allocate and write
      have hgo : ∀ (m₂ : Machine) (o₂ : ObjId), StepInv b m₂ →
          Step b m₂ (match (m₂.heap.get o₂).payload with
            | .cls c => match c.superclass with
              | some s => Interp.eigenclassOf.go m₂ s fuel
              | none => ((if c.isModule then Boot.moduleId else Boot.classId), m₂)
            | _ => ((m₂.heap.get o₂).klass, m₂)).2 := by
        intro m₂ o₂ h₂
        split
        · split
          · exact Step.eigenclassOf_go fuel m₂ _ h₂
          · exact Step.refl h₂
        · exact Step.refl h₂
      refine Step.heap' (hgo m o h) rfl rfl ?_
      refine MCap.push_free_then_set rfl ?_ rfl
      exact fun _ => capAt_cls_nil rfl rfl

/-- **`eigenclassOf`** itself, at the fuel the model gives it. -/
theorem Step.eigenclassOf {b : FrameId} (m : Machine) (o : ObjId) (h : StepInv b m) :
    Step b m (Interp.eigenclassOf m o).2 := by
  rw [Interp.eigenclassOf]
  exact Step.eigenclassOf_go _ m o h

/-- `eigenclassOf` as a **peel**, for an arm that reaches it after doing something else —
`enterClassBody`'s create path allocates and registers the constant first. -/
theorem Step.eigenclassOf' {b : FrameId} {m mid : Machine} (s : Step b m mid) (o : ObjId) :
    Step b m (Interp.eigenclassOf mid o).2 := s.trans (Step.eigenclassOf mid o s.2)

/-! ### `enterClassBody` — peeled by hand, because `split at h` cannot see these scrutinees

The obstruction that parked this (and `callClosure`, and `enterHandler`) is one thing:
`split at h` peels the chains in `Builtins` — six hundred arms under a single `match` on `bid` —
and fails on the ones in `Interp/`, where the arms are guarded by `let`-bound scrutinees and
helper calls. `Builtins` was the wrong sample to calibrate the tactic on, and `split_ifs` is
Mathlib-only and not in this package.

The technique that works is `cases hc : <scrutinee>` followed by `rw [hc] at hstep` — naming the
scrutinee rather than asking `split` to find it, which is what `FrameLocal.lean` does for
`newImpl_locals` and what closed `doReturn` in stage 1.

Two paths. **Reopen** finds the existing class object and pushes straight away. **Create**
allocates the class (`.cls`, empty method table), registers the constant in the enclosing
namespace (`constSetIn`, a payload-preserving `setClassPayload`), realises the metaclass chain
through `Step.eigenclassOf`, then pushes. Either way the pushed frame's `captured` is
**defaulted**, so `Step.push_free` discharges both of `Sealed.push`'s premises vacuously — one of
the four sites the L266 `Option` made free. -/

/-! **Deprioritised, not blocked.** `enterClassBody` feeds `evalExpr`'s `class`/`module` arms,
whose rules (`classStmt`/`moduleStmt`) belong to the declaration family — so it is *not* on the
path to any of the 26 reachable rules. Its create path is understood (allocate the class,
`constSetIn` the constant, `Step.eigenclassOf'`, then `Step.push_free`) and its two remaining
`rfl`s are heap-shape work against `setClassPayload` nested under `constSetIn`'s own match. The
call family is the reachable prize, so the effort goes there.

The reopen path, for the record, is one line: `Step.push_free h _ rfl` under `Step.withKont'`. -/


/-! ### `enterUserMethod` — **proved**, in `StepAct.lean`

The one `frames.push` whose `captured` comes from a **`MethodDef`** rather than a frame or a
closure, which is why L267 added `Sealed`'s third clause; and the helper three attempts parked.
It is now `Step.enterUserMethod` (`Denote/Sem/StepAct.lean`), through a mirror of the function
whose five machine-touching stages are named and whose fidelity is one `rfl` — read that file's
header for the nineteenth stall point (why hand-splitting the conditions cannot work either) and
for the rule it generalises. Its heap fact travels on `PreAct` (`StepSupport.lean`), which is
`Step` plus "every installed method is still installed". -/


/-! ## The `methodIn` bridges — every caller of `enterUserMethod` has one

`Step.enterUserMethod` (`StepAct.lean`) wants its `MethodDef` as a **heap** fact
(`methodIn m.heap k n = some md`), because that is what `Sealed.meth` consumes. Every caller
holds it in a different currency: `lookup` (receiver-keyed), `methodOn` (class-keyed),
`lookupAbove` (the block fallback), `superFound` (`super`), `userInit?` (`Class#new`) and
`moduleHook` (the mixin hooks). All six are the same walk over one class's own table, so they
share one arm lemma and one `firstM` lemma.

Keyed on `methodIn` rather than on membership in `cp.methods` for the sixth stall point's reason,
the one `CapAt`'s class arm was keyed that way for too (clink 62): the membership form is easier
to establish and `Sealed.meth` cannot consume it. -/

/-- The generic `firstM` bridge: five of the six lookups are a `firstM` over an ancestor list. -/
theorem methodIn_of_firstM {h : Heap} {n : String} (f : ObjId → Option (ObjId × MethodDef))
    (hf : ∀ c owner md, f c = some (owner, md) → methodIn h owner n = some md) :
    ∀ (l : List ObjId) {owner : ObjId} {md : MethodDef},
      l.firstM f = some (owner, md) → methodIn h owner n = some md
  | [], _, _, hl => by simp [List.firstM] at hl
  | c :: rest, owner, md, hl => by
    rw [List.firstM] at hl
    cases hc : f c with
    | none => rw [hc] at hl; simp at hl; exact methodIn_of_firstM f hf rest hl
    | some p =>
      rw [hc] at hl
      simp at hl
      subst hl
      exact hf c owner md hc

/-- The arm every one of these lookups is built out of: read `n` off one class's own table. -/
theorem methodIn_of_arm {h : Heap} {n : String} {c owner : ObjId} {md : MethodDef}
    (hc : (match h.classPayload? c with
      | some cp => (cp.methods.find? (·.1 == n)).map (fun (p : String × MethodDef) => (c, p.2))
      | none => none) = some (owner, md)) : methodIn h owner n = some md := by
  cases hcp : h.classPayload? c with
  | none => rw [hcp] at hc; simp at hc
  | some cp =>
    rw [hcp] at hc
    dsimp only at hc
    cases hfd : cp.methods.find? (·.1 == n) with
    | none => rw [hfd] at hc; simp at hc
    | some p =>
      rw [hfd] at hc
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨ho, hd⟩ := hc
      subst ho; subst hd
      unfold methodIn
      rw [hcp]
      simp only [Option.bind_some, hfd, Option.map_some]


/-- **`methodOn`** — the class-keyed lookup. -/
theorem methodIn_of_methodOn {h : Heap} {k : ObjId} {n : String} {owner : ObjId} {md : MethodDef}
    (hl : Interp.methodOn h k n = some (owner, md)) : methodIn h owner n = some md := by
  rw [Interp.methodOn] at hl
  exact methodIn_of_firstM _ (fun _ _ _ hc => methodIn_of_arm hc) _ hl

/-- **`lookupAbove`** — the block fallback's walk. -/
theorem methodIn_of_lookupAbove {h : Heap} {v : Value} {ow : ObjId} {n : String}
    {owner : ObjId} {md : MethodDef}
    (hl : Interp.lookupAbove h v ow n = some (owner, md)) : methodIn h owner n = some md := by
  rw [Interp.lookupAbove] at hl
  exact methodIn_of_firstM _ (fun _ _ _ hc => methodIn_of_arm hc) _ hl

/-- **`superFound`** — what `super` re-dispatches to. -/
theorem methodIn_of_superFound {h : Heap} {k dm : ObjId} {n : String}
    {owner : ObjId} {md : MethodDef}
    (hl : Interp.superFound h k dm n = some (owner, md)) : methodIn h owner n = some md := by
  rw [Interp.superFound] at hl
  exact methodIn_of_firstM _ (fun _ _ _ hc => methodIn_of_arm hc) _ hl

/-- **`lookup`** — the receiver-keyed walk, by induction on the ancestor list. -/
theorem methodIn_of_lookup_go {h : Heap} {n : String} :
    ∀ (l : List ObjId) {owner : ObjId} {md : MethodDef},
      RubyCore.lookup.go h n l = some (owner, md) → methodIn h owner n = some md
  | [], _, _, hl => by rw [RubyCore.lookup.go] at hl; simp at hl
  | c :: rest, owner, md, hl => by
    rw [RubyCore.lookup.go] at hl
    cases hcp : h.classPayload? c with
    | none => rw [hcp] at hl; dsimp only at hl; exact methodIn_of_lookup_go rest hl
    | some cp =>
      rw [hcp] at hl
      dsimp only at hl
      cases hfd : cp.methods.find? (·.1 == n) with
      | none => rw [hfd] at hl; dsimp only at hl; exact methodIn_of_lookup_go rest hl
      | some p =>
        rw [hfd] at hl
        dsimp only at hl
        simp only [Option.some.injEq, Prod.mk.injEq] at hl
        obtain ⟨ho, hd⟩ := hl
        subst ho; subst hd
        unfold methodIn
        rw [hcp]
        simp only [Option.bind_some, hfd, Option.map_some]

theorem methodIn_of_lookup {h : Heap} {v : Value} {n : String} {owner : ObjId} {md : MethodDef}
    (hl : RubyCore.lookup h v n = some (owner, md)) : methodIn h owner n = some md := by
  rw [RubyCore.lookup] at hl
  exact methodIn_of_lookup_go _ hl

/-- **`userInit?`** — `Class#new`'s initializer, which is a `methodOn` under a `builtin` gate. -/
theorem methodIn_of_userInit {h : Heap} {k : ObjId} {md : MethodDef}
    (hl : Interp.userInit? h k = some md) : ∃ c, methodIn h c "initialize" = some md := by
  rw [Interp.userInit?] at hl
  cases hm : Interp.methodOn h k "initialize" with
  | none => rw [hm] at hl; simp at hl
  | some p =>
    rw [hm] at hl
    dsimp only at hl
    split at hl
    · simp only [Option.some.injEq] at hl
      subst hl
      exact ⟨p.1, methodIn_of_methodOn (by rw [hm])⟩
    · simp at hl

/-- **`moduleHook`** — the `included`/`prepended`/`extended` hook, on the module's eigenclass. -/
theorem methodIn_of_moduleHook {m : Machine} {mo : ObjId} {n : String} {md : MethodDef}
    (hl : Interp.moduleHook m mo n = some md) : ∃ c, methodIn m.heap c n = some md := by
  rw [Interp.moduleHook] at hl
  cases he : (m.heap.get mo).eigen with
  | none => rw [he] at hl; simp at hl
  | some e =>
    rw [he] at hl
    dsimp only at hl
    cases hm : Interp.methodOn m.heap e n with
    | none => rw [hm] at hl; simp at hl
    | some p =>
      rw [hm] at hl
      simp only [Option.map_some, Option.some.injEq] at hl
      subst hl
      exact ⟨p.1, methodIn_of_methodOn (by rw [hm])⟩



/-! ## Stage 2's remaining helpers, and the ordering rule they all needed

`missNoMethod`, `visError?`, and the native block-iterator trio `iterStep`/`startIter`/
`tryIterator`.

**The ordering rule, in a third costume.** `notes.md` §The second walk item 3 says an argument
that *determines* metavariables goes early and one that *consumes* them goes late. Here it
decides whether a peel works at all: `callClosure`'s peel with the `Step` (or the closure fact)
first unifies `?mid` with `m` and then rejects the real machine, so the peels below take **the
`.next m'` hypothesis first** and let the goal's own machine determine `mid`. -/


/-- **`missNoMethod`** — the default `method_missing`: a `NameError` or a `NoMethodError`. -/
theorem Step.missNoMethod {b : FrameId} {m m' : Machine} (h : StepInv b m) (recv : Value)
    (site : SendSite) (mname : String) (args : List Value)
    (hstep : Interp.missNoMethod m recv site mname args = .next m') : Step b m m' := by
  rw [Interp.missNoMethod] at hstep
  split at hstep
  · cases hstep; exact Step.raiseErr h _ _
  · cases hstep; exact Step.raiseErr h _ _

/-- **`visError?`** — the private/protected refusal, when it answers at all. -/
theorem Step.visError {b : FrameId} {m m' : Machine} (h : StepInv b m) (recv : Value)
    (site : SendSite) (md : MethodDef) (mname : String)
    (hstep : Interp.visError? m recv site md mname = some (.next m')) : Step b m m' := by
  rw [Interp.visError?.eq_def] at hstep
  repeat (any_goals (first
    | (cases hstep; exact Step.raiseErr h _ _)
    | (obtain ⟨-, he⟩ := hstep; exact he ▸ Step.raiseErr h _ _)
    | simp at hstep
    | split at hstep))

/-- `callClosure` as a peel — **hypothesis first**, so the goal's own machine determines `mid`
rather than the `Step` argument or the closure fact doing it (both of which unify `?mid` with
`m` and then reject the real one). The same ordering rule as `notes.md` §The second walk item 3:
an argument that *determines* metavariables goes early. -/
theorem Step.callClosure_at {b : FrameId} {m mid m' : Machine} {o : ObjId} {cl : Closure}
    {args : List Value} {brk : Option FrameId} {selfOv : Option Value} {defmodOv : Option ObjId}
    (hstep : Interp.callClosure mid cl args brk selfOv defmodOv = .next m')
    (s : Step b m mid) (hh : mid.heap = m.heap)
    (hcl : procClosure? m.heap (.ref o) = some cl) : Step b m m' :=
  s.trans (Step.callClosure s.2 (by rw [hh]; exact hcl) args brk selfOv defmodOv hstep)

/-- **`iterStep`** — the native block-iterator's driver: the final value (which `collect`
allocates) or one more block call. The closure is a heap fact, as `callClosure` needs. -/
theorem Step.iterStep {b : FrameId} {m m' : Machine} (h : StepInv b m) {o : ObjId}
    {cl : Closure} (hcl : procClosure? m.heap (.ref o) = some cl) (brk : FrameId)
    (rest : List (List Value)) (kind : IterKind) (acc : List Value) (retVal : Value)
    (hstep : Interp.iterStep m cl brk rest kind acc retVal = .next m') : Step b m m' := by
  rw [Interp.iterStep.eq_def] at hstep
  split at hstep
  · -- the loop is over: `collect` allocates the result array, the others do not
    dsimp only at hstep
    repeat (any_goals (first
      | (cases hstep; exact Step.withCtl h _)
      | (cases hstep; refine Step.withCtl' ?_ _; exact Step.allocArr h _)
      | split at hstep))
  · -- one more call: push the `iterK`, then invoke the block
    dsimp only at hstep
    exact Step.callClosure_at hstep (Step.frameOnly h rfl rfl rfl) rfl hcl

/-- `iterStep` as a peel, hypothesis first for the same reason. -/
theorem Step.iterStep_at {b : FrameId} {m mid m' : Machine} {o : ObjId} {cl : Closure}
    {brk : FrameId} {rest : List (List Value)} {kind : IterKind} {acc : List Value}
    {retVal : Value}
    (hstep : Interp.iterStep mid cl brk rest kind acc retVal = .next m')
    (s : Step b m mid) (hh : mid.heap = m.heap)
    (hcl : procClosure? m.heap (.ref o) = some cl) : Step b m m' :=
  s.trans (Step.iterStep s.2 (by rw [hh]; exact hcl) brk rest kind acc retVal hstep)

/-- **`startIter`** — the iterator activation: a frame whose `captured` is defaulted
(`Step.push_free`), the `frameK` boundary, then the loop. -/
theorem Step.startIter {b : FrameId} {m m' : Machine} (h : StepInv b m) {o : ObjId}
    {cl : Closure} (hcl : procClosure? m.heap (.ref o) = some cl) (recv : Value) (mname : String)
    (elemArgs : List (List Value)) (kind : IterKind) (initAcc : List Value) (retVal : Value)
    (hstep : Interp.startIter m recv mname cl elemArgs kind initAcc retVal = .next m') :
    Step b m m' := by
  rw [Interp.startIter] at hstep
  dsimp only at hstep
  exact Step.iterStep_at hstep (Step.frameOnly' (Step.push_free h _ rfl) rfl rfl rfl) rfl hcl

/-- …and both as peels off a `PreAct`, which is how `tryIterator` reaches them: the `Hash#each`
arms allocate one array per entry *before* the loop starts, so the closure fact travels. -/
theorem Step.startIter_pre {b : FrameId} {m mid m' : Machine} {o : ObjId} {cl : Closure}
    {recv : Value} {mname : String} {elemArgs : List (List Value)} {kind : IterKind}
    {initAcc : List Value} {retVal : Value}
    (hstep : Interp.startIter mid recv mname cl elemArgs kind initAcc retVal = .next m')
    (p : PreAct b m mid) (hcl : procClosure? m.heap (.ref o) = some cl) : Step b m m' :=
  p.1.trans (Step.startIter p.1.2 (p.2.2 o cl hcl) recv mname elemArgs kind initAcc retVal hstep)



/-- The fold over an **`Array`**, which is what `Hash#each`'s per-entry array allocation walk
normalises to. One `Array.foldl_toList` off `PreAct.foldPair'`. -/
theorem PreAct.foldPairArr {b : FrameId} {α β : Type} (f : β × Machine → α → β × Machine)
    (hf : ∀ (p : β × Machine) (a : α), StepInv b p.2 → PreAct b p.2 (f p a).2)
    (l : Array α) (init : β) {m mid : Machine} (s : PreAct b m mid) :
    PreAct b m (l.foldl f (init, mid)).2 := by
  rw [← Array.foldl_toList]
  exact PreAct.foldPair' f hf _ _ s

set_option maxHeartbeats 1000000 in
/-- **`tryIterator`** — the native block-iterator entry: which `(recv, mname)` pairs run a block
loop, and with what per-iteration argument lists. The block being a Proc *in the heap* is what
`startIter`'s push needs, and it is exactly the arm's own hypothesis; the two `Hash` arms
allocate one `[k, v]` array per entry **before** the loop starts, which is what `PreAct` carries
the closure fact across. -/
theorem Step.tryIterator {b : FrameId} {m m' : Machine} (h : StepInv b m) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value)
    (hstep : Interp.tryIterator m recv mname args blk = some (.next m')) : Step b m m' := by
  rw [Interp.tryIterator.eq_def] at hstep
  cases hblk : blk with
  | none => rw [hblk] at hstep; simp at hstep
  | some bv =>
    rw [hblk] at hstep
    dsimp only at hstep
    cases bv
    case ref bo =>
      dsimp only at hstep
      cases hpay : (m.heap.get bo).payload
      case proc cl =>
        have hcl : procClosure? m.heap (.ref bo) = some cl := by rw [procClosure?, hpay]
        have hfold : ∀ (p : List (List Value) × Machine) (a : Value × Value),
            StepInv b p.2 → PreAct b p.2 (
              (let r := Builtins.allocArr p.2 #[a.1, a.2]
               (p.1 ++ [[r.1]], r.2) : List (List Value) × Machine)).2 :=
          fun p a hp => (PreAct.refl hp).allocArr _
        rw [hpay] at hstep
        dsimp only at hstep
        repeat (any_goals (first
          | (simp only [Option.some.injEq] at hstep)
          | exact Step.startIter_pre hstep (PreAct.refl h) hcl
          | exact Step.startIter_pre hstep (PreAct.foldPair' _ hfold _ _ (PreAct.refl h)) hcl
          | exact Step.startIter_pre hstep (PreAct.foldPairArr _ hfold _ _ (PreAct.refl h)) hcl
          | (cases hstep; exact Step.withCtl h _)
          | (simp at hstep)
          | (split at hstep)))
      all_goals (rw [hpay] at hstep; simp at hstep)
    all_goals (simp at hstep)

#print axioms methodIn_of_arm
#print axioms methodIn_of_lookup
#print axioms methodIn_of_methodOn
#print axioms methodIn_of_lookupAbove
#print axioms methodIn_of_superFound
#print axioms methodIn_of_userInit
#print axioms methodIn_of_moduleHook
#print axioms Step.missNoMethod
#print axioms Step.visError
#print axioms Step.iterStep
#print axioms Step.startIter
#print axioms Step.tryIterator

#print axioms Step.eigenclassOf_go
#print axioms Step.eigenclassOf

end Ratchet.Denote
