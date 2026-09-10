import Denote.Sem.StepDispatch

/-!
# `Denote/Sem/StepReflect.lean` — stage 4 of the walk: `Interp/Reflect.lean`

The reflection dispatcher and its fifteen `reflect*` helpers. `dispatchMiss` routes through
`tryReflect`, so the whole dispatch spine (`invokeDispatch`/`invoke`/`finishSend`) waits on this
file — it is not an optional corner.

Most of the helpers are **queries**: they answer a `Bool`/`Symbol`/array and write only `ctl`, so
they close on `Step.withCtl`, one allocation or a `raiseErr`, and the shared closer list
(`step_reflect`) does them uniformly. The four that touch the method graph or push a frame are
where the content is, and each needed exactly one new heap lemma:

| helper | what it writes | the lemma |
|---|---|---|
| `define_method` | a method whose body is a **closure** | `CapMono.defineMethod_clos` — the edge is the Proc's own, or `none` by J33's capture erasure |
| `alias_method` | a **copy** of an installed method | `CapMono.defineMethod_copy` — the copy's edge is the original's |
| `remove_method`/`undef_method` | a filtered table, or a tombstone | `CapMono.setClassPayload_filter` — removing a name can only *hide* an edge |
| `public`/`private`/`module_function` | a copy per name, plus an eigenclass copy | `methodIn_defineMethod` + `PayKeep.eigenclassOf` |

## Two things this file establishes about the *relations*, not the helpers

**`PreAct` is false across `defineMethod`.** Its method conjunct says every installed method is
still installed, and `defineMethod` **replaces** — a redefinition of the same name drops the old
entry. So the visibility and removal walks are `Step`, not `PreAct`, and what their second write
needs is not the old fact transported but the **new** one established (`methodIn_defineMethod`).
The type checker found this, by refusing a `PayKeep` for a `defineMethod`.

**`PayKeep` is the right interface for `eigenclassOf`.** "The heap only grew" is false of it (it
writes the attachee's `eigen`), but "every payload that was there is still there" is true — and
payloads are all `methodIn`/`procClosure?` read. So `PayKeep` transports both.

## And the ordering rule, fifth and sixth costume

* a composition whose *intermediate* carries an argument the goal does not mention
  (`(eigenclassOf m ?o).2`) must be supplied as **one `exact` term**, not a `refine … ?_`, or
  `?o` is never determined;
* a peel whose target is a record update (`m.setCurrentFrame ?fr`) must be reached by a
  **separate `refine`**, or the `rfl` side conditions unify `?fr` with the *unmodified* frame and
  the closer proves the wrong statement.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Ratchet.Denote

open RubyCore

/-- A capture edge is readable at the class that installs the method. -/
theorem capAt_of_methodIn {h : Heap} {k : ObjId} {n : String} {md : MethodDef} {p : Nat}
    (hmd : methodIn h k n = some md) (hcf : md.capturedFrame = some p) : CapAt (h.get k) p := by
  have hcp : ∃ cp, h.classPayload? k = some cp := by
    cases hc : h.classPayload? k with
    | none => rw [methodIn, hc] at hmd; exact absurd hmd (by simp)
    | some cp => exact ⟨cp, rfl⟩
  obtain ⟨cp, hc⟩ := hcp
  have hpl : (h.get k).payload = .cls cp := by
    simp only [Heap.classPayload?] at hc
    cases hp : (h.get k).payload with
    | cls c => rw [hp] at hc; exact congrArg Payload.cls (Option.some.inj hc)
    | _ => rw [hp] at hc; exact absurd hc (by simp)
  simp only [CapAt, hpl]
  exact ⟨n, md, by rw [← methodIn_eq_methodOf hc]; exact hmd, hcf⟩

/-- …and at the Proc that carries it. -/
theorem capAt_of_procClosure {h : Heap} {o : ObjId} {cl : Closure} {p : Nat}
    (hcl : procClosure? h (.ref o) = some cl) (hcf : cl.captured = some p) :
    CapAt (h.get o) p := by
  rw [procClosure?] at hcl
  cases hp : (h.get o).payload with
  | proc c =>
    rw [hp] at hcl
    dsimp only at hcl
    simp only [CapAt, hp]
    rw [Option.some.inj hcl]
    exact hcf
  | _ => rw [hp] at hcl; exact absurd hcl (by simp)

/-- **`constSetIn`** — a `setClassPayload` that rewrites `consts` and leaves `methods`. -/
theorem CapMono.of_constSetIn (h : Heap) (cls : ObjId) (n : String) (v : Value) :
    CapMono h (RubyCore.constSetIn h cls n v) := by
  unfold RubyCore.constSetIn
  cases hc : h.classPayload? cls with
  | none => exact CapMono.refl h
  | some c => exact CapMono.setClassPayload_methods hc rfl


/-! ### `PayKeep`: the heap's *payloads* survived, which is all `PreAct` reads

`PreAct`'s two transports read `payload` and nothing else (`methodIn` through `classPayload?`,
`procClosure?` directly), so the right interface for a helper that both allocates *and* writes a
field is not "the heap only grew" — `eigenclassOf` writes the attachee's `eigen`, an object
already there — but **"every payload that was there is still there"**. -/

def PayKeep (h h' : Heap) : Prop :=
  h.objs.size ≤ h'.objs.size ∧ ∀ o, o < h.objs.size → (h'.get o).payload = (h.get o).payload

theorem PayKeep.refl (h : Heap) : PayKeep h h := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem PayKeep.trans {a b c : Heap} (h₁ : PayKeep a b) (h₂ : PayKeep b c) : PayKeep a c :=
  ⟨Nat.le_trans h₁.1 h₂.1,
   fun o hlt => by rw [h₂.2 o (Nat.lt_of_lt_of_le hlt h₁.1), h₁.2 o hlt]⟩

theorem PayKeep.alloc (h : Heap) (obj : Object) : PayKeep h (h.alloc obj).2 :=
  ⟨by show h.objs.size ≤ (h.objs.push obj).size; simp,
   fun o hlt => by rw [alloc_get_lt obj hlt]⟩

theorem PayKeep.set_payload {h : Heap} {o : ObjId} {obj : Object}
    (hp : obj.payload = (h.get o).payload) : PayKeep h (h.set o obj) := by
  refine ⟨by show h.objs.size ≤ (h.objs.set! o obj).size; simp [Array.set!], fun o' hlt => ?_⟩
  by_cases hf : o' = o
  · subst hf
    rw [show Heap.get (h.set o' obj) o' = obj from getD_set!_self h.objs o' obj hlt]
    exact hp
  · rw [show Heap.get (h.set o obj) o' = h.get o' from getD_set!_ne h.objs o o' obj hf]

/-- `PreAct` across a heap change that kept the payloads. -/
theorem PreAct.heapKeep {b : FrameId} {m mid m' : Machine} (p : PreAct b m mid)
    (hs : m'.stack = mid.stack) (hf : m'.frames = mid.frames) (hcm : MCap mid m')
    (hk : PayKeep mid.heap m'.heap) : PreAct b m m' :=
  ⟨Step.heap' p.1 hs hf hcm,
   fun k n md hm => by
     have h0 := p.2.1 k n md hm
     rw [methodIn, Heap.classPayload?, hk.2 k (methodIn_lt h0), ← Heap.classPayload?, ← methodIn]
     exact h0,
   fun o cl hc => by
     have h0 := p.2.2 o cl hc
     rw [procClosure?, hk.2 o (procClosure_lt h0)]
     rw [← procClosure?]
     exact h0⟩

/-- **`eigenclassOf` at `PreAct`** — `reflectDefineMethod` looks its Proc up *before* the
eigenclass chain is realised and installs the method after, so the closure fact has to cross the
walk. `Step.eigenclassOf_go`'s induction, one relation up. -/
theorem PreAct.eigenclassOf_go {b : FrameId} {m : Machine} :
    ∀ (fuel : Nat) (mid : Machine) (o : ObjId), PreAct b m mid →
      PreAct b m (Interp.eigenclassOf.go mid o fuel).2
  | 0, mid, o, p => p
  | fuel + 1, mid, o, p => by
    rw [Interp.eigenclassOf.go]
    split
    · exact p
    · have hgo : ∀ (m₂ : Machine) (o₂ : ObjId), PreAct b m m₂ →
          PreAct b m (match (m₂.heap.get o₂).payload with
            | .cls c => match c.superclass with
              | some s => Interp.eigenclassOf.go m₂ s fuel
              | none => ((if c.isModule then Boot.moduleId else Boot.classId), m₂)
            | _ => ((m₂.heap.get o₂).klass, m₂)).2 := by
        intro m₂ o₂ p₂
        split
        · split
          · exact PreAct.eigenclassOf_go fuel m₂ _ p₂
          · exact p₂
        · exact p₂
      refine (hgo mid o p).heapKeep rfl rfl ?_ ?_
      · refine MCap.push_free_then_set rfl ?_ rfl
        exact fun _ => capAt_cls_nil rfl rfl
      · exact (PayKeep.alloc _ _).trans (PayKeep.set_payload rfl)

theorem PreAct.eigenclassOf {b : FrameId} {m mid : Machine} (p : PreAct b m mid) (o : ObjId) :
    PreAct b m (Interp.eigenclassOf mid o).2 := by
  rw [Interp.eigenclassOf]
  exact PreAct.eigenclassOf_go _ mid o p



/-! ## Stage 4, the light half of `tryReflect`

One `Step` lemma per `reflect*` helper. Most are *queries* — they answer a `Bool`/`Symbol`/array
and write only `ctl`, so they close on `Step.withCtl`, one allocation or a `raiseErr`. The closer
list is shared, and `step_reflect` names it once rather than repeating it per helper. -/

set_option hygiene false in
/-- The shared closer list for a `reflect*` walk. `split at hstep` **last**: peeling before the
closers is what §The second walk measured, and a `simp at hstep` earlier would renormalise the
matcher a later `split` has to see. -/
macro "step_reflect" h:ident hs:ident : tactic => `(tactic|
  (repeat (any_goals (first
    | (simp only [Option.some.injEq] at $hs:ident)
    | (cases $hs:ident; exact Step.withCtl $h _)
    | (cases $hs:ident; exact Step.raiseErr $h _ _)
    | (cases $hs:ident
       refine Step.withCtl' ?_ _
       exact Step.allocArr $h _)
    | (cases $hs:ident
       refine Step.withCtl' ?_ _
       exact Step.heap $h rfl rfl (MCap.set_payload_eq rfl rfl))
    | (cases $hs:ident
       refine Step.withCtl' ?_ _
       exact Step.heap $h rfl rfl (CapMono.of_constSetIn _ _ _ _))
    | (cases $hs:ident
       refine Step.withCtl' ?_ _
       exact Step.eigenclassOf _ _ $h)
    | (simp at $hs:ident)
    | (split at $hs:ident)))))

/-- **`instance_variable_get`/`instance_variable_defined?`** — a query. -/
theorem Step.reflectIvarGet {b : FrameId} {m m' : Machine} (h : StepInv b m) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value)
    (hstep : Interp.reflectIvarGet m recv mname args blk = some (.next m')) : Step b m m' := by
  rw [Interp.reflectIvarGet.eq_def] at hstep
  step_reflect h hstep

/-- **`instance_variable_set`** — a `Heap.set` with the payload copied, or a `FrozenError`. -/
theorem Step.reflectIvarSet {b : FrameId} {m m' : Machine} (h : StepInv b m) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value)
    (hstep : Interp.reflectIvarSet m recv mname args blk = some (.next m')) : Step b m m' := by
  rw [Interp.reflectIvarSet.eq_def] at hstep
  step_reflect h hstep

/-- **`instance_variables`** — one array allocation. -/
theorem Step.reflectIvarNames {b : FrameId} {m m' : Machine} (h : StepInv b m) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value)
    (hstep : Interp.reflectIvarNames m recv mname args blk = some (.next m')) : Step b m m' := by
  rw [Interp.reflectIvarNames.eq_def] at hstep
  step_reflect h hstep

/-- **`const_get`/`const_defined?`** — a query, or a `NameError`. -/
theorem Step.reflectConstGet {b : FrameId} {m m' : Machine} (h : StepInv b m) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value)
    (hstep : Interp.reflectConstGet m recv mname args blk = some (.next m')) : Step b m m' := by
  rw [Interp.reflectConstGet.eq_def] at hstep
  step_reflect h hstep

/-- **`const_set`** — `constSetIn`, a `setClassPayload` that leaves `methods`. -/
theorem Step.reflectConstSet {b : FrameId} {m m' : Machine} (h : StepInv b m) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value)
    (hstep : Interp.reflectConstSet m recv mname args blk = some (.next m')) : Step b m m' := by
  rw [Interp.reflectConstSet.eq_def] at hstep
  step_reflect h hstep

/-- **`method_defined?`** and friends — a query. -/
theorem Step.reflectMethodDefined {b : FrameId} {m m' : Machine} (h : StepInv b m) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value)
    (hstep : Interp.reflectMethodDefined m recv mname args blk = some (.next m')) :
    Step b m m' := by
  rw [Interp.reflectMethodDefined.eq_def] at hstep
  step_reflect h hstep

/-- **`respond_to?`** — a query (a user `respond_to_missing?` is a gate). -/
theorem Step.reflectRespondTo {b : FrameId} {m m' : Machine} (h : StepInv b m) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value)
    (hstep : Interp.reflectRespondTo m recv mname args blk = some (.next m')) : Step b m m' := by
  rw [Interp.reflectRespondTo.eq_def] at hstep
  step_reflect h hstep

/-- **`singleton_class`** — realises the eigenclass chain. -/
theorem Step.reflectSingletonClass {b : FrameId} {m m' : Machine} (h : StepInv b m)
    (recv : Value) (mname : String) (args : List Value) (blk : Option Value)
    (hstep : Interp.reflectSingletonClass m recv mname args blk = some (.next m')) :
    Step b m m' := by
  rw [Interp.reflectSingletonClass.eq_def] at hstep
  step_reflect h hstep

/-- **`throw`** — a jump, or the `UncaughtThrowError` raised at the throw site. -/
theorem Step.reflectThrow {b : FrameId} {m m' : Machine} (h : StepInv b m) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value)
    (hstep : Interp.reflectThrow m recv mname args blk = some (.next m')) : Step b m m' := by
  rw [Interp.reflectThrow.eq_def] at hstep
  step_reflect h hstep

/-- **`attr_reader`/`attr_writer`/`attr_accessor`** — `defineAttr` then one array. -/
theorem Step.reflectAttr {b : FrameId} {m m' : Machine} (h : StepInv b m) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value)
    (hstep : Interp.reflectAttr m recv mname args blk = some (.next m')) : Step b m m' := by
  rw [Interp.reflectAttr.eq_def] at hstep
  repeat (any_goals (first
    | (simp only [Option.some.injEq] at hstep)
    | (cases hstep
       refine Step.withCtl' ?_ _
       refine Step.allocArr' ?_ _
       exact Step.defineAttr h _ _ _)
    | (simp at hstep)
    | (split at hstep)))



/-! ## Stage 4, the half that writes the method graph or pushes a frame -/

/-- `Interp.procClosure?` (the machine-level reader) in `Denote`'s heap-level currency. -/
theorem procClosure_of_interp {m : Machine} {v : Value} {cl : Closure}
    (hc : Interp.procClosure? m v = some cl) : ∃ o, procClosure? m.heap (.ref o) = some cl := by
  rw [Interp.procClosure?.eq_def] at hc
  cases v
  case ref o => exact ⟨o, hc⟩
  all_goals exact absurd hc (by simp)

/-- …and the block's. -/
theorem procClosure_of_blockClosure {m : Machine} {blk : Option Value} {cl : Closure}
    (hc : Interp.blockClosure? m blk = some cl) :
    ∃ o, procClosure? m.heap (.ref o) = some cl := by
  rw [Interp.blockClosure?.eq_def] at hc
  cases blk with
  | none => exact absurd hc (by simp)
  | some v => exact procClosure_of_interp (by simpa using hc)

/-- `callClosure` off a `PreAct`, with the closure fact read at the **entry** machine — which is
where `blockClosure?` reads it, one eigenclass realisation before the call. -/
theorem Step.callClosure_pre {b : FrameId} {m mid m' : Machine} {cl : Closure}
    {args : List Value} {brk : Option FrameId} {selfOv : Option Value} {defmodOv : Option ObjId}
    (hstep : Interp.callClosure mid cl args brk selfOv defmodOv = .next m')
    (p : PreAct b m mid) (hex : ∃ o, procClosure? m.heap (.ref o) = some cl) : Step b m m' := by
  obtain ⟨o, hcl⟩ := hex
  exact p.1.trans (Step.callClosure p.1.2 (p.2.2 o cl hcl) args brk selfOv defmodOv hstep)

/-- **`define_method`/`define_singleton_method`** — installs a method whose body is a *closure*,
so the edge `CapMono.defineMethod` asks about is the Proc's own, read across the eigenclass
realisation `dmTargetM` performs first (`PreAct.eigenclassOf`). J33's capture erasure installs
`none` for a `localFreeB` body, which is the other disjunct. -/
theorem CapMono.defineMethod_clos {h : Heap} {cls : ObjId} {n : String} {md : MethodDef}
    {o : ObjId} {cl : Closure} (hcl : procClosure? h (.ref o) = some cl)
    (hcf : md.capturedFrame = none ∨ md.capturedFrame = cl.captured) :
    CapMono h (RubyCore.defineMethod h cls n md) := by
  refine CapMono.defineMethod (fun p hp => ?_)
  rcases hcf with he | he
  · exact absurd (he ▸ hp) (by simp)
  · exact ⟨o, capAt_of_procClosure hcl (he ▸ hp)⟩

/-- **`alias_method`** and the visibility walk both install a *copy* of a method already in the
heap, so the copy's edge is the original's and it is readable at the original's owner. -/
theorem CapMono.defineMethod_copy {h : Heap} {cls k : ObjId} {n n0 : String}
    {md md0 : MethodDef} (hmd : methodIn h k n0 = some md0)
    (hcf : md.capturedFrame = md0.capturedFrame) :
    CapMono h (RubyCore.defineMethod h cls n md) :=
  CapMono.defineMethod (fun p hp => ⟨k, capAt_of_methodIn hmd (hcf ▸ hp)⟩)

/-- **`catch`** — marks the stack with a `catchK` and calls the block; a tagless `catch`
allocates the tag object first, which is why the closure fact travels on `PreAct`. -/
theorem Step.reflectCatch {b : FrameId} {m m' : Machine} (h : StepInv b m) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value)
    (hstep : Interp.reflectCatch m recv mname args blk = some (.next m')) : Step b m m' := by
  rw [Interp.reflectCatch.eq_def] at hstep
  repeat (any_goals (first
    | (simp only [Option.some.injEq] at hstep)
    | (refine Step.callClosure_pre hstep ?_ (procClosure_of_blockClosure (by assumption))
       refine PreAct.heapKeep (PreAct.refl h) rfl rfl ?_ ?_
       · exact MCap.of_eq rfl
       · exact PayKeep.refl _)
    | (refine Step.callClosure_pre hstep ?_ (procClosure_of_blockClosure (by assumption))
       refine PreAct.heapKeep (PreAct.refl h) rfl rfl ?_ ?_
       · exact MCap.push_eq rfl (fun _ hc => hc)
       · exact PayKeep.alloc _ _)
    | (simp at hstep)
    | (split at hstep)))

/-- **`class_eval`/`instance_eval`/`*_exec`** — calls the block with `self` (and the `def`
target) rebound; the `instance_*` forms realise the eigenclass first. -/
theorem Step.reflectEval {b : FrameId} {m m' : Machine} (h : StepInv b m) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value)
    (hstep : Interp.reflectEval m recv mname args blk = some (.next m')) : Step b m m' := by
  rw [Interp.reflectEval.eq_def] at hstep
  repeat (any_goals (first
    | (simp only [Option.some.injEq] at hstep)
    | (exact Step.callClosure_pre hstep (PreAct.refl h)
        (procClosure_of_blockClosure (by assumption)))
    | (exact Step.callClosure_pre hstep ((PreAct.refl h).eigenclassOf _)
        (procClosure_of_blockClosure (by assumption)))
    | (obtain ⟨-, hst⟩ := hstep
       exact Step.callClosure_pre hst (PreAct.refl h)
         (procClosure_of_blockClosure (by assumption)))
    | (obtain ⟨-, hst⟩ := hstep
       exact Step.callClosure_pre hst ((PreAct.refl h).eigenclassOf _)
         (procClosure_of_blockClosure (by assumption)))
    | (simp at hstep)
    | (split at hstep)))



set_option hygiene false in
/-- The closer list for `reflectDefineMethod`'s two body-source branches. -/
macro "step_dm" h:ident hs:ident : tactic => `(tactic|
  (repeat (any_goals (first
    | (simp only [Option.some.injEq] at $hs:ident)
    | (cases $hs:ident
       refine Step.withCtl' ?_ _
       refine Step.heap' (PreAct.dmTargetM (PreAct.refl $h) _ _).1 rfl rfl ?_
       exact CapMono.defineMethod_clos
         ((PreAct.dmTargetM (PreAct.refl $h) _ _).2.2 _ _
           (Exists.choose_spec (procClosure_of_interp (by assumption))))
         (by first | exact Or.inl rfl | exact Or.inr rfl))
    | (simp at $hs:ident)
    | (split at $hs:ident)))))

/-- **`dmTargetM`** at `PreAct` — `define_singleton_method` on a plain object realises the
eigenclass, everything else leaves the machine alone. -/
theorem PreAct.dmTargetM {b : FrameId} {m mid : Machine} (p : PreAct b m mid) (recv : Value)
    (singleton : Bool) : PreAct b m (Interp.dmTargetM mid recv singleton) := by
  unfold Interp.dmTargetM
  repeat (any_goals (first
    | exact p.eigenclassOf _
    | exact p
    | split))

/-- **`define_method`/`define_singleton_method`** — the eigenclass realisation (`dmTargetM`)
carries the Proc fact on `PreAct`, and the installed method's edge is that Proc's own (or `none`,
by J33's capture erasure).

The body's *source* — the block, or a Proc passed as the second argument — is peeled by hand,
because the closure fact has to come out of that match as a bare `Interp.procClosure?`: a
hand-written `match` in a lemma's premise is a **fresh matcher constant** and would not unify
with the model's (the nineteenth stall point, in the small). -/
theorem Step.reflectDefineMethod {b : FrameId} {m m' : Machine} (h : StepInv b m) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value)
    (hstep : Interp.reflectDefineMethod m recv mname args blk = some (.next m')) :
    Step b m m' := by
  rw [Interp.reflectDefineMethod.eq_def] at hstep
  cases args with
  | nil => simp at hstep
  | cons nameArg rest =>
    dsimp only at hstep
    cases blk with
    | some bv =>
      dsimp only at hstep
      step_dm h hstep
    | none =>
      dsimp only at hstep
      cases rest with
      | nil => split at hstep <;> simp at hstep
      | cons pv t =>
        cases t with
        | nil => step_dm h hstep
        | cons _ _ => split at hstep <;> simp at hstep

/-- **`alias_method`** — installs a *copy* of a method already in the heap, so the copy's edge is
the original's and readable at the original's owner. -/
theorem Step.reflectAliasMethod {b : FrameId} {m m' : Machine} (h : StepInv b m) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value)
    (hstep : Interp.reflectAliasMethod m recv mname args blk = some (.next m')) :
    Step b m m' := by
  rw [Interp.reflectAliasMethod.eq_def] at hstep
  repeat (any_goals (first
    | (simp only [Option.some.injEq] at hstep)
    | (cases hstep
       refine Step.withCtl' ?_ _
       exact Step.heap h rfl rfl (CapMono.defineMethod_copy
         (methodIn_of_methodOn (by assumption)) (by first | rfl | (split <;> rfl))))
    | (simp at hstep)
    | (split at hstep)))



/-! ## The two `Option Machine` walks

`visNames` and `removeNames` fold over `Option Machine` with `bind`, and their callers read
`isSome` and `getD` separately (the model's own `visOk`/`visRun` split, made for the
continuation-framing proof). So the layer needs one fold lemma in that shape, and two heap
lemmas: removing a name from a method table (`setClassPayload_filter`) and installing a copy
(`defineMethod_copy`, above). -/

/-- Filtering a name out of a table leaves **no** entry for it. -/
theorem find?_filter_self {n : String} :
    ∀ (l : List (String × MethodDef)),
      (l.filter (·.1 != n)).find? (·.1 == n) = none
  | [] => rfl
  | a :: rest => by
    by_cases hk : a.1 = n
    · rw [List.filter_cons, show (a.1 != n) = false from by simp [hk], if_neg (by simp)]
      exact find?_filter_self rest
    · rw [List.filter_cons, show (a.1 != n) = true from by simp [hk], if_pos (by simp),
        List.find?_cons, show (a.1 == n) = false from by simp [hk]]
      exact find?_filter_self rest

/-- **Removing a name** from a class's method table carries no new capture edge: the removed
name resolves to nothing, and every other name resolves exactly as it did. -/
theorem CapMono.setClassPayload_filter {h : Heap} {o : ObjId} {c : ClassPayload} {n : String}
    (hc : h.classPayload? o = some c) :
    CapMono h (h.setClassPayload o { c with methods := c.methods.filter (·.1 != n) }) := by
  refine CapMono.set_gen (fun p hcap => ?_)
  have hpl : (h.get o).payload = .cls c := by
    simp only [Heap.classPayload?] at hc
    cases hp : (h.get o).payload with
    | cls c' => rw [hp] at hc; exact congrArg Payload.cls (Option.some.inj hc)
    | _ => rw [hp] at hc; exact absurd hc (by simp)
  simp only [CapAt] at hcap
  obtain ⟨n', md', hmd, hcf⟩ := hcap
  by_cases hne : n' = n
  · subst hne
    simp only [methodOf, find?_filter_self] at hmd
    exact absurd hmd (by simp)
  · refine ⟨o, ?_⟩
    simp only [CapAt, hpl]
    refine ⟨n', md', ?_, hcf⟩
    simp only [methodOf] at hmd ⊢
    rw [← find?_filter_ne hne]
    exact hmd

/-- The fold over `Option Machine` with `bind`, at `PreAct`. -/
theorem PreAct.foldOpt {b : FrameId} {α : Type} (f : Machine → α → Option Machine)
    (hf : ∀ (m₀ m₁ : Machine) (a : α), StepInv b m₀ → f m₀ a = some m₁ → PreAct b m₀ m₁) :
    ∀ (l : List α) (m₀ m₁ : Machine), StepInv b m₀ →
      l.foldl (fun acc a => Option.bind acc (fun mm => f mm a)) (some m₀) = some m₁ →
      PreAct b m₀ m₁
  | [], m₀, m₁, h, he => by
    rw [List.foldl_nil] at he
    rw [← Option.some.inj he]
    exact PreAct.refl h
  | a :: rest, m₀, m₁, h, he => by
    rw [List.foldl_cons] at he
    cases hfa : f m₀ a with
    | none =>
      rw [Option.bind_some, hfa] at he
      rw [show ∀ (l : List α), l.foldl (fun acc x => Option.bind acc (fun mm => f mm x))
          none = none from by
        intro l
        induction l with
        | nil => rfl
        | cons x t ih => rw [List.foldl_cons, Option.bind_none]; exact ih] at he
      exact absurd he (by simp)
    | some m₂ =>
      rw [Option.bind_some, hfa] at he
      exact (hf m₀ m₂ a h hfa).trans (PreAct.foldOpt f hf rest m₂ m₁ (hf m₀ m₂ a h hfa).1.2 he)



/-! ### The visibility and removal walks are **`Step`**, not `PreAct` — and that is a fact

`PreAct`'s method conjunct says *every installed method is still installed*, and
`defineMethod` **replaces**: a re-definition of the same name drops the old entry. So `PreAct` is
**false** across `visNames`/`removeNames`, and the type checker says so (it refused
`PayKeep.set_payload` for a `defineMethod`, which writes a class *payload*). Nothing downstream
wants it either — `reflectVisibility` allocates an array and writes `ctl` after the walk, which
is `Step`.

What the walk's *second* write needs is not the old fact transported but the **new** one
established: `methodIn_defineMethod` (a method just installed is installed), moved across the
eigenclass realisation by `PayKeep` (which `eigenclassOf` does satisfy — it allocates and writes
`eigen`, never a payload). -/

/-- Reading back a payload just written. -/
theorem classPayload_setClassPayload {h : Heap} {o : ObjId} {cp : ClassPayload}
    (hlt : o < h.objs.size) : (h.setClassPayload o cp).classPayload? o = some cp := by
  unfold Heap.setClassPayload Heap.classPayload?
  rw [show Heap.get (h.set o { h.get o with payload := .cls cp }) o
      = { h.get o with payload := .cls cp } from getD_set!_self h.objs o _ hlt]

/-- A class the heap has is in range. -/
theorem classPayload_lt {h : Heap} {o : ObjId} {c : ClassPayload}
    (hc : h.classPayload? o = some c) : o < h.objs.size := by
  rcases Nat.lt_or_ge o h.objs.size with hlt | hge
  · exact hlt
  · rw [Heap.classPayload?, heap_get_oob hge,
      show (default : Object).payload = Payload.none from rfl] at hc
    exact absurd hc (by simp)

/-- **A method just installed is installed** — what the second write of the `module_function`
walk needs, in place of transporting the first write's replaced entry. -/
theorem methodIn_defineMethod {h : Heap} {cls : ObjId} {n : String} {md : MethodDef}
    {c : ClassPayload} (hc : h.classPayload? cls = some c) :
    methodIn (RubyCore.defineMethod h cls n md) cls n = some md := by
  unfold RubyCore.defineMethod
  rw [hc]
  dsimp only
  rw [methodIn_eq_methodOf (classPayload_setClassPayload (classPayload_lt hc)) n]
  simp only [methodOf, List.find?_cons, beq_self_eq_true, Option.map_some]

/-- `methodIn` survives any heap change that kept the payloads. -/
theorem methodIn_payKeep {h h' : Heap} (hk : PayKeep h h') {k : ObjId} {n : String}
    {md : MethodDef} (hm : methodIn h k n = some md) : methodIn h' k n = some md := by
  rw [methodIn, Heap.classPayload?, hk.2 k (methodIn_lt hm), ← Heap.classPayload?, ← methodIn]
  exact hm

/-- **`eigenclassOf` keeps every payload** — it allocates and writes `eigen` fields. -/
theorem PayKeep.eigenclassOf_go :
    ∀ (fuel : Nat) (mid : Machine) (o : ObjId),
      PayKeep mid.heap (Interp.eigenclassOf.go mid o fuel).2.heap
  | 0, mid, o => PayKeep.refl _
  | fuel + 1, mid, o => by
    rw [Interp.eigenclassOf.go]
    split
    · exact PayKeep.refl _
    · have hgo : ∀ (m₂ : Machine) (o₂ : ObjId),
          PayKeep m₂.heap (match (m₂.heap.get o₂).payload with
            | .cls c => match c.superclass with
              | some s => Interp.eigenclassOf.go m₂ s fuel
              | none => ((if c.isModule then Boot.moduleId else Boot.classId), m₂)
            | _ => ((m₂.heap.get o₂).klass, m₂)).2.heap := by
        intro m₂ o₂
        split
        · split
          · exact PayKeep.eigenclassOf_go fuel m₂ _
          · exact PayKeep.refl _
        · exact PayKeep.refl _
      exact (hgo mid o).trans ((PayKeep.alloc _ _).trans (PayKeep.set_payload rfl))

theorem PayKeep.eigenclassOf (mid : Machine) (o : ObjId) :
    PayKeep mid.heap (Interp.eigenclassOf mid o).2.heap := by
  rw [Interp.eigenclassOf]
  exact PayKeep.eigenclassOf_go _ mid o

/-- The fold over `Option Machine` with `bind`, at `Step`. -/
theorem Step.foldOpt {b : FrameId} {α : Type} (f : Machine → α → Option Machine)
    (hf : ∀ (m₀ m₁ : Machine) (a : α), StepInv b m₀ → f m₀ a = some m₁ → Step b m₀ m₁) :
    ∀ (l : List α) (m₀ m₁ : Machine), StepInv b m₀ →
      l.foldl (fun acc a => Option.bind acc (fun mm => f mm a)) (some m₀) = some m₁ →
      Step b m₀ m₁
  | [], m₀, m₁, h, he => by
    rw [List.foldl_nil] at he
    rw [← Option.some.inj he]
    exact Step.refl h
  | a :: rest, m₀, m₁, h, he => by
    rw [List.foldl_cons] at he
    cases hfa : f m₀ a with
    | none =>
      rw [Option.bind_some, hfa] at he
      rw [show ∀ (l : List α), l.foldl (fun acc x => Option.bind acc (fun mm => f mm x))
          none = none from by
        intro l
        induction l with
        | nil => rfl
        | cons x t ih => rw [List.foldl_cons, Option.bind_none]; exact ih] at he
      exact absurd he (by simp)
    | some m₂ =>
      rw [Option.bind_some, hfa] at he
      exact (hf m₀ m₂ a h hfa).trans (Step.foldOpt f hf rest m₂ m₁ (hf m₀ m₂ a h hfa).2 he)



/-- **The `visNames` step**, peeled by hand: `split` cannot see its `let`-bound machine, so the
conditions (the `methodOn` lookup, the unmodeled-builtin gate, `module_function`) are peeled and
each leaf is one `exact`.

The `module_function` leaf is the interesting one: its second write installs a copy at the
**eigenclass**, and the edge that copy carries is the one the *first* write just put at `target`
(`methodIn_defineMethod`, moved across the eigenclass realisation by `PayKeep`) — or, when
`target` is not a class and the first write was the identity, the original's, still where
`methodOn` found it. Both cases, because `defineMethod` on a payload-less object is `h`. -/
theorem Step.visStep {b : FrameId} {m₀ m₁ : Machine} (h₀ : StepInv b m₀) (o target : ObjId)
    (vis : Visibility) (modFun : Bool) (n : String)
    (hfa : (match Interp.methodOn m₀.heap target n with
      | some (_, md) =>
        if md.builtin.isSome && !md.fromPrelude then none
        else
          let m := { m₀ with heap := RubyCore.defineMethod m₀.heap target n { md with visibility := vis } }
          if modFun then
            let em := Interp.eigenclassOf m o
            some { em.2 with heap := RubyCore.defineMethod em.2.heap em.1 n { md with visibility := .pub, owner := em.1 } }
          else some m
      | none => none) = some m₁) : Step b m₀ m₁ := by
  cases hmo : Interp.methodOn m₀.heap target n with
  | none => rw [hmo] at hfa; exact absurd hfa (by simp)
  | some p =>
    rw [hmo] at hfa
    dsimp only at hfa
    by_cases hb : (p.2.builtin.isSome && !p.2.fromPrelude) = true
    · rw [if_pos hb] at hfa; exact absurd hfa (by simp)
    · rw [if_neg hb] at hfa
      have hmi : methodIn m₀.heap p.1 n = some p.2 := methodIn_of_methodOn hmo
      have s1 : Step b m₀ { m₀ with heap := RubyCore.defineMethod m₀.heap target n { p.2 with visibility := vis } } :=
        Step.heap h₀ rfl rfl (CapMono.defineMethod_copy hmi rfl)
      by_cases hmf : modFun = true
      · rw [if_pos hmf] at hfa
        cases hfa
        refine Step.heap' (Step.eigenclassOf' s1 o) rfl rfl ?_
        cases hcx : m₀.heap.classPayload? target with
        | some c =>
          exact CapMono.defineMethod_copy (k := target) (n0 := n)
            (methodIn_payKeep (PayKeep.eigenclassOf _ o) (methodIn_defineMethod hcx)) rfl
        | none =>
          -- the first write was the identity, so the original is still where `methodOn` found it
          have hkeep : methodIn (RubyCore.defineMethod m₀.heap target n
              { p.2 with visibility := vis }) p.1 n = some p.2 := by
            rw [RubyCore.defineMethod, hcx]
            exact hmi
          exact CapMono.defineMethod_copy (k := p.1) (n0 := n)
            (methodIn_payKeep (PayKeep.eigenclassOf _ o) hkeep) rfl
      · rw [if_neg hmf] at hfa
        cases hfa
        exact s1

/-- **`visNames`** — the walk, folded. -/
theorem Step.visNames {b : FrameId} {m : Machine} (h : StepInv b m) (o target : ObjId)
    (vis : Visibility) (modFun : Bool) (names : List String) :
    ∀ m₂, Interp.visNames m o target vis modFun names = some m₂ → Step b m m₂ := by
  intro m₂ he
  rw [Interp.visNames] at he
  exact Step.foldOpt _ (fun m₀ m₁ n h₀ hfa => Step.visStep h₀ o target vis modFun n hfa)
    names m m₂ h he

/-- …and `visRun`, which is the walk's machine or the original one. -/
theorem Step.visRun {b : FrameId} {m : Machine} (h : StepInv b m) (o target : ObjId)
    (vis : Visibility) (modFun : Bool) (names : List String) :
    Step b m (Interp.visRun m o target vis modFun names) := by
  unfold Interp.visRun
  cases hv : Interp.visNames m o target vis modFun names with
  | none => exact Step.refl h
  | some m₂ => exact Step.visNames h o target vis modFun names m₂ hv



/-- **`setCurrentFrame`** — the interpreter's third frame writer (`private` in a class body sets
the frame's default visibility). `LocalsSame.setCurrentFrame` is the frame half; the heap is
untouched, so the seal travels by `of_localsSame`. -/
theorem setCurrentFrame_heap (m : Machine) (fr : RubyCore.Frame) :
    (m.setCurrentFrame fr).heap = m.heap := by
  unfold Machine.setCurrentFrame
  cases m.stack with
  | nil => rfl
  | cons fid rest => rfl

theorem Step.setCurrentFrame {b : FrameId} {m : Machine} (h : StepInv b m) (fr : RubyCore.Frame)
    (hl : fr.locals = m.currentFrame.locals) (hc : fr.captured = m.currentFrame.captured) :
    Step b m (m.setCurrentFrame fr) :=
  have hls := LocalsSame.setCurrentFrame hl hc
  ⟨hls.off,
   { sealed := h.sealed.of_localsSame hls
       (fun o cl hcl => h.sealed.clos o cl (by rw [setCurrentFrame_heap] at hcl; exact hcl))
       (fun k n md hmd => h.sealed.meth k n md
         (by rw [setCurrentFrame_heap] at hmd; exact hmd))
     wf := h.wf.of_localsSame hls
       (fun o cl hcl => h.wf.clos o cl (by rw [setCurrentFrame_heap] at hcl; exact hcl))
       (fun k n md hmd => h.wf.meth k n md
         (by rw [setCurrentFrame_heap] at hmd; exact hmd))
     inRange := by rw [hls.2.2.2]; exact h.inRange }⟩

/-- **The `removeNames` step** — `undef_method` installs a tombstone (a fresh `MethodDef`, so
capture-free); `remove_method` filters the name out, which can only *hide* an edge. -/
theorem Step.removeStep {b : FrameId} {m₀ m₁ : Machine} (h₀ : StepInv b m₀) (o : ObjId)
    (undef : Bool) (n : String)
    (hfa : (match m₀.heap.classPayload? o with
      | some c =>
        if undef then some { m₀ with heap := RubyCore.undefMethod m₀.heap o n }
        else match c.methods.find? (·.1 == n) with
          | some (_, md) =>
            if md.undefined then none
            else some { m₀ with heap := m₀.heap.setClassPayload o { c with methods := c.methods.filter (·.1 != n) } }
          | none => none
      | none => none) = some m₁) : Step b m₀ m₁ := by
  cases hcx : m₀.heap.classPayload? o with
  | none => rw [hcx] at hfa; exact absurd hfa (by simp)
  | some c =>
    rw [hcx] at hfa
    dsimp only at hfa
    by_cases hu : undef = true
    · rw [if_pos hu] at hfa
      cases hfa
      exact Step.heap h₀ rfl rfl
        (CapMono.defineMethod (fun _ hcn => absurd hcn (by simp)))
    · rw [if_neg hu] at hfa
      cases hfd : c.methods.find? (·.1 == n) with
      | none => rw [hfd] at hfa; exact absurd hfa (by simp)
      | some q =>
        rw [hfd] at hfa
        dsimp only at hfa
        by_cases hun : q.2.undefined = true
        · rw [if_pos hun] at hfa; exact absurd hfa (by simp)
        · rw [if_neg hun] at hfa
          cases hfa
          exact Step.heap h₀ rfl rfl (CapMono.setClassPayload_filter hcx)

/-- **`removeNames`** and its `removeRun`. -/
theorem Step.removeNames {b : FrameId} {m : Machine} (h : StepInv b m) (o : ObjId)
    (undef : Bool) (names : List String) :
    ∀ m₂, Interp.removeNames m o undef names = some m₂ → Step b m m₂ := by
  intro m₂ he
  rw [Interp.removeNames] at he
  exact Step.foldOpt _ (fun m₀ m₁ n h₀ hfa => Step.removeStep h₀ o undef n hfa) names m m₂ h he

theorem Step.removeRun {b : FrameId} {m : Machine} (h : StepInv b m) (o : ObjId)
    (undef : Bool) (names : List String) : Step b m (Interp.removeRun m o undef names) := by
  unfold Interp.removeRun
  cases hv : Interp.removeNames m o undef names with
  | none => exact Step.refl h
  | some m₂ => exact Step.removeNames h o undef names m₂ hv

/-! ### `reflectVisibility`, and the measurement that closed it

Parked for one attempt on the diagnosis "its four leaves need hand peels", which was right and
insufficient: with the leaves peeled the walk still **timed out at 1M heartbeats (28 s)**, and the
cause is clink 62's rule arriving for the fifth time — a closer whose *conclusion* carries the
shape (`Step b m (visRun (eigenclassOf m ?o).2 …)`) is expensive **to fail**, because unification
must unfold the callee against a machine-sized term at every goal it does not close.
`Step.visRun_eq`/`visRunEigen_eq` move the shape into a `rfl` hypothesis and the same walk closes
in **2.3 s**. -/

/-- `visRun` in `_eq` form: the shape in a `rfl` hypothesis, the conclusion first-order — clink
62's rule, which this leaf needed because the goal-keyed form is expensive **to fail** (a
`Step b m (visRun (eigenclassOf m ?o).2 …)` conclusion forces `whnf` against a machine-sized term
at every goal it does not close, and the walk timed out at 1M heartbeats). -/
theorem Step.visRun_eq {b : FrameId} {m m' : Machine} (h : StepInv b m) {o target : ObjId}
    {vis : Visibility} {modFun : Bool} {names : List String}
    (he : m' = Interp.visRun m o target vis modFun names) : Step b m m' :=
  he ▸ Step.visRun h o target vis modFun names

/-- …and the same after an eigenclass realisation, which is the `*_class_method` shape. -/
theorem Step.visRunEigen_eq {b : FrameId} {m m' : Machine} (h : StepInv b m) {o o₂ target : ObjId}
    {vis : Visibility} {modFun : Bool} {names : List String}
    (he : m' = Interp.visRun (Interp.eigenclassOf m o).2 o₂ target vis modFun names) :
    Step b m m' :=
  he ▸ (Step.eigenclassOf m o h).trans
    (Step.visRun (Step.eigenclassOf m o h).2 o₂ target vis modFun names)

set_option maxHeartbeats 1000000 in
theorem Step.reflectVisibility {b : FrameId} {m m' : Machine} (h : StepInv b m) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value)
    (hstep : Interp.reflectVisibility m recv mname args blk = some (.next m')) : Step b m m' := by
  rw [Interp.reflectVisibility.eq_def] at hstep
  cases recv
  case ref o0 =>
    dsimp only at hstep
    by_cases hl : ((args.filterMap (Interp.symOrStr m)).length != args.length) = true
    · rw [if_pos hl] at hstep; exact absurd hstep (by simp)
    · rw [if_neg hl] at hstep
      by_cases he : (args.filterMap (Interp.symOrStr m)).isEmpty = true
      · rw [if_pos he] at hstep
        by_cases hc1 : (mname == "private_class_method" || mname == "public_class_method") = true
        · rw [if_pos hc1] at hstep; exact absurd hstep (by simp)
        · rw [if_neg hc1] at hstep
          by_cases hc2 : (mname == "module_function") = true
          · rw [if_pos hc2] at hstep; exact absurd hstep (by simp)
          · rw [if_neg hc2] at hstep
            simp only [Option.some.injEq, StepResult.next.injEq] at hstep
            cases hstep
            refine Step.withCtl' ?_ _
            exact Step.setCurrentFrame h _ rfl rfl
      · rw [if_neg he] at hstep
        repeat (any_goals (first
          | (cases hstep
             refine Step.withCtl' ?_ _
             refine Step.allocArr' ?_ _
             exact Step.visRunEigen_eq h rfl)
          | (cases hstep
             refine Step.withCtl' ?_ _
             refine Step.allocArr' ?_ _
             exact Step.visRun_eq h rfl)
          | (cases hstep)
          | (split at hstep)))
  all_goals exact absurd hstep (by simp)

/-- **`remove_method`/`undef_method`**. -/
theorem Step.reflectRemoveMethod {b : FrameId} {m m' : Machine} (h : StepInv b m) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value)
    (hstep : Interp.reflectRemoveMethod m recv mname args blk = some (.next m')) :
    Step b m m' := by
  rw [Interp.reflectRemoveMethod.eq_def] at hstep
  repeat (any_goals (first
    | (simp only [Option.some.injEq] at hstep)
    | (cases hstep; exact Step.withCtl' (Step.removeRun h _ _ _) _)
    | (cases hstep; exact Step.raiseErr h _ _)
    | (obtain ⟨-, hst⟩ := hstep
       cases hst
       exact Step.withCtl' (Step.removeRun h _ _ _) _)
    | (obtain ⟨-, hst⟩ := hstep
       cases hst
       exact Step.raiseErr h _ _)
    | (simp at hstep)
    | (split at hstep)))

/-- **`tryReflect`** — the reflection dispatcher: a match on the method name over the fifteen
helpers above, so one closer each and no work of its own. -/
theorem Step.tryReflect {b : FrameId} {m m' : Machine} (h : StepInv b m) (recv : Value)
    (mname : String) (args : List Value) (blk : Option Value)
    (hstep : Interp.tryReflect m recv mname args blk = some (.next m')) : Step b m m' := by
  rw [Interp.tryReflect.eq_def] at hstep
  repeat (any_goals (first
    | exact Step.reflectDefineMethod h recv _ args blk hstep
    | exact Step.reflectEval h recv _ args blk hstep
    | exact Step.reflectCatch h recv _ args blk hstep
    | exact Step.reflectThrow h recv _ args blk hstep
    | exact Step.reflectVisibility h recv _ args blk hstep
    | exact Step.reflectSingletonClass h recv _ args blk hstep
    | exact Step.reflectIvarGet h recv _ args blk hstep
    | exact Step.reflectIvarSet h recv _ args blk hstep
    | exact Step.reflectIvarNames h recv _ args blk hstep
    | exact Step.reflectConstGet h recv _ args blk hstep
    | exact Step.reflectConstSet h recv _ args blk hstep
    | exact Step.reflectRemoveMethod h recv _ args blk hstep
    | exact Step.reflectAliasMethod h recv _ args blk hstep
    | exact Step.reflectAttr h recv _ args blk hstep
    | exact Step.reflectMethodDefined h recv _ args blk hstep
    | exact Step.reflectRespondTo h recv _ args blk hstep
    | (cases hstep)
    | (split at hstep)))



set_option maxHeartbeats 1000000 in
/-- **`dispatchMiss`** — the lookup-miss path: the native iterators, the mixin hooks, the
reflection dispatcher, three CRuby-shadow gates, then a user `method_missing` (whose `MethodDef`
comes from `methodOn`, so the bridge applies) or the byte-exact `NoMethodError`.

**This closes the miss path**, which is what `invokeDispatch` waits on. -/
theorem Step.dispatchMiss {b : FrameId} {m m' : Machine} (h : StepInv b m) (recv : Value)
    (site : SendSite) (mname : String) (args : List Value) (blk : Option Value)
    (hstep : Interp.dispatchMiss m recv site mname args blk = .next m') : Step b m m' := by
  rw [Interp.dispatchMiss.eq_def] at hstep
  repeat (any_goals (first
    | exact Step.tryIterator h recv _ args blk (by rw [← hstep]; assumption)
    | exact Step.tryMixin h recv _ args (by rw [← hstep]; assumption)
    | exact Step.tryReflect h recv _ args blk (by rw [← hstep]; assumption)
    | exact Step.missNoMethod h recv site _ args hstep
    | (exact Step.enterUserMethod h recv _ (methodIn_of_methodOn (by assumption)) _ _ _ hstep)
    | (cases hstep)
    -- `dispatchMiss`'s gates sit under a `have chain := …`, which `split` cannot see through
    -- (failure mode 1); zeta-reducing it is what puts the match in reach
    | (dsimp only at hstep)
    | (split at hstep)))

#print axioms capAt_of_methodIn
#print axioms capAt_of_procClosure
#print axioms CapMono.of_constSetIn
#print axioms PayKeep.set_payload
#print axioms PreAct.eigenclassOf
#print axioms PayKeep.eigenclassOf
#print axioms methodIn_defineMethod
#print axioms methodIn_payKeep
#print axioms Step.foldOpt
#print axioms Step.setCurrentFrame
#print axioms find?_filter_self
#print axioms CapMono.setClassPayload_filter
#print axioms CapMono.defineMethod_clos
#print axioms CapMono.defineMethod_copy
#print axioms procClosure_of_blockClosure
#print axioms Step.reflectIvarGet
#print axioms Step.reflectIvarSet
#print axioms Step.reflectIvarNames
#print axioms Step.reflectConstGet
#print axioms Step.reflectConstSet
#print axioms Step.reflectMethodDefined
#print axioms Step.reflectRespondTo
#print axioms Step.reflectSingletonClass
#print axioms Step.reflectThrow
#print axioms Step.reflectAttr
#print axioms Step.reflectCatch
#print axioms Step.reflectEval
#print axioms Step.reflectDefineMethod
#print axioms Step.reflectAliasMethod
#print axioms Step.visStep
#print axioms Step.visRun
#print axioms Step.removeStep
#print axioms Step.removeRun
#print axioms Step.reflectRemoveMethod
#print axioms Step.visRun_eq
#print axioms Step.reflectVisibility
#print axioms Step.tryReflect
#print axioms Step.dispatchMiss

end Ratchet.Denote
