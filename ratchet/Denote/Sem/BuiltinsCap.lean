import Denote.Sem.StepLocal

/-!
# `Denote/Sem/BuiltinsCap.lean` — the `Builtins` layer's **heap** half

`Denote/Sem/FrameLocal.lean` walked the six hundred arms of `Builtins.run` for `LocalsSame` —
the *frame*-side congruence of `Sealed`/`FramesWF` — and `Denote/Sem/StepLocal.lean`'s
`builtins_run_seal`/`builtins_run_framesWF` reduced the seal across that layer to exactly two
remaining hypotheses (`notes.md` §The `Builtins` layer, half proved):

```
∀ o cl, procClosure? m'.heap (.ref o) = some cl → ∀ p, cl.captured = some p → <p is sealed>
∀ k n md, methodIn m'.heap k n = some md → ∀ p, md.capturedFrame = some p → <p is sealed>
```

i.e. **`Builtins.run` installs no capturing closure and no capturing method**. This file is
that second traversal, and the notes' price is the right one: it does not ride the first walk,
because nearly every arm discharges `LocalsSame` by `of_eq rfl rfl` — *frames* unchanged —
while the heap is exactly what those arms change.

## The predicate, and why it is not "the heap did not change"

`CapMono h h'` says the heap's **capture edges did not grow**: every capture edge readable at
`h'` was already readable at the same object id in `h`. That is what the two hypotheses above
need and all they need, and it is the weakest claim with the two properties the walk lives on:

* **reflexive and transitive**, so an arm that chains three helpers chains three lemmas; and
* **discharged by the payload alone** for an allocation. A pushed `.str`/`.arr`/`.hsh`/`.exc`
  object carries no capture edge *by its constructor*, so `CapMono.push` closes with a `simp`
  on `CapAt` rather than with an argument about heaps.

**The edge is not keyed to the object id, and one builtin is why.** The first version said
"every edge readable at `h'` was readable *at the same id* in `h`", and `Object#dup` refutes
it: `dupObj` pushes a fresh object with the *source's* payload, so `p.dup` on a Proc puts the
same capture edge at a new id. The seal does not care — `Sealed.clos` at the source discharges
it — so the honest claim is existential in the id, which is also what `Sealed`'s clauses
consume (they are quantified over ids). Measured, not predicted: `CapMono.push` would not
close for `dupObj`.

`CapAt` is keyed on `methodOf` — the **first** entry of the name, which is what `methodIn`
reads — rather than on membership in `cp.methods`. That is not a detail: `Sealed.meth`
constrains the first match per name, so a membership-shaped `CapAt` would be a claim this
file could establish and `Sealed` could not consume. Same lesson as the tenth stall point
(*state the component over the lookup function*), arriving one layer down.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Ratchet.Denote

open RubyCore

/-- The method a class payload binds to `n`: the **first** entry, which is what `methodIn`
reads. -/
def methodOf (cp : ClassPayload) (n : String) : Option MethodDef :=
  (cp.methods.find? (·.1 == n)).map (·.2)

theorem methodIn_eq_methodOf {h : Heap} {k : ObjId} {cp : ClassPayload}
    (hc : h.classPayload? k = some cp) (n : String) :
    methodIn h k n = methodOf cp n := by
  simp only [methodIn, hc, Option.bind_some, methodOf]

/-- **Object `obj` carries a capture edge into frame `p`** — either it *is* a Proc that
captured `p`, or it is a class one of whose installed methods did. The two are exactly the two
things `Sealed` reads out of the heap. -/
def CapAt (obj : Object) (p : Nat) : Prop :=
  match obj.payload with
  | .proc cl => cl.captured = some p
  | .cls cp => ∃ n md, methodOf cp n = some md ∧ md.capturedFrame = some p
  | _ => False

/-- An object with no payload — which is what `Heap.get` answers past the end of the heap —
carries no capture edge. -/
theorem capAt_default (p : Nat) : ¬ CapAt default p := by
  intro h; exact h

/-- Two objects with the same payload carry the same capture edges. -/
theorem capAt_congr {a b : Object} (hp : a.payload = b.payload) (p : Nat) :
    CapAt a p ↔ CapAt b p := by
  simp only [CapAt, hp]

/-- **A freshly allocated class carries no capture edge**, because its method table is empty.
`newImpl`'s `Class.new` arm is the one allocation in the layer that pushes a `.cls` payload, so
this is the closer that arm needs and the reason `CapAt`'s class arm is not simply refuted by
`simp`. -/
theorem capAt_cls_nil {obj : Object} {cp : ClassPayload} (hp : obj.payload = .cls cp)
    (hm : cp.methods = []) {p : Nat} : ¬ CapAt obj p := by
  intro hcap
  simp only [CapAt, hp] at hcap
  obtain ⟨n, md, hmd, -⟩ := hcap
  simp only [methodOf, hm] at hmd
  exact absurd hmd (by simp)

/-- **`Class#allocate`'s payload is capture-free**, and it needs its own lemma because
`Builtins.emptyCorePayload sup` is a *function call*: `CapAt` cannot reduce by iota through it,
so the pure-term side conditions above are stuck. Four `if` arms, all of them `.str`/`.arr`/
`.hsh`/`.exc`, none a Proc and none a class. -/
theorem capAt_emptyCore {obj : Object} {sup : ObjId}
    (hp : obj.payload = Builtins.emptyCorePayload sup) {p : Nat} : ¬ CapAt obj p := by
  intro hcap
  have hcases : (∃ x, obj.payload = .str x) ∨ (∃ x, obj.payload = .arr x) ∨
      (∃ x, obj.payload = .hsh x) ∨ (∃ x, obj.payload = .exc x) := by
    unfold Builtins.emptyCorePayload at hp
    split at hp
    · exact Or.inl ⟨_, hp⟩
    · split at hp
      · exact Or.inr (Or.inl ⟨_, hp⟩)
      · split at hp
        · exact Or.inr (Or.inr (Or.inl ⟨_, hp⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨_, hp⟩))
  rcases hcases with ⟨_, he⟩ | ⟨_, he⟩ | ⟨_, he⟩ | ⟨_, he⟩ <;>
    simp only [CapAt, he] at hcap

/-- **`Symbol#to_proc`'s Proc carries no edge**, because its `captured` is `none` (L266).

Its own lemma rather than a closer, and that is the discipline this file had to learn twice: the
elaborator will not unfold `CapAt` to expose an `Eq` in *argument* position, so `noConfusion`
cannot see the reduced hypothesis — and rewriting it with `simp` *inside the walk* put a `simp`
on every side goal of six hundred arms, which took `runNumerics` past 14 GB of proof term. The
`simp` belongs here, elaborated once. -/
theorem capAt_proc_none {obj : Object} {cl : Closure} (hp : obj.payload = .proc cl)
    (hcn : cl.captured = none) {p : Nat} : ¬ CapAt obj p := by
  intro hcap
  simp only [CapAt, hp, hcn] at hcap
  exact absurd hcap (by simp)

/-! `cap_free` discharges a **side goal** `∀ p, ¬ CapAt obj p` at an object that is already
determined. Three cases and no search: an ordinary payload makes `CapAt` reduce to `False` by
iota, the layer's one Proc allocation (`Symbol#to_proc`, `captured := none` since L266) needs
`Option.noConfusion`, and its one class allocation (`Class.new`, `methods := []`) needs
`capAt_cls_nil`. -/

set_option hygiene false in
macro "cap_free" : tactic => `(tactic|
  (intro p hc
   first
     -- an ordinary payload constructor makes `CapAt` reduce to `False` by iota
     | exact hc
     -- and the three payloads iota cannot reduce, one lemma each. **Every one of these is a
     -- pure term**: a `simp` reached on every side goal of six hundred arms is a search, not a
     -- side condition, and it cost `runNumerics` a 14 GB proof term before it was moved into
     -- `capAt_proc_none`.
     | exact capAt_proc_none rfl rfl hc
     | exact capAt_emptyCore rfl hc
     | exact capAt_cls_nil rfl rfl hc))

/-- **The heap's set of capture edges did not grow** — every frame some object at `h'` captures
was already captured by some object at `h`. Existential in the object id; see the module
docstring for the builtin that forces that. -/
def CapMono (h h' : Heap) : Prop := ∀ o p, CapAt (h'.get o) p → ∃ o', CapAt (h.get o') p

theorem CapMono.refl (h : Heap) : CapMono h h := fun o _ hc => ⟨o, hc⟩

theorem CapMono.trans {a b c : Heap} (h₁ : CapMono a b) (h₂ : CapMono b c) : CapMono a c :=
  fun o p hc => by
    obtain ⟨o', hc'⟩ := h₂ o p hc
    exact h₁ o' p hc'

theorem CapMono.of_eq {h h' : Heap} (he : h' = h) : CapMono h h' := by
  rw [he]; exact CapMono.refl h

/-! ### The two shapes a heap write takes

Everything under `RubyCore/Builtins/` reaches the heap through one of these: it **pushes** a
fresh object (`Heap.alloc` and its wrappers) or it **sets** an existing one (`Heap.set`, and
`setClassPayload` through it). -/

/-- **Pushing an object whose edges are already in the heap.** The general form; the two
instances below are the ones the arms use. -/
theorem CapMono.push_gen {h : Heap} {obj : Object}
    (hcf : ∀ p, CapAt obj p → ∃ o', CapAt (h.get o') p) :
    CapMono h ⟨h.objs.push obj⟩ := by
  intro o p hc
  by_cases hlt : o < h.objs.size
  · refine ⟨o, ?_⟩
    rw [show (Heap.get ⟨h.objs.push obj⟩ o) = h.get o from by
      simp only [Heap.get, Array.getD_eq_getD_getElem?, Array.getElem?_push,
        if_neg (Nat.ne_of_lt hlt)]] at hc
    exact hc
  · by_cases heq : o = h.objs.size
    · subst heq
      have hget : Heap.get ⟨h.objs.push obj⟩ h.objs.size = obj := by
        simp only [Heap.get, Array.getD_eq_getD_getElem?, Array.getElem?_push, if_pos rfl]
        rfl
      rw [hget] at hc
      exact hcf p hc
    · -- past the end on both sides: `default`, which carries nothing
      refine ⟨o, ?_⟩
      have hge : h.objs.size + 1 ≤ o := by
        rcases Nat.lt_or_ge o h.objs.size with hx | hx
        · exact absurd hx hlt
        · exact Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hx (fun hc => heq hc.symm))
      have hoob : ¬ o < (h.objs.push obj).size := by
        simp only [Array.size_push]; exact Nat.not_lt.mpr hge
      have hget : Heap.get ⟨h.objs.push obj⟩ o = default := by
        simp only [Heap.get, Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_none (Nat.le_of_not_lt hoob)]
        rfl
      rw [hget] at hc
      exact absurd hc (capAt_default p)

/-- **Pushing a capture-free object** — every allocator in the layer but `dupObj`. The side
condition is about the object's payload alone, which is why the arms close by `rfl`. -/
theorem CapMono.push {h : Heap} {obj : Object} (hcf : ∀ p, ¬ CapAt obj p) :
    CapMono h ⟨h.objs.push obj⟩ :=
  CapMono.push_gen (fun p hc => absurd hc (hcf p))

/-- **Pushing a copy of an object already in the heap** — `dupObj`/`cloneObj`, which is where
a capture edge can legitimately appear at a fresh id. -/
theorem CapMono.push_copy {h : Heap} {obj : Object} {src : ObjId}
    (hp : obj.payload = (h.get src).payload) : CapMono h ⟨h.objs.push obj⟩ :=
  CapMono.push_gen (fun p hc => ⟨src, (capAt_congr hp p).mp hc⟩)

/-- **Overwriting an object with one that carries no new edge.** -/
theorem CapMono.set {h : Heap} {o : ObjId} {obj : Object}
    (hcf : ∀ p, CapAt obj p → CapAt (h.get o) p) : CapMono h (h.set o obj) := by
  intro o' p hc
  refine ⟨o', ?_⟩
  by_cases hf : o' = o
  · subst hf
    by_cases hlt : o' < h.objs.size
    · rw [show Heap.get (h.set o' obj) o' = obj from getD_set!_self h.objs o' obj hlt] at hc
      exact hcf p hc
    · rw [show Heap.get (h.set o' obj) o' = h.get o' from
        getD_set!_oob h.objs o' obj hlt] at hc
      exact hc
  · rw [show Heap.get (h.set o obj) o' = h.get o' from
      getD_set!_ne h.objs o o' obj hf] at hc
    exact hc

/-- The `Heap.set` special case every ivar/flag write is: the payload is copied. -/
theorem CapMono.set_payload {h : Heap} {o : ObjId} {obj : Object}
    (hp : obj.payload = (h.get o).payload) : CapMono h (h.set o obj) :=
  CapMono.set (fun p hc => (capAt_congr hp p).mp hc)

/-! ### At the machine

The arms hand back machines, so the walk is stated at machines and the heap projection is
where the content is. `MCap.of_eq` is the analogue of `LocalsSame.of_eq` and covers every arm
that writes a field other than the heap. -/

/-- `CapMono` on the two machines' heaps. -/
def MCap (m m' : Machine) : Prop := CapMono m.heap m'.heap

theorem MCap.refl (m : Machine) : MCap m m := CapMono.refl m.heap

theorem MCap.trans {a b c : Machine} (h₁ : MCap a b) (h₂ : MCap b c) : MCap a c :=
  CapMono.trans h₁ h₂

/-- A machine that differs anywhere but the heap. -/
theorem MCap.of_eq {m m' : Machine} (hh : m'.heap = m.heap) : MCap m m' :=
  CapMono.of_eq hh

/-- **An arm that destructured its result as a pair.** `runStrings`' `String#match` family binds
`match allocStrEnc … with | (v, m) => .ok v m`, so `split at h` introduces `pm : Value × Machine`
with the chain in a *separate* equation and `m'` linked only through it — invisible to every
closer above. This re-links them, with the equation supplied by `assumption`. -/
theorem MCap.of_pair {m m' : Machine} {v : Value} {pm : Value × Machine}
    (he : pm = (v, m')) (h : MCap m pm.2) : MCap m m' := by
  rw [he] at h; exact h

/-! ### The shape goes in a `rfl` hypothesis, not in the conclusion

**The one measurement that made this file tractable.** `FrameLocal.lean` closes six hundred
arms in ninety seconds with `LocalsSame.of_eq rfl rfl`, and the reason is the *shape* of that
lemma: its conclusion is `LocalsSame m ?m'`, which unifies with any goal first-order and
instantly, and everything specific lives in hypotheses that compare **projections** by `rfl`.

The first version of this file did the opposite — `CapMono.push` concludes
`CapMono ?h ⟨?h.objs.push ?obj⟩`, so to *fail* on a non-allocating arm the unifier has to unfold
`Builtins.allocStr`/`Heap.alloc` and match a structure literal against a machine-sized term.
Six hundred arms times eight closers of expensive failure: `sample` on the running process
showed 60% of it in `whnfImp`/`tryHeuristic`/`reduceMatcher?`/`getStuckMVar?`, and it had not
finished in thirty-five minutes.

The `_eq` variants below are the repair. `MCap.push_eq rfl ?_` unifies its conclusion in one
step, proves `m'.heap.objs = m.heap.objs.push ?obj` by `rfl` — which unfolds the allocator
*once*, type-directed — and fails fast on the `Array.push` head when the arm allocated nothing.
Worth recording as the general lesson, because it is the second time this layer has paid for
it: **put the arm's shape in a `rfl`-provable hypothesis; leave the conclusion first-order.** -/

/-- **An arm that pushed one object**, with the push read off as an equation. -/
theorem MCap.push_eq {m m' : Machine} {obj : Object}
    (he : m'.heap.objs = m.heap.objs.push obj) (hcf : ∀ p, ¬ CapAt obj p) : MCap m m' := by
  intro o p hc
  have hh : m'.heap = ⟨m.heap.objs.push obj⟩ := by rw [← he]
  rw [hh] at hc
  exact CapMono.push hcf o p hc

/-- **An arm that pushed a *copy* of an object already in the heap** — `dupObj`, and the one
allocation in the layer whose payload can carry a capture edge (`p.dup` on a Proc). Both
hypotheses are `rfl`: the first reads the pushed object off the goal, the second reads the
source id off that object's payload. -/
theorem MCap.push_copy_eq {m m' : Machine} {obj : Object} {src : ObjId}
    (he : m'.heap.objs = m.heap.objs.push obj)
    (hp : obj.payload = (m.heap.get src).payload) : MCap m m' := by
  intro o p hc
  have hh : m'.heap = ⟨m.heap.objs.push obj⟩ := by rw [← he]
  rw [hh] at hc
  exact CapMono.push_copy hp o p hc

/-- **An arm that overwrote one object**, likewise. -/
theorem MCap.set_eq {m m' : Machine} {o : ObjId} {obj : Object}
    (he : m'.heap.objs = m.heap.objs.set! o obj)
    (hcf : ∀ p, CapAt obj p → CapAt (m.heap.get o) p) : MCap m m' := by
  intro o' p hc
  have hh : m'.heap = m.heap.set o obj := by rw [Heap.set, ← he]
  rw [hh] at hc
  exact CapMono.set hcf o' p hc

/-- **Peeling one push off the end of a chain.** Same discipline as `push_eq`: the conclusion is
`MCap ?m ?m'`, which unifies first-order, and the `rfl` hypothesis reads `mid` and `obj` off the
goal. This is what lets a chain of any length close by a `repeat` fixpoint without a single
goal-keyed closer. -/
theorem MCap.push_trans_eq {m m' mid : Machine} {obj : Object}
    (he : m'.heap.objs = mid.heap.objs.push obj) (h : MCap m mid) (hcf : ∀ p, ¬ CapAt obj p) :
    MCap m m' :=
  h.trans (MCap.push_eq he hcf)

/-- …and one set. -/
theorem MCap.set_trans_eq {m m' mid : Machine} {o : ObjId} {obj : Object}
    (he : m'.heap.objs = mid.heap.objs.set! o obj) (h : MCap m mid)
    (hcf : ∀ p, CapAt obj p → CapAt (mid.heap.get o) p) : MCap m m' :=
  h.trans (MCap.set_eq he hcf)

/-- The `set` every ivar/flag write is: the payload is copied, so the side condition is `rfl`. -/
theorem MCap.set_payload_eq {m m' : Machine} {o : ObjId} {obj : Object}
    (he : m'.heap.objs = m.heap.objs.set! o obj)
    (hp : obj.payload = (m.heap.get o).payload) : MCap m m' :=
  MCap.set_eq he (fun p hc => (capAt_congr hp p).mp hc)

/-- **`String#freeze`/`clone` on a `dup`**: push a copy, then set the *new* object's flag. It
needs its own lemma rather than `push_copy_eq.trans set_payload_eq`, because `MCap.trans` would
have to be given the intermediate machine and `?mid.heap.objs ≟ m.heap.objs.push cpy` is a
projection against a metavariable — `notes.md`'s shape problem, and the same reason
`push_trans_eq` cannot peel this arm. Naming the composite keys it. -/
theorem MCap.push_copy_then_set {m m' : Machine} {cpy obj : Object} {src o : ObjId}
    (he : m'.heap.objs = (m.heap.objs.push cpy).set! o obj)
    (hp : cpy.payload = (m.heap.get src).payload)
    (hq : obj.payload = (Heap.get ⟨m.heap.objs.push cpy⟩ o).payload) : MCap m m' :=
  (MCap.push_copy_eq (m' := { m with heap := ⟨m.heap.objs.push cpy⟩ }) rfl hp).trans
    (MCap.set_eq (m := { m with heap := ⟨m.heap.objs.push cpy⟩ }) he
      (fun p hc => (capAt_congr hq p).mp hc))


#print axioms CapMono.push
#print axioms CapMono.set

/-! ## What `CapMono` buys: the two hypotheses of `builtins_run_seal`

`Denote/Sem/StepLocal.lean` left the seal across `Builtins.run` owing exactly two heap
clauses. `CapMono` discharges both, and the proof is the reason `CapAt` is keyed on `methodOf`:
a capture edge at `m'` is pulled back to *the same object id* at `m`, where it is either a
Proc `Sealed.clos` covers or a first-match method `Sealed.meth` covers. -/

/-- **A capture edge into `p` is readable somewhere in `h`** — in one of exactly the two ways
`Sealed` reads the heap. This is the shape the pull-backs land in and the shape the seal's two
clauses consume. -/
def SealHit (h : Heap) (p : Nat) : Prop :=
  (∃ (o : ObjId) (cl : Closure), procClosure? h (.ref o) = some cl ∧ cl.captured = some p) ∨
  (∃ (k : ObjId) (n : String) (md : MethodDef), methodIn h k n = some md ∧
    md.capturedFrame = some p)

/-- `CapAt` **is** `SealHit` at a named object: the two constructors of `CapAt` are the two
disjuncts. -/
theorem capAt_sealHit {h : Heap} {o : ObjId} {p : Nat} (hc : CapAt (h.get o) p) :
    SealHit h p := by
  simp only [CapAt] at hc
  cases hpl : (h.get o).payload with
  | proc c =>
    rw [hpl] at hc
    exact Or.inl ⟨o, c, by simp only [procClosure?, hpl], hc⟩
  | cls cp =>
    rw [hpl] at hc
    obtain ⟨n, md, hmd, hcap⟩ := hc
    refine Or.inr ⟨o, n, md, ?_, hcap⟩
    rw [methodIn_eq_methodOf (by rw [Heap.classPayload?, hpl]) n]
    exact hmd
  | _ => rw [hpl] at hc; exact absurd hc (by simp)

/-- A Proc capture edge readable at `h'`, read back at `h`. -/
theorem CapMono.clos_pull {h h' : Heap} (hcm : CapMono h h') {o : ObjId} {cl : Closure}
    (hcl : procClosure? h' (.ref o) = some cl) {p : Nat} (hp : cl.captured = some p) :
    SealHit h p := by
  have hat : CapAt (h'.get o) p := by
    simp only [procClosure?] at hcl
    cases hpl : (h'.get o).payload with
    | proc c =>
      rw [hpl] at hcl
      simp only [Option.some.injEq] at hcl
      simp only [CapAt, hpl]
      rw [hcl]; exact hp
    | _ => rw [hpl] at hcl; exact absurd hcl (by simp)
  obtain ⟨o₀, hat'⟩ := hcm o p hat
  exact capAt_sealHit hat'

/-- A method capture edge readable at `h'`, read back at `h`. -/
theorem CapMono.meth_pull {h h' : Heap} (hcm : CapMono h h') {k : ObjId} {n : String}
    {md : MethodDef} (hmd : methodIn h' k n = some md) {p : Nat}
    (hp : md.capturedFrame = some p) : SealHit h p := by
  have hat : CapAt (h'.get k) p := by
    simp only [methodIn, Heap.classPayload?] at hmd
    cases hpl : (h'.get k).payload with
    | cls cp =>
      rw [hpl] at hmd
      simp only [Option.bind_some] at hmd
      simp only [CapAt, hpl]
      exact ⟨n, md, hmd, hp⟩
    | _ => rw [hpl] at hmd; exact absurd hmd (by simp)
  obtain ⟨o₀, hat'⟩ := hcm k p hat
  exact capAt_sealHit hat'

/-- **The seal travels across any capture-monotone heap change**, given the frame side. -/
theorem Sealed.of_capMono {b : FrameId} {m m' : Machine} (h : Sealed b m)
    (hls : LocalsSame m m') (hcm : MCap m m') : Sealed b m' :=
  h.of_localsSame hls
    (fun o cl hcl p hp => by
      rcases hcm.clos_pull hcl hp with ⟨o', cl', hcl', hp'⟩ | ⟨k, n, md, hmd, hp'⟩
      · exact h.clos o' cl' hcl' p hp'
      · exact h.meth k n md hmd p hp')
    (fun k n md hmd p hp => by
      rcases hcm.meth_pull hmd hp with ⟨o', cl', hcl', hp'⟩ | ⟨k', n', md', hmd', hp'⟩
      · exact h.clos o' cl' hcl' p hp'
      · exact h.meth k' n' md' hmd' p hp')

/-- …and the bookkeeping half with it. -/
theorem FramesWF.of_capMono {m m' : Machine} (h : FramesWF m) (hls : LocalsSame m m')
    (hcm : MCap m m') : FramesWF m' :=
  h.of_localsSame hls
    (fun o cl hcl p hp => by
      rcases hcm.clos_pull hcl hp with ⟨o', cl', hcl', hp'⟩ | ⟨k, n, md, hmd, hp'⟩
      · exact h.clos o' cl' hcl' p hp'
      · exact h.meth k n md hmd p hp')
    (fun k n md hmd p hp => by
      rcases hcm.meth_pull hmd hp with ⟨o', cl', hcl', hp'⟩ | ⟨k', n', md', hmd', hp'⟩
      · exact h.clos o' cl' hcl' p hp'
      · exact h.meth k' n' md' hmd' p hp')

#print axioms Sealed.of_capMono
#print axioms FramesWF.of_capMono

/-! ## The twenty machine-threading helpers, again

`Denote/Sem/FrameLocal.lean`'s list, one `MCap` lemma per entry. This is the price the notes
quoted — the second walk needs its own copy — and the copies are *not* uniform with the
originals, which is the interesting part: where `LocalsSame` was `of_eq rfl rfl` for every
allocator, `MCap` has to name the payload. Six lemmas below are `CapMono.push` and one is
`CapMono.push_copy`; the rest are `of_eq`, and those are exactly the arms that write a field
other than the heap. -/

theorem emit_cap (m : Machine) (s : String) : MCap m (m.emit s) := MCap.of_eq rfl

theorem allocArr_cap (m : Machine) (xs : Array Value) :
    MCap m (Builtins.allocArr m xs).2 := CapMono.push (fun _ hc => hc)

theorem allocHsh_cap (m : Machine) (xs : Array (Value × Value)) :
    MCap m (Builtins.allocHsh m xs).2 := CapMono.push (fun _ hc => hc)

theorem allocExc_cap (m : Machine) (cls : ObjId) (msg : String) :
    MCap m (Builtins.allocExc m cls msg).2 := CapMono.push (fun _ hc => hc)

theorem allocStr_cap (m : Machine) (s : String) :
    MCap m (Builtins.allocStr m s).2 := CapMono.push (fun _ hc => hc)

theorem allocStrEnc_cap (m : Machine) (s : String) (b : Bool) :
    MCap m (Builtins.allocStrEnc m s b).2 := CapMono.push (fun _ hc => hc)

theorem allocMData_cap (m : Machine) (s : String)
    (caps : Array (Option (Nat × Nat))) (names : List (String × Nat)) (bin : Bool) :
    MCap m (Builtins.allocMData m s caps names bin).2 := CapMono.push (fun _ hc => hc)

/-- **`dup`/`clone`**, and the one allocator whose object can carry a capture edge: the payload
is the source's, so a `Proc#dup` really does put the same edge at a fresh id. `push_copy` is
what makes that sound rather than a counterexample — see the module docstring. -/
theorem dupObj_cap (m : Machine) (o : ObjId) (kf : Bool) :
    MCap m (Builtins.dupObj m o kf).2 := CapMono.push_copy (src := o) rfl

/-- `$~`'s write is to a **frame**, so the heap is untouched. -/
theorem setLastMatchValue_cap (m : Machine) (v : Value) : MCap m (m.setLastMatchValue v) :=
  MCap.of_eq (by
    unfold Machine.setLastMatchValue
    by_cases hlt : m.matchFrameId < m.frames.size
    · rw [if_pos hlt]
    · rw [if_neg hlt])

theorem setMatchGlobals_cap (m : Machine) (md : Option Value) :
    MCap m (Builtins.setMatchGlobals m md) := setLastMatchValue_cap _ _

theorem foldlM_cap {α : Type} (f : Machine → α → Option Machine)
    (hf : ∀ m a m', f m a = some m' → MCap m m') :
    ∀ (l : List α) (m m' : Machine), l.foldlM f m = some m' → MCap m m'
  | [], m, m', h => by
    simp only [List.foldlM_nil] at h
    injection h with h
    exact h ▸ MCap.refl m
  | a :: rest, m, m', h => by
    rw [List.foldlM_cons] at h
    cases hstep : f m a with
    | none => rw [hstep] at h; exact absurd h (by simp)
    | some m₁ =>
      rw [hstep] at h
      exact (hf m a m₁ hstep).trans (foldlM_cap f hf rest m₁ m' h)

theorem putsGo_cap : ∀ (fuel : Nat) (m : Machine) (args : List Value) (m₂ : Machine),
    Builtins.putsGo m args fuel = some m₂ → MCap m m₂ := by
  intro fuel
  induction fuel with
  | zero => intro m args m₂ h; simp [Builtins.putsGo] at h
  | succ n ih =>
    intro m args m₂ h
    rw [Builtins.putsGo] at h
    refine foldlM_cap _ ?_ args m m₂ h
    intro m' a m'' hstep
    repeat (any_goals (first
      | (cases hstep; exact emit_cap _ _)
      | (obtain ⟨-, rfl⟩ := hstep; exact emit_cap _ _)
      | (simp at hstep)
      | (exact ih m' _ m'' hstep)
      | split at hstep))

theorem putsImpl_cap (m : Machine) (args : List Value) :
    ∀ v m', Builtins.putsImpl m args = .ok v m' → MCap m m' := by
  intro v m' h
  rw [Builtins.putsImpl] at h
  cases hg : Builtins.putsGo m args 100 with
  | none => rw [hg] at h; exact absurd h (by simp)
  | some m₁ =>
    rw [hg] at h
    simp only [BRes.ok.injEq] at h
    exact (putsGo_cap 100 m args m₁ hg).trans (h.2 ▸ MCap.of_eq rfl)

theorem printFold_cap : ∀ (args : List Value) (m m₂ : Machine),
    args.foldlM (fun m a => match Builtins.toSP m a with
      | .ok s => some (m.emit s)
      | .error _ => none) m = some m₂ → MCap m m₂ := by
  refine foldlM_cap _ (fun m a m' hs => ?_)
  split at hs
  · cases hs; exact emit_cap _ _
  · exact absurd hs (by simp)

theorem pGo_cap : ∀ (m : Machine) (args : List Value) (m₂ : Machine),
    Builtins.runObjects.go m args = some m₂ → MCap m m₂
  | m, [], m₂, h => by
    rw [Builtins.runObjects.go] at h
    injection h with h
    exact h ▸ MCap.refl m
  | m, a :: rest, m₂, h => by
    rw [Builtins.runObjects.go] at h
    split at h
    · exact (emit_cap _ _).trans (pGo_cap _ rest m₂ h)
    · exact absurd h (by simp)

theorem foldPair_cap {α β : Type} (f : β × Machine → α → β × Machine)
    (hf : ∀ p a, MCap (p : β × Machine).2 (f p a).2) :
    ∀ (l : List α) (p : β × Machine), MCap p.2 (l.foldl f p).2
  | [], p => MCap.refl p.2
  | a :: rest, p => by
    rw [List.foldl_cons]
    exact (hf p a).trans (foldPair_cap f hf rest (f p a))

theorem foldPairArray_cap {α β : Type} (f : β × Machine → α → β × Machine)
    (hf : ∀ p a, MCap (p : β × Machine).2 (f p a).2) (l : Array α) (p : β × Machine) :
    MCap p.2 (l.foldl f p).2 := by
  rw [← Array.foldl_toList]
  exact foldPair_cap f hf _ p

/-- **A fold whose every step is capture-monotone**, in the same `rfl`-hypothesis shape.

`foldPair_cap`'s own conclusion is `MCap p.2 (l.foldl f p).2`, and applying it through
`MCap.trans` asks unification to solve `?p.2 ≟ m` — a projection against a metavariable, which
it cannot do, so the branch silently never fires (measured: it left `Regexp#names`' arm open).
Reading the fold off the goal's `m'` by `rfl` determines `?l`, `?f` and `?p` structurally
instead. -/
theorem MCap.fold_eq {α β : Type} {m m' : Machine} {f : β × Machine → α → β × Machine}
    {l : List α} {p : β × Machine} (he : m' = (l.foldl f p).2) (hm : p.2 = m)
    (hf : ∀ q a, MCap (q : β × Machine).2 (f q a).2) : MCap m m' := by
  subst he; subst hm; exact foldPair_cap f hf l p

/-- The `Array` twin. -/
theorem MCap.foldArray_eq {α β : Type} {m m' : Machine} {f : β × Machine → α → β × Machine}
    {l : Array α} {p : β × Machine} (he : m' = (l.foldl f p).2) (hm : p.2 = m)
    (hf : ∀ q a, MCap (q : β × Machine).2 (f q a).2) : MCap m m' := by
  subst he; subst hm; exact foldPairArray_cap f hf l p

theorem setLastMatch_cap (m : Machine) (s src : String) (opts : Nat)
    (hits : List (Nat × Nat × Array (Option (Nat × Nat)))) (bin : Bool) :
    MCap m (Builtins.setLastMatch m s src opts hits bin) := by
  unfold Builtins.setLastMatch
  split
  · exact setMatchGlobals_cap _ _
  · exact (allocMData_cap _ _ _ _ _).trans (setMatchGlobals_cap _ _)

theorem regexApply_cap (bid : String) (m : Machine) (re subj : Value) :
    ∀ v m', Builtins.runRegex.regexApply bid m re subj = .ok v m' → MCap m m' := by
  intro v m' h
  unfold Builtins.runRegex.regexApply at h
  repeat (any_goals (first
    | (cases h; exact MCap.refl _)
    | (cases h; exact setMatchGlobals_cap _ _)
    | (cases h; exact (allocMData_cap _ _ _ _ _).trans (setMatchGlobals_cap _ _))
    | (simp at h)
    | (unfold Builtins.runRegex.applyTo at h)
    | split at h))

theorem scanAll_cap (m : Machine) (s src : String) (opts : Nat) (bin : Bool) :
    ∀ v m', Builtins.runRegex.scanAll m s src opts bin = .ok v m' → MCap m m' := by
  intro v m' h
  unfold Builtins.runRegex.scanAll at h
  split at h
  · exact absurd h (by simp)
  · dsimp only at h
    cases h
    refine (setLastMatch_cap _ _ _ _ _ _).trans
      (MCap.trans (foldPair_cap _ ?_ _ _) (allocArr_cap _ _))
    intro p a
    split
    · exact allocStrEnc_cap _ _ _
    · refine MCap.trans (foldPair_cap _ ?_ _ (#[], p.snd)) (allocArr_cap _ _)
      intro q b
      split
      · exact allocStrEnc_cap _ _ _
      · exact MCap.refl _

theorem splitBy_cap (m : Machine) (s src : String) (opts : Nat) (lim : Int) (bin : Bool) :
    ∀ v m', Builtins.runRegex.splitBy m s src opts lim bin = .ok v m' → MCap m m' := by
  intro v m' h
  unfold Builtins.runRegex.splitBy at h
  split at h
  · dsimp only at h
    cases h
    exact allocArr_cap _ _
  · split at h
    · exact absurd h (by simp)
    · dsimp only at h
      cases h
      refine MCap.trans (foldPair_cap _ ?_ _ _) (allocArr_cap _ _)
      intro p a
      exact allocStrEnc_cap _ _ _

theorem splitOn_cap (m : Machine) (hp : Heap) (s : String) (pat : Value) (lim : Int)
    (bin : Bool) :
    ∀ v m', Builtins.runRegex.splitOn m hp s pat lim bin = .ok v m' → MCap m m' := by
  intro v m' h
  unfold Builtins.runRegex.splitOn at h
  repeat (any_goals (first
    | (exact splitBy_cap _ _ _ _ _ _ _ _ h)
    | (simp at h)
    | split at h))

theorem subst_cap (m : Machine) (s src : String) (opts : Nat) (rep : String)
    (global : Bool) (recvV repV : Value) :
    ∀ v m', Builtins.runRegex.subst m s src opts rep global recvV repV = .ok v m' →
      MCap m m' := by
  intro v m' h
  unfold Builtins.runRegex.subst at h
  split at h
  · exact absurd h (by simp)
  · dsimp only at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · dsimp only [Builtins.okStrEnc, Builtins.allocStrEnc] at h
        cases h
        exact (setLastMatch_cap _ _ _ _ _ _).trans (CapMono.push (fun _ hc => hc))

/-- The one `setClassPayload` in the whole layer (`Module#private_constant`, which rewrites
`privateConsts`): the method table is what `CapAt` reads, and it is copied. -/
theorem CapMono.setClassPayload_methods {h : Heap} {o : ObjId} {cp cp' : ClassPayload}
    (hc : h.classPayload? o = some cp) (hm : cp'.methods = cp.methods) :
    CapMono h (h.setClassPayload o cp') := by
  refine CapMono.set (fun p hcap => ?_)
  simp only [CapAt] at hcap ⊢
  have hpl : (h.get o).payload = .cls cp := by
    simp only [Heap.classPayload?] at hc
    cases hp : (h.get o).payload with
    | cls c =>
      rw [hp] at hc
      exact congrArg Payload.cls (Option.some.inj hc)
    | _ => rw [hp] at hc; exact absurd hc (by simp)
  rw [hpl]
  obtain ⟨n, md, hmd, hcf⟩ := hcap
  refine ⟨n, md, ?_, hcf⟩
  simp only [methodOf] at hmd ⊢
  rw [← hm]
  exact hmd

/-! `cap_norm` is `RubyCore/Proof/KontFrame.lean`'s `frame_simp` technique, and it is what makes
the closer list short. Measured (`profiler.threshold 400` on `runRegex`): a **goal**-keyed helper
closer — `exact setMatchGlobals_cap _ _`, whose conclusion is `MCap m (Builtins.setMatchGlobals
m ?md)` — costs 1–12 s *to fail*, because unifying it forces `whnf` to unfold the helper against
a machine-sized term, and the profile showed the same block of five such failures repeating per
goal. Unfolding the helpers **once, in the goal**, replaces fifteen expensive unifications with
one `simp only`, after which the arm's machine is a record-update literal and the cheap
projection closers apply.

`apply_ite`/`ite_self` are in the set for `setLastMatchValue`, whose two branches differ in
`frames` and agree on `heap`: pushing the projection inside the `if` makes the two sides
identical and `ite_self` finishes it, so no `split` is needed. -/

set_option hygiene false in
macro "cap_norm" : tactic => `(tactic|
  simp only [Builtins.allocStr, Builtins.allocStrEnc, Builtins.allocArr, Builtins.allocHsh,
    Builtins.allocExc, Builtins.allocMData, Builtins.dupObj, Builtins.okStr, Builtins.okStrEnc,
    Builtins.setMatchGlobals, Machine.setLastMatchValue, Machine.emit, Machine.setCurrentFrame,
    Heap.alloc, Heap.set, Heap.setClassPayload])

set_option hygiene false in
macro "cap_step" : tactic => `(tactic|
  first
    | exact MCap.refl _
    | exact MCap.of_eq rfl
    | (refine MCap.push_eq rfl ?_; cap_free)
    | exact MCap.push_copy_eq rfl rfl
    | exact MCap.set_payload_eq rfl rfl
    | (refine MCap.set_eq rfl ?_; intro p hc
       first
         | exact hc
         | exact False.elim hc
         | exact Option.noConfusion hc
         | exact capAt_cls_privConsts (by assumption) hc)
    | (refine MCap.push_trans_eq rfl ?_ ?_; rotate_left; cap_free)
    | (refine MCap.set_trans_eq rfl ?_ ?_; rotate_left; intro p hc
       first
         | exact hc
         | exact False.elim hc
         | exact Option.noConfusion hc
         | exact capAt_cls_privConsts (by assumption) hc)
    | (refine MCap.fold_eq rfl rfl ?_; intro q a)
    | (refine MCap.foldArray_eq rfl rfl ?_; intro q a)
    | split)

/-! The chain closer: a `repeat` fixpoint over steps whose conclusions are all first-order, so
nesting is free and every failure is a `rfl` head-check. -/

set_option hygiene false in
macro "cap_close" : tactic => `(tactic| ((repeat (any_goals cap_step)); done))

set_option hygiene false in
macro "cap_leaf" : tactic => `(tactic|
  first
    -- the cheap path: chain of projection equations, closed by a fixpoint
    | cap_close
    -- otherwise normalise the machine once, then the same fixpoint
    | (cap_norm; cap_close)
    -- …or the arm destructured its result as a pair: re-link, then either of the above
    | (refine MCap.of_pair (by assumption) ?_
       first
         | cap_close
         | (cap_norm; cap_close)
         | exact ((allocMData_cap _ _ _ _ _).trans (setMatchGlobals_cap _ _)).trans
             (allocStrEnc_cap _ _ _))
    -- `String#match`'s chain, **keyed**. `push_trans_eq`'s `?mid` cannot be recovered from a
    -- projection pattern (`?mid.heap.objs ≟ inner.heap.objs`), which is `notes.md`'s shape
    -- problem — Lean collapses the nested record update and nothing matches `{?mid with …}`.
    -- The fix there was the same: a keyed variant per callee.
    | exact ((allocMData_cap _ _ _ _ _).trans (setMatchGlobals_cap _ _)).trans
        (allocStrEnc_cap _ _ _))

/-! ### The context-searching closers, kept out of the common path

Measured: `exact printFold_cap _ _ _ (by assumption)` costs ~12 s **to fail**, because
`assumption` runs `isDefEq` against a machine-sized `h`. And it is needed by exactly one
dispatcher — `printFold`/`pGo` are `Object#print` and `Object#p`, which live in `runObjects`,
and `setClassPayload_methods` is `Module#private_constant`, in `runModules`. Splitting the walk
per module (which was done for the progress readout) is what lets each dispatcher pay only for
its own tail: five of the six use `cap_arms`, and the two that need a tail use `cap_arms_ctx`. -/

set_option hygiene false in
macro "cap_leaf_rx" : tactic => `(tactic|
  first
    | cap_leaf
    | exact ((allocMData_cap _ _ _ _ _).trans (setMatchGlobals_cap _ _)).trans
        (runRegex_cap _ _ _ _ _ _ (by assumption)))

set_option hygiene false in
macro "cap_leaf_mod" : tactic => `(tactic| cap_leaf)

set_option hygiene false in
macro "cap_leaf_obj" : tactic => `(tactic|
  first
    | cap_leaf
    | exact printFold_cap _ _ _ (by assumption)
    | exact pGo_cap _ _ _ (by assumption)
    | exact (pGo_cap _ _ _ (by assumption)).trans (allocArr_cap _ _)
    | exact (printFold_cap _ _ _ (by assumption)).trans (allocArr_cap _ _))

/-- **`Module#private_constant`'s arm, as a side goal rather than as a conclusion.**

`setClassPayload h o cp'` *is* `h.set o { h.get o with payload := .cls cp' }`, so the arm is an
ordinary `set` and `MCap.set_eq` peels it with a first-order conclusion. What is left is this:
the overwritten payload's method table is the old one's, so it carries no new edge. Keeping it
at the side goal — where `cp'` is already concrete — is the difference between a closer that
costs 12 s to *fail* on every other arm and one that costs nothing (§the second walk, item 1). -/
theorem capAt_cls_privConsts {h : Heap} {o : ObjId} {cp : ClassPayload} {pcs : List String}
    {p : Nat} (hc : h.classPayload? o = some cp)
    (hcap : CapAt { h.get o with payload := .cls { cp with privateConsts := pcs } } p) :
    CapAt (h.get o) p := by
  have hpl : (h.get o).payload = .cls cp := by
    simp only [Heap.classPayload?] at hc
    cases hp : (h.get o).payload with
    | cls c => rw [hp] at hc; exact congrArg Payload.cls (Option.some.inj hc)
    | _ => rw [hp] at hc; exact absurd hc (by simp)
  simp only [CapAt] at hcap ⊢
  rw [hpl]
  obtain ⟨n, md, hmd, hcf⟩ := hcap
  exact ⟨n, md, hmd, hcf⟩

/-- **`Class#new`'s allocator**, and the one helper that needs its splits *ordered* — the same
`newImpl_locals` does, for the same reason (`split at h` reaches for a scrutinee whose binder
is not yet in scope). Every object it pushes has a concrete payload. -/
theorem newImpl_cap (m : Machine) (recv : Value) (args : List Value) :
    ∀ v m', Builtins.newImpl m recv args = .ok v m' → MCap m m' := by
  intro v m' h
  unfold Builtins.newImpl at h
  split at h
  · rename_i o
    split at h
    · exact absurd h (by simp)
    · rename_i c hc
      by_cases hmod : c.isModule = true
      · rw [if_pos hmod] at h; exact absurd h (by simp)
      · rw [if_neg hmod] at h
        by_cases hexc : (ancestors m.heap o).contains Boot.exceptionId = true
        · rw [if_pos hexc] at h
          repeat (any_goals (first
            | (cases h; cap_leaf)
            | (cases h; exact MCap.of_eq rfl)
            | (simp at h)
            | split at h))
        · rw [if_neg hexc] at h
          by_cases hstr : (ancestors m.heap o).contains Boot.stringId = true
          · rw [if_pos hstr] at h
            repeat (any_goals (first
              | (cases h; cap_leaf)
              | (cases h; exact MCap.of_eq rfl)
              | (simp at h)
              | split at h))
          · rw [if_neg hstr] at h
            repeat (any_goals (first
              | (cases h; cap_leaf)
              | (cases h; cap_leaf)
              | (cases h; exact MCap.refl _)
              | (cases h; exact MCap.of_eq rfl)
              | (cases h; cap_leaf)
              | (simp at h)
              | split at h))
  · exact absurd h (by simp)

/-! ## The closers, and the seven dispatchers' tactic

The same shape as `FrameLocal.lean`'s `builtin_arms`: reduce the dispatcher's equation, then
repeatedly close a leaf or split. What differs is the **closer list**, and the difference is the
whole content of this file — where the frame walk answered `of_eq rfl rfl` for every allocating
arm, this one has to say *which* heap change happened. Six closers do it: `MCap.refl`/
`MCap.of_eq` (no heap change), `CapMono.push` (a fresh object with a concrete payload),
`CapMono.set` (a payload write), `CapMono.set_payload` (a flag write, payload copied),
`CapMono.push_copy` through `dupObj_cap`, and `CapMono.setClassPayload_methods` (the one
`setClassPayload`).

**Split into `cap_leaf` and `cap_arms`, which the frame walk did not need to be.** There the
leaf closer was `of_eq rfl rfl` whatever the arm had done, so `cases h; exact …` was one
alternative. Here there are six, and inlining them into the outer `first` would run `cases h`
once per closer — measured: the six hundred arms did not finish. Peeling the hypothesis once
and then choosing the closer is the same search with the expensive step hoisted out. -/

/-! ## The closers, and the seven dispatchers' tactic

The same shape as `FrameLocal.lean`'s `builtin_arms`: reduce the dispatcher's equation, then
repeatedly close a leaf or split. What differs is the **closer list**, and the difference is the
whole content of this file — where the frame walk answered `of_eq rfl rfl` for every allocating
arm, this one has to say *which* heap change happened. Eight closers do it: `MCap.refl`/
`MCap.of_eq` (no heap change), three `CapMono.push` (a fresh object, by payload constructor),
two `CapMono.set` (a payload write), `CapMono.set_payload` (a flag write, payload copied),
`CapMono.push_copy` through `dupObj_cap`, and `CapMono.setClassPayload_methods` (the layer's one
`setClassPayload`).

**Three measurements about the tactic, each of which cost a run of the walk** (~3 min for
`runRegex` alone, so they are not free to re-learn):

1. **Peel the hypothesis once, then choose the closer.** The frame walk's leaf closer was
   `of_eq rfl rfl` whatever the arm had done, so `cases h; exact …` was *one* alternative. There
   are eight here, and inlining them into the outer `first` runs `cases h` eight times per goal
   — the six hundred arms did not finish. Hence `cap_leaf`.
2. **No nested `by` in a closer.** `CapMono.push (fun _ hc => by simp at hc)` is tried on every
   leaf of every arm, and a `simp` on a machine-sized goal is not a side condition, it is a
   search. Every side condition here is a **pure term**: `fun _ hc => hc` where the payload's
   constructor makes `CapAt` reduce to `False`, `Option.noConfusion hc` for the one Proc
   allocation (`Symbol#to_proc`, whose `captured` is `none` since L266), and `capAt_cls_nil` for
   the one class allocation (`Class.new`, whose `methods` is `[]`).
3. **A `repeat (any_goals …)` fixpoint of *peeling* closers (`refine MCap.trans ?_ (…)`) is
   slower than naming the chains.** It reads better and it was measured at 4× the time, because
   a peel's second argument has to be elaborated against a metavariable machine. There are only
   two chained shapes in the layer, so they are written out. -/

set_option hygiene false in
macro "cap_arms" : tactic => `(tactic|
  repeat (any_goals (first
    | (cases h; cap_leaf)
    | (obtain ⟨-, rfl⟩ := h; cap_leaf)
    | (dsimp only at h)
    | (unfold Builtins.withIndex at h)
    | split at h
    | (exact putsImpl_cap _ _ _ _ h)
    | (exact regexApply_cap _ _ _ _ _ _ h)
    | (exact scanAll_cap _ _ _ _ _ _ _ h)
    | (exact splitBy_cap _ _ _ _ _ _ _ _ h)
    | (exact splitOn_cap _ _ _ _ _ _ _ _ h)
    | (exact subst_cap _ _ _ _ _ _ _ _ _ _ h)
    | (exact (setMatchGlobals_cap _ _).trans (splitOn_cap _ _ _ _ _ _ _ _ h))
    | (exact (setMatchGlobals_cap _ _).trans (splitBy_cap _ _ _ _ _ _ _ _ h))
    | (exact ((allocMData_cap _ _ _ _ _).trans
        (setMatchGlobals_cap _ _)).trans (runRegex_cap _ _ _ _ _ _ h))
    | (exact newImpl_cap _ _ _ _ _ h)
        | (simp at h)
    | split at h
    | (unfold Builtins.numBin at h)
    | (unfold Builtins.okStrFrom at h)
    | (unfold Builtins.binArg at h)
    | (unfold Builtins.frozenErr at h)
    | (unfold Builtins.coerceFailed at h)
    | (unfold Builtins.floatToInt at h)
    | (unfold Builtins.raiseImpl at h)
    | (unfold Builtins.raiseClass at h)
    | (unfold Builtins.intBitRef at h)
    | (unfold Builtins.numCmp at h)
    | (unfold Builtins.sortImpl at h)
    | (unfold Builtins.joinImpl at h)
    | (unfold Builtins.okStr at h)
    | (unfold Builtins.okStrEnc at h)
    | (unfold Builtins.allocStr at h)
    | (unfold Builtins.allocStrEnc at h)
    | (unfold Builtins.allocArr at h)
    | (unfold Builtins.allocHsh at h)
    | (unfold Builtins.allocExc at h)
    | (unfold Builtins.dupObj at h)
    -- `simp at h` **last**: on an arithmetic arm it tries to evaluate `Int`/`Float` literals,
    -- which took `runNumerics` to a 14 GB proof term that never finished. `dsimp only at h`
    -- above does the one thing it was actually needed for -- beta-reducing a
    -- `(fun b => match …) b` arm so `split` can see the match -- definitionally.
    | (simp at h)
    | (exact runRegex_cap _ _ _ _ _ _ h)
    | (exact runModules_cap _ _ _ _ _ _ h)
    | (exact runCollections_cap _ _ _ _ _ _ h)
    | (exact runStrings_cap _ _ _ _ _ _ h)
    | (exact runNumerics_cap _ _ _ _ _ _ h)
    | (exact runObjects_cap _ _ _ _ _ _ h))))



set_option hygiene false in
macro "cap_arms_rx" : tactic => `(tactic|
  repeat (any_goals (first
    | (cases h; cap_leaf_rx)
    | (obtain ⟨-, rfl⟩ := h; cap_leaf_rx)
    | (dsimp only at h)
    | (unfold Builtins.withIndex at h)
    | split at h
    | (exact putsImpl_cap _ _ _ _ h)
    | (exact regexApply_cap _ _ _ _ _ _ h)
    | (exact scanAll_cap _ _ _ _ _ _ _ h)
    | (exact splitBy_cap _ _ _ _ _ _ _ _ h)
    | (exact splitOn_cap _ _ _ _ _ _ _ _ h)
    | (exact subst_cap _ _ _ _ _ _ _ _ _ _ h)
    | (exact (setMatchGlobals_cap _ _).trans (splitOn_cap _ _ _ _ _ _ _ _ h))
    | (exact (setMatchGlobals_cap _ _).trans (splitBy_cap _ _ _ _ _ _ _ _ h))
    | (exact ((allocMData_cap _ _ _ _ _).trans
        (setMatchGlobals_cap _ _)).trans (runRegex_cap _ _ _ _ _ _ h))
    | (exact newImpl_cap _ _ _ _ _ h)
        | (simp at h)
    | split at h
    | (unfold Builtins.numBin at h)
    | (unfold Builtins.okStrFrom at h)
    | (unfold Builtins.binArg at h)
    | (unfold Builtins.frozenErr at h)
    | (unfold Builtins.coerceFailed at h)
    | (unfold Builtins.floatToInt at h)
    | (unfold Builtins.raiseImpl at h)
    | (unfold Builtins.raiseClass at h)
    | (unfold Builtins.intBitRef at h)
    | (unfold Builtins.numCmp at h)
    | (unfold Builtins.sortImpl at h)
    | (unfold Builtins.joinImpl at h)
    | (unfold Builtins.okStr at h)
    | (unfold Builtins.okStrEnc at h)
    | (unfold Builtins.allocStr at h)
    | (unfold Builtins.allocStrEnc at h)
    | (unfold Builtins.allocArr at h)
    | (unfold Builtins.allocHsh at h)
    | (unfold Builtins.allocExc at h)
    | (unfold Builtins.dupObj at h)
    -- `simp at h` **last**: on an arithmetic arm it tries to evaluate `Int`/`Float` literals,
    -- which took `runNumerics` to a 14 GB proof term that never finished. `dsimp only at h`
    -- above does the one thing it was actually needed for -- beta-reducing a
    -- `(fun b => match …) b` arm so `split` can see the match -- definitionally.
    | (simp at h)
    | (exact runRegex_cap _ _ _ _ _ _ h)
    | (exact runModules_cap _ _ _ _ _ _ h)
    | (exact runCollections_cap _ _ _ _ _ _ h)
    | (exact runStrings_cap _ _ _ _ _ _ h)
    | (exact runNumerics_cap _ _ _ _ _ _ h)
    | (exact runObjects_cap _ _ _ _ _ _ h))))



set_option hygiene false in
macro "cap_arms_mod" : tactic => `(tactic|
  repeat (any_goals (first
    | (cases h; cap_leaf_mod)
    | (obtain ⟨-, rfl⟩ := h; cap_leaf_mod)
    | (dsimp only at h)
    | (unfold Builtins.withIndex at h)
    | split at h
    | (exact putsImpl_cap _ _ _ _ h)
    | (exact regexApply_cap _ _ _ _ _ _ h)
    | (exact scanAll_cap _ _ _ _ _ _ _ h)
    | (exact splitBy_cap _ _ _ _ _ _ _ _ h)
    | (exact splitOn_cap _ _ _ _ _ _ _ _ h)
    | (exact subst_cap _ _ _ _ _ _ _ _ _ _ h)
    | (exact (setMatchGlobals_cap _ _).trans (splitOn_cap _ _ _ _ _ _ _ _ h))
    | (exact (setMatchGlobals_cap _ _).trans (splitBy_cap _ _ _ _ _ _ _ _ h))
    | (exact ((allocMData_cap _ _ _ _ _).trans
        (setMatchGlobals_cap _ _)).trans (runRegex_cap _ _ _ _ _ _ h))
    | (exact newImpl_cap _ _ _ _ _ h)
        | (simp at h)
    | split at h
    | (unfold Builtins.numBin at h)
    | (unfold Builtins.okStrFrom at h)
    | (unfold Builtins.binArg at h)
    | (unfold Builtins.frozenErr at h)
    | (unfold Builtins.coerceFailed at h)
    | (unfold Builtins.floatToInt at h)
    | (unfold Builtins.raiseImpl at h)
    | (unfold Builtins.raiseClass at h)
    | (unfold Builtins.intBitRef at h)
    | (unfold Builtins.numCmp at h)
    | (unfold Builtins.sortImpl at h)
    | (unfold Builtins.joinImpl at h)
    | (unfold Builtins.okStr at h)
    | (unfold Builtins.okStrEnc at h)
    | (unfold Builtins.allocStr at h)
    | (unfold Builtins.allocStrEnc at h)
    | (unfold Builtins.allocArr at h)
    | (unfold Builtins.allocHsh at h)
    | (unfold Builtins.allocExc at h)
    | (unfold Builtins.dupObj at h)
    -- `simp at h` **last**: on an arithmetic arm it tries to evaluate `Int`/`Float` literals,
    -- which took `runNumerics` to a 14 GB proof term that never finished. `dsimp only at h`
    -- above does the one thing it was actually needed for -- beta-reducing a
    -- `(fun b => match …) b` arm so `split` can see the match -- definitionally.
    | (simp at h)
    | (exact runRegex_cap _ _ _ _ _ _ h)
    | (exact runModules_cap _ _ _ _ _ _ h)
    | (exact runCollections_cap _ _ _ _ _ _ h)
    | (exact runStrings_cap _ _ _ _ _ _ h)
    | (exact runNumerics_cap _ _ _ _ _ _ h)
    | (exact runObjects_cap _ _ _ _ _ _ h))))



set_option hygiene false in
macro "cap_arms_obj" : tactic => `(tactic|
  repeat (any_goals (first
    | (cases h; cap_leaf_obj)
    | (obtain ⟨-, rfl⟩ := h; cap_leaf_obj)
    | (dsimp only at h)
    | (unfold Builtins.withIndex at h)
    | split at h
    | (exact putsImpl_cap _ _ _ _ h)
    | (exact regexApply_cap _ _ _ _ _ _ h)
    | (exact scanAll_cap _ _ _ _ _ _ _ h)
    | (exact splitBy_cap _ _ _ _ _ _ _ _ h)
    | (exact splitOn_cap _ _ _ _ _ _ _ _ h)
    | (exact subst_cap _ _ _ _ _ _ _ _ _ _ h)
    | (exact (setMatchGlobals_cap _ _).trans (splitOn_cap _ _ _ _ _ _ _ _ h))
    | (exact (setMatchGlobals_cap _ _).trans (splitBy_cap _ _ _ _ _ _ _ _ h))
    | (exact ((allocMData_cap _ _ _ _ _).trans
        (setMatchGlobals_cap _ _)).trans (runRegex_cap _ _ _ _ _ _ h))
    | (exact newImpl_cap _ _ _ _ _ h)
        | (simp at h)
    | split at h
    | (unfold Builtins.numBin at h)
    | (unfold Builtins.okStrFrom at h)
    | (unfold Builtins.binArg at h)
    | (unfold Builtins.frozenErr at h)
    | (unfold Builtins.coerceFailed at h)
    | (unfold Builtins.floatToInt at h)
    | (unfold Builtins.raiseImpl at h)
    | (unfold Builtins.raiseClass at h)
    | (unfold Builtins.intBitRef at h)
    | (unfold Builtins.numCmp at h)
    | (unfold Builtins.sortImpl at h)
    | (unfold Builtins.joinImpl at h)
    | (unfold Builtins.okStr at h)
    | (unfold Builtins.okStrEnc at h)
    | (unfold Builtins.allocStr at h)
    | (unfold Builtins.allocStrEnc at h)
    | (unfold Builtins.allocArr at h)
    | (unfold Builtins.allocHsh at h)
    | (unfold Builtins.allocExc at h)
    | (unfold Builtins.dupObj at h)
    -- `simp at h` **last**: on an arithmetic arm it tries to evaluate `Int`/`Float` literals,
    -- which took `runNumerics` to a 14 GB proof term that never finished. `dsimp only at h`
    -- above does the one thing it was actually needed for -- beta-reducing a
    -- `(fun b => match …) b` arm so `split` can see the match -- definitionally.
    | (simp at h)
    | (exact runRegex_cap _ _ _ _ _ _ h)
    | (exact runModules_cap _ _ _ _ _ _ h)
    | (exact runCollections_cap _ _ _ _ _ _ h)
    | (exact runStrings_cap _ _ _ _ _ _ h)
    | (exact runNumerics_cap _ _ _ _ _ _ h)
    | (exact runObjects_cap _ _ _ _ _ _ h))))


end Ratchet.Denote
