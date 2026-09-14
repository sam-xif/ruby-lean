import Ratchet.Ty
import Denote.Ext

/-!
# `Denote/Den.lean` — the semantic denotation of `Ratchet.Ty`

**What a type *means*, as a predicate over the real machine.** `Ratchet/Judge.lean` says
what the checker *derives*; this file says what those derivations would have to be *about*
for them to be true. Nothing here mentions `Judge`, `chk` or a rung: the denotation is a
statement about `RubyCore`'s `Heap`/`Value`/`Machine` and about `Ty`, and the two are
related only by this file's own recursion.

This replaces, and generalises, `CheckRungs.lean`'s `expectedClasses` — a `Ty → List String`
that reads a type as "the set of class names its values can have". That was enough to pin
thirteen rungs and it is structurally unable to say more: it cannot look inside an array, it
cannot look at an ivar, and it cannot say anything at all about a Proc. Its own docstrings
say so, three times. A denotation that recurses is what closes those three gaps.

## Shape

The user-facing shape is `Ty → Heap → Value → Prop` (and, computably, `→ Bool` — see
`Denote/DenB.lean`), and for every **first-order** type that is exactly the shape:
`denM_heap_only` proves the machine argument is irrelevant whenever the type is arrow- and
`clos`-free. The master definition is nevertheless machine-indexed, for one reason recorded
at length in `Denote/Apply.lean`: `Closure.captured` is a `FrameId`, so a closure's captured
environment is not in the heap and cannot be recovered from one.

Three mutually recursive functions:

* `denM τ m v` — the denotation proper.
* `denApp acc τ m f` — the arrow spine walk: gathers one argument per `arrowCons` and, at
  the `arrow0`, states the obligation about the call.
* `denSpine τ m get` — a **binding spine** (`ivar0`/`ivarCons`), read through an arbitrary
  `String → Value`. One function for both of `Ty`'s uses of the spine: an object's ivars
  (`ivarOf`) and a closure's captured locals (`closLocal`).

## The arrow arm, which is the point of the exercise

`(A, B) → R` at machine `m`, applied to value `f`, means:

> `f` is a Proc, **and** for every machine `m₂` that `m` could have *run on to* without
> pushing or popping a frame (`Later`, `Denote/Ext.lean`), for every `a : A` and `b : B` at
> `m₂`, if calling
> `f.call(a, b)` from `m₂` returns a value `v` in machine `m'`, then `v : R` **at `m'`**.

Five things are load-bearing in that sentence.

1. **Only about runs that return.** A proc that raises, diverges, hits `.unsupported`, or
   jumps (`break` out of a dead home frame) imposes no obligation. This is a partial-
   correctness reading, and it is the only sound one available: `Ty` has no effect or
   totality discipline to say otherwise, and `Ratchet.Ty.never` — the type of an expression
   that *does not return* — is defined by that same asymmetry.
2. **The codomain is checked at `m'`, not at `m`.** Calling the proc can allocate, mutate,
   reopen a class or `define_method`. The result's type is a claim about the heap the call
   actually produced. Checking it at `m` would be checking it against a heap that no longer
   exists.
3. **The domain is checked at `m`.** The caller has to supply arguments that are in the
   domain *before* the call, so that is where the hypothesis is discharged.
4. **Contravariance falls out** rather than being stipulated: the domain is a hypothesis and
   the codomain a conclusion, so `subTy`-style variance is a theorem about this definition,
   not a rule inside it.

5. **The `∀ m₂, Later m m₂` quantifier, and why it is not decoration.** Every other arm of
   this denotation reads the heap; the arrow arm reads *runs*, and a run from a heap with one
   more object in it allocates at shifted object ids, so it is not the run from the heap
   without it. Stated at `m` alone, the arrow is therefore the one arm of `denM` that does
   **not** survive an allocation — which stalled the semantic ratchet at its third literal
   (`Denote/Sem/notes.md` §The fourth stall point: a string literal allocates, and
   re-establishing `EnvOk` across the push means transporting `denM τ` for an arbitrary
   `τ`). Quantifying over `Ext`-futures makes the arrow monotone *by construction*
   (`Ext.trans`), which is what `denM_ext` below needs and what nothing weaker supplies.
   Taking `m₂ := m` (`Ext.refl`) recovers the unquantified reading, so this is a
   strengthening: an arrow that holds here holds there.

`ArrowStable` below strengthens 2/3/5 further, across arbitrary *execution*: a
proc is typically called from a state the program has run on to, so the fully honest claim
quantifies over every machine reachable from the one where the arrow was established, and
`Reaches` (`Denote/Apply.lean`) is that quantifier. `Later` is deliberately the weaker of the
two: it is blind to `ctl`/`kont`, which is what keeps `Denote/Rules/Core.lean`'s `denM_ctl`
true (the conflict `Denote/Sem/notes.md` recorded against seeding the arrow with `Reaches`
directly), and it forbids a frame push, which is the clause the first call rung will have to
spend. It is `ArrowStable` approximated from below, one step kind per rung that needs it.

## Two stated gaps

* **`Ty.clos`'s `idx`** indexes the *checker's* syntactic closure table, which `Denote/` does
  not import (and could not compare against, since `Ratchet.Expr` and `RubyCore.Expr` are
  two separately-copied inductives — see `Denote/notes.md`). So the `clos` arm denotes the
  nominal-plus-environment part (a Proc whose captured scope and `self` match the spine) and
  drops `idx`. The behavioural content of a `clos` is available *via the arrow*: that is what
  the arrow arm is for, and `closArrow` states the bridge a future `Judge.closCall`-soundness
  proof would need.
* **`Ty.clos`'s `selfTy` uses `.never` as a sentinel** for "created where `self` was not
  typed" (top level) rather than as the bottom type. Since `denM .never` is `False`, that arm
  is special-cased to impose no constraint, and the special case is written out rather than
  inherited.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

mutual

/-- **The denotation**: which machine values inhabit `τ`, at machine `m`. -/
def denM : Ty → Machine → Value → Prop
  | .int, _, v => isIntV v = true
  | .bool, _, v => isBoolV v = true
  | .nilT, _, v => isNilV v = true
  | .sym, _, v => isSymV v = true
  | .float, _, v => isFltV v = true
  -- The top type: no constraint. `Ty.any`'s docstring calls it "some value, of a type the
  -- checker does not pin", and `True` is precisely that.
  | .any, _, _ => True
  -- The bottom type: no value inhabits it. This is what makes `Ty.never`'s three jobs
  -- (`Ty.never`'s docstring) one job: an expression typed `.never` produces no value, so any
  -- claim downstream of it is vacuous.
  | .never, _, _ => False
  -- Nominal, and heap-indexed: the machine's own ancestors walk at the class the *name*
  -- resolves to in this heap. So `.cls "Foo"` is inhabited by instances of subclasses of
  -- `Foo` too, matching `is_a?` and matching what a checked program can actually observe.
  | .cls n, m, v => isAName m.heap v n = true
  | .clsOf n, m, v => isClassRefNamed m.heap v n = true
  | .nilable τ, m, v => isNilV v = true ∨ denM τ m v
  | .union σ τ, m, v => denM σ m v ∨ denM τ m v
  -- Parameterised, and *elementwise*: the type says every element is in `elem`, so the
  -- denotation quantifies over the payload. This is the first thing `expectedClasses` could
  -- not say. Note `arrayOf .never` is inhabited by exactly the empty arrays, which is what
  -- `Ty.arrayOf`'s "provably empty" reading claims.
  | .arrayOf e, m, v => ∃ xs, arrElems? m.heap v = some xs ∧ ∀ x ∈ xs, denM e m x
  | .hashOf k w, m, v =>
      ∃ es, hshEntries? m.heap v = some es ∧
        ∀ p ∈ es, denM k m p.1 ∧ denM w m p.2
  -- A user-class instance: nominal on the class *plus* the ivar spine read out of the
  -- object. The spine is a lower bound — ivars the type does not mention are unconstrained,
  -- which is what makes `ivarSet`'s append-at-the-end growth monotone in the denotation.
  --
  -- The class part is **exact**, not is-a (`found-issues.md` §F12, `isExactInst`): every rule
  -- that dispatches on an `.inst n` receiver types the callee's body out of `n`'s own table,
  -- and an is-a reading would admit a subclass that redefined it. `Ty.cls` keeps the is-a
  -- reading, because `rescueBind?` needs it and §F11 guards what dispatches on it.
  | .inst n I, m, v => isExactInst m.heap v n = true ∧ denSpineFrom [] I m (ivarOf m.heap v)
  -- `sameAs` is a fact about a *binding*, not about a value (`Ty.sameAs`'s docstring), and
  -- `Judge.var` strips it. So the denotation reads straight through the alias: the values
  -- are the values of the underlying type.
  | .sameAs _ τ, m, v => denM τ m v
  -- Spines are not value types. `False` rather than `True`: no expression has type `ivar0`,
  -- and a denotation that admitted every value here would silently validate a type error.
  | .ivar0, _, _ => False
  | .ivarCons .., _, _ => False
  -- The arrow (see the module docstring §The arrow arm).
  | .arrow0 r, m, f =>
      isProcV m.heap f = true ∧
        ∀ m₂, Later m m₂ → ∀ v m', Returns m₂ f [] v m' → denM r m' v
  | .arrowCons p rest, m, f =>
      isProcV m.heap f = true ∧
        ∀ m₂, Later m m₂ → ∀ a, denM p m₂ a → denApp [a] rest m₂ f
  -- A callable value, nominally: a Proc whose captured scope and `self` match what the type
  -- recorded at its creation. `idx` is dropped; see the module docstring §Two stated gaps.
  | .clos _ cap selfT, m, f =>
      ∃ cl, procClosure? m.heap f = some cl ∧
        denSpineFrom [] cap m (closLocal m cl) ∧
        (selfT = .never ∨ denM selfT m (closSelf m cl))
termination_by τ _ _ => sizeOf τ

/-- The arrow spine walk. `acc` is the argument list gathered so far, in call order. -/
def denApp : List Value → Ty → Machine → Value → Prop
  | acc, .arrow0 r, m, f => ∀ v m', Returns m f acc v m' → denM r m' v
  | acc, .arrowCons p rest, m, f => ∀ a, denM p m a → denApp (acc ++ [a]) rest m f
  -- A malformed spine (`arrowCons` over a non-arrow tail) denotes nothing. `arrowParts?`
  -- already answers `none` on those; this is the same judgement one level down.
  | _, _, _, _ => False
termination_by _ τ _ _ => sizeOf τ

/-- A binding spine, read through `get`, **at the keys the spine actually resolves**.
`ivar0` is the empty spine and so is vacuously satisfied; anything that is not a spine is not
one; and an entry whose key an *earlier* entry already bound is skipped, which is the whole
content of the `seen` accumulator.

**Why the accumulator** (`Denote/Sem/notes.md` §The tenth stall point). Every consumer of a
spine reads it through `ivarGet?`, which answers with the **first** match — and the checker
really does build spines with a repeated key: `Judge.closCall` types a lambda's body in
`paramEnv c.params argTys ++ spineToEnv cap`, so a parameter shadowing a captured local is a
duplicate by design, and `envToSpine` of that environment carries both entries. Without the
accumulator the denotation demands that the *shadowed* entry hold too, which is false of the
machine and makes `StateOk` unsatisfiable at any machine holding such a closure — vacuity, not
falsity, which is the failure mode `Denote/Sanity.lean` exists to police. Demonstrated:

```ruby
x = 1
f = lambda { |x| lambda { x } }
g = f.call("s")
g              # validate: <closure#1>{x: String, x: Integer} -- and it is right
```

`seen` rather than a `dedup : Ty → Ty` applied at the two call sites, and that is a proof
consideration rather than a taste one: `dedup cap` is not a *subterm* of the type, so every
one of the four transports (`denM_heap_only_aux`, `denM_ctl`, `denM_ext`, `denM_setLocal`)
would have had to become a well-founded induction on `sizeOf`. With the accumulator the
recursion stays structural and each transport carries one extra `∀ seen`. -/
def denSpineFrom : List String → Ty → Machine → (String → Value) → Prop
  | _, .ivar0, _, _ => True
  | seen, .ivarCons x σ rest, m, get =>
      (x ∈ seen ∨ denM σ m (get x)) ∧ denSpineFrom (x :: seen) rest m get
  | _, _, _, _ => False
termination_by _ τ _ _ => sizeOf τ

end

/-- A binding spine, read through `get`: `denSpineFrom` with nothing yet shadowed. The form
every rule and every component states, and the form `denM`'s two spine arms are defined at. -/
def denSpine (τ : Ty) (m : Machine) (get : String → Value) : Prop := denSpineFrom [] τ m get

@[simp] theorem denSpine_ivar0 (m : Machine) (g : String → Value) :
    denSpine .ivar0 m g := by simp [denSpine, denSpineFrom]

theorem denSpine_cons {x : String} {σ rest : Ty} {m : Machine} {g : String → Value} :
    denSpine (.ivarCons x σ rest) m g ↔ denM σ m (g x) ∧ denSpineFrom [x] rest m g := by
  simp only [denSpine, denSpineFrom, List.not_mem_nil, false_or]

/-! ## The heap-only view

`den` is the shape the design note asked for: `Ty → Heap → Value → Prop`. It is `denM` at a
**fresh** machine on that heap — one toplevel frame, no program. For a first-order type that
is exactly `denM` (`denM_heap_only`); for an arrow or a `clos` it is *a* reading rather than
*the* reading, because a fresh machine has no frames for a closure to have captured. -/

/-- `denM` at a bare machine over `h`. -/
def den (τ : Ty) (h : Heap) (v : Value) : Prop := denM τ (Machine.initOn h .nil) v

/-- **The machine is irrelevant for a first-order type.** Two machines with the same heap
agree on every arrow-free, `clos`-free type — so for that whole fragment `denM` really is the
`Ty → Heap → Value → Prop` the design note asked for, and `den` loses nothing.

Proved simultaneously with the spine statement (they are mutually recursive, so the induction
has to carry both), by structural induction on the type. -/
theorem denM_heap_only_aux : ∀ (τ : Ty), FirstOrder τ = true →
    (∀ (m₁ m₂ : Machine) (v : Value), m₁.heap = m₂.heap → (denM τ m₁ v ↔ denM τ m₂ v)) ∧
    (∀ (m₁ m₂ : Machine) (g : String → Value) (seen : List String), m₁.heap = m₂.heap →
      (denSpineFrom seen τ m₁ g ↔ denSpineFrom seen τ m₂ g)) := by
  intro τ
  induction τ with
  | int | bool | nilT | sym | float | any | never | ivar0 =>
    intro _; exact ⟨fun _ _ _ _ => by simp [denM], fun _ _ _ _ _ => by simp [denSpineFrom]⟩
  | cls n => intro _; exact ⟨fun _ _ _ hh => by simp [denM, hh], fun _ _ _ _ _ => by simp [denSpineFrom]⟩
  | clsOf n => intro _; exact ⟨fun _ _ _ hh => by simp [denM, hh], fun _ _ _ _ _ => by simp [denSpineFrom]⟩
  | nilable τ ih =>
    intro hf
    simp only [FirstOrder] at hf
    exact ⟨fun m₁ m₂ v hh => by simp only [denM]; rw [(ih hf).1 m₁ m₂ v hh],
           fun _ _ _ _ _ => by simp [denSpineFrom]⟩
  | union σ τ ihσ ihτ =>
    intro hf
    simp only [FirstOrder, Bool.and_eq_true] at hf
    exact ⟨fun m₁ m₂ v hh => by
             simp only [denM]; rw [(ihσ hf.1).1 m₁ m₂ v hh, (ihτ hf.2).1 m₁ m₂ v hh],
           fun _ _ _ _ _ => by simp [denSpineFrom]⟩
  | sameAs n τ ih =>
    intro hf
    simp only [FirstOrder] at hf
    exact ⟨fun m₁ m₂ v hh => by simp only [denM]; rw [(ih hf).1 m₁ m₂ v hh],
           fun _ _ _ _ _ => by simp [denSpineFrom]⟩
  | arrayOf e ih =>
    intro hf
    simp only [FirstOrder] at hf
    refine ⟨fun m₁ m₂ v hh => ?_, fun _ _ _ _ _ => by simp [denSpineFrom]⟩
    simp only [denM, hh]
    exact exists_congr fun xs => and_congr_right fun _ =>
      forall_congr' fun x => imp_congr_right fun _ => (ih hf).1 m₁ m₂ x hh
  | hashOf k w ihk ihw =>
    intro hf
    simp only [FirstOrder, Bool.and_eq_true] at hf
    refine ⟨fun m₁ m₂ v hh => ?_, fun _ _ _ _ _ => by simp [denSpineFrom]⟩
    simp only [denM, hh]
    exact exists_congr fun es => and_congr_right fun _ =>
      forall_congr' fun p => imp_congr_right fun _ =>
        and_congr ((ihk hf.1).1 m₁ m₂ p.1 hh) ((ihw hf.2).1 m₁ m₂ p.2 hh)
  | inst n I ih =>
    intro hf
    simp only [FirstOrder] at hf
    refine ⟨fun m₁ m₂ v hh => ?_, fun _ _ _ _ _ => by simp [denSpineFrom]⟩
    simp only [denM, hh]
    exact and_congr_right fun _ => (ih hf).2 m₁ m₂ (ivarOf m₂.heap v) [] hh
  | ivarCons x σ rest ihσ ihrest =>
    intro hf
    simp only [FirstOrder, Bool.and_eq_true] at hf
    refine ⟨fun _ _ _ _ => by simp [denM], fun m₁ m₂ g seen hh => ?_⟩
    simp only [denSpineFrom]
    exact and_congr (or_congr_right ((ihσ hf.1).1 m₁ m₂ (g x) hh))
      ((ihrest hf.2).2 m₁ m₂ g (x :: seen) hh)
  -- The three higher-order arms are excluded by `FirstOrder`, so the hypothesis is absurd.
  | arrow0 r _ => intro hf; simp [FirstOrder] at hf
  | arrowCons p rest _ _ => intro hf; simp [FirstOrder] at hf
  | clos i cap st _ _ => intro hf; simp [FirstOrder] at hf

theorem denM_heap_only {τ : Ty} (hf : FirstOrder τ = true) {m₁ m₂ : Machine} {v : Value}
    (hh : m₁.heap = m₂.heap) : denM τ m₁ v ↔ denM τ m₂ v :=
  (denM_heap_only_aux τ hf).1 m₁ m₂ v hh

/-- The payoff: on the first-order fragment, `den` (heap-only) *is* `denM` (machine-indexed).
`Machine.initOn h .nil` has heap `h`, so this is `denM_heap_only` at a specific pair. -/
theorem den_iff_denM {τ : Ty} (hf : FirstOrder τ = true) (m : Machine) (v : Value) :
    den τ m.heap v ↔ denM τ m v :=
  denM_heap_only hf rfl

#print axioms denM_heap_only
#print axioms den_iff_denM

end Ratchet.Denote
