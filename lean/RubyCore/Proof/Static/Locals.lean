import RubyCore.Proof.BuiltinConformance
import RubyCore.Proof.HeapFacts
import RubyCore.Proof.HeapGrow
import RubyCore.Types.Core

/-!
# P0 static soundness, part 1 — values, frames and environments

Split out of `Proof/StaticSoundness.lean` (L136), which had reached 971 lines
against `PLAN.md` §4 norm 3's 1,000-line ceiling with F1 about to add to it. No
statement changed; the cut follows the file's own section numbering, and
`StaticSoundness.lean` still holds the theorem, so nothing downstream moved.

This part is §1: what it means for a *value* to have a type, for one activation
to conform to one environment, and for the whole activation stack to conform to a
stack of environments — plus the array and environment algebra those need.
-/

namespace RubyCore
namespace Proof
namespace Static

open Interp
open RubyCore.Types

-- The boot-heap `rfl`s of `tableOk_initHeap` walk the whole method table.
set_option maxRecDepth 100000

/-! ## 1. Values and locals -/

/-- **A receiver `invoke` dispatches uniformly.** The three receiver *shapes*
    `invoke` special-cases before it ever consults the resolved builtin
    (`Interp/Send.lean:33–92`) are all `.ref`s, and each is recognised by the
    object's payload: a `.proc` answers `call`/`()`/`[]`/`yield` by running its
    closure, a `.hsh` with a `prc` default answers `[]` by running that, and a
    `.cls` reaches `invokeMaybeNew` (or the `Math`/`Regexp` singleton arms, both of
    which are class objects). Everything else falls through to `invokeDispatch`,
    which is the path `ResolvesTo` describes.

    `eigen = none` is here for a different reason: dispatch resolves through
    `classOf`, which *is* the eigenclass when there is one, so an object with a
    singleton method would have its declarations read off a class other than the
    one the type names. Excluding it keeps the key and the dispatch class the same
    object — the same hypothesis `Proof/T5.lean`'s `dispatch_progress` carries as
    `heigen`.

    **This is a refusal, not an approximation.** A Proc, a Hash and a class object
    simply have no type in this rung; nothing unsound follows from a value having
    no type, only that no call on it can be checked.

    **`o < h.objs.size` is the producer rung's clause, and it repairs a latent
    defect rather than merely preparing for one.** `Heap.get` answers an
    out-of-bounds id with `default`, whose `klass` is `0`, whose `eigen` is `none`
    and whose payload is `.none` — so without this bound *every unallocated id is
    a plain receiver*, and L141's `.ref` arm gave it the type
    `.cls "BasicObject"`. Measured, not reasoned: at the boot heap
    `valueTy? h (.ref 40) = some (.cls "BasicObject")` with `h.objs.size = 40`.

    Nothing observes that today, because nothing constructs a class-typed value
    and every `baseDecls` row is at a ground type. What it *blocks* is the
    producer: `alloc` turns id `n` from `.cls "BasicObject"` into `.cls C`, which
    refutes `TypeAgree`'s first clause at the fresh id — so the transport
    condition is **false for any allocating step**, before any question of
    `ancestors_congr`'s fuel arises. With the bound, `ValueTy` implies the value
    is in bounds (`valueTy_ref_lt`), which is what lets the transport be
    relativized to ids the old heap actually had, and `alloc` satisfies *that*
    definitionally.

    The move is L141's own: a side condition the use site would have to derive
    goes into the judgement instead.

    **`(h.get o).klass < h.objs.size` is the same move a second time, and it is
    what the relativized `TypeAgree` needs** (L143). The `.ref` arm's type is
    `className h (classOf h (.ref o))`, so the transport owes an agreement about
    the *class* id as well as about `o`, and `className` is another function that
    answers out of bounds with a default (`"Object"`). Without this clause an
    object whose `klass` is the id an `alloc` is about to hand out changes type
    when that id becomes a class — `.cls "Object"` before, `.cls C` after — which
    is L142's defect one indirection along, and it is why relativizing the
    transport to `o < h.objs.size` alone is not enough.

    A heap where an object's class does not exist is not one any rule builds; this
    refuses to *type* its objects rather than asserting it cannot arise, which is
    the same trade the bound above makes.

    **L147 strengthens that clause from a bound to `(h.classPayload? klass).isSome`
    and subsumes it** — `classPayload?` answers `none` out of bounds, so being a
    class *implies* being in bounds (`plainRecv_klass_lt`). It is the same move a
    third time, and the third time is where the pattern is worth naming: every one of
    these clauses was found by asking what a *later* rung has to derive at the use
    site, and every one of them is cheaper in the judgement. Here the use site is
    `EntryOk`'s class-indexed resolution clause (L147), which is instantiated at the
    receiver's dispatch class and therefore needs that class to *be* a class. -/
def plainRecv (h : Heap) (o : ObjId) : Bool :=
  o < h.objs.size && (h.classPayload? (h.get o).klass).isSome && (h.get o).eigen.isNone &&
    -- **Not frozen** (L191), and it is `plainRecv`'s fifth clause for the fifth time
    -- the same reason: *a side condition a later rung has to derive at the use site
    -- is cheaper in the judgement.* The use site is `@x = e`, whose `applyKont` arm
    -- raises `FrozenError` — a `.jump`, which `CtlOk` refuses outright — when the
    -- frame's `self` is frozen (`Interp/Kont.lean:35`). Immediates are frozen too,
    -- which is why the rule needs a `.ref` self and gets one from `StackCtx`'s
    -- `selfCls` clause.
    !(h.get o).frozen &&
    (match (h.get o).payload with
     | .proc _ => false
     | .hsh _ => false
     | .cls _ => false
     | _ => true)

/-- **A class-object receiver** (L185) — the shape `Ty.clsOf` types, and the dual
    of `plainRecv`: the payload *is* a class, and the two receiver ids `invoke`
    special-cases are excluded.

    The exclusions are `plainRecv`'s move a fourth time — *a side condition a later
    rung has to derive at the use site is cheaper in the judgement*. `invoke`
    intercepts a `.cls` receiver twice before it reaches `invokeDispatch`
    (`Interp/Send.lean:59`, `:69`): `Regexp.escape`/`.quote`/`.union` and the
    `Math.sqrt`/`exp`/`log` family are singleton methods dispatched by receiver
    **id**, because the boot heap installs builtins as *instance* methods and those
    are not (L106). Refusing the two ids here is what lets `entry_dispatch`'s class
    case be a `simp` rather than a case analysis over arms it must then refute.

    `eigen` is deliberately **not** constrained, unlike `plainRecv`'s `eigen.isNone`:
    a class object legitimately has one — 27 of the booted heap's 87 do
    (`scripts/classobj_probe.lean`) — and its presence is exactly what `classOf`
    reads. That is why the type is keyed on the class's *own* name while `TyClass`
    names `classOf`'s answer; L180 measured that the two cannot be the same
    string. -/
def classRecv (h : Heap) (o : ObjId) : Bool :=
  o < h.objs.size && o != Boot.regexpId && o != Boot.mathId &&
    (h.classPayload? o).isSome

/-- The type of a value **in a heap**, where P0 has one. `.flt` has none — the
    fragment has no Float type — and a `.ref` has one exactly when it is a
    receiver `invoke` dispatches uniformly (`plainRecv`).

    **Heap-indexed since L137, and the `.ref` arm is the first arm to use it**
    (F1b/T2). L137's note said a nominal class type "can only say what class a
    `.ref` belongs to by consulting `classOf`/`className`, so the *judgement* has
    to be heap-relative before the *type language* can grow", and this is that
    prediction cashed: the arm is `className ∘ classOf`, and the cost of the
    threading lands in §1.5's congruence lemmas exactly where it was predicted to.

    `classOf` rather than `realClassOf` because dispatch uses `classOf`, and
    `plainRecv` makes them equal anyway — the type must name the class the method
    table is actually walked from, not the one `Object#class` reports. -/
def valueTy? (h : Heap) : Value → Option Ty
  | .int _ => some .int
  | .bool _ => some .bool
  | .nil => some .nilT
  -- `def` evaluates to the method name (`Interp.lean:2624`).
  | .sym _ => some .sym
  | .ref o =>
    if plainRecv h o then some (.cls (className h (classOf h (.ref o))))
    -- **L185's class-object arm.** Keyed on the object's *own* name, not on
    -- `classOf`'s: a class object's dispatch chain is its eigenclass, or `Class`
    -- when it has none, and neither of those names is one a declaration can hang
    -- off (L180). `TyClass` is where `classOf` appears.
    else if classRecv h o then some (.clsOf (className h o))
    else none
  | _ => none

/-- **The value judgement, and since L193 it is a *relation*** — `v`'s exact type
    (which `valueTy?` still computes, unchanged) is *below* `τ`.

    L183 wrote down this design and declined it, and the reason it is here now is
    `Ty.nilable`: a `String` reference has to satisfy both `.cls "String"` and
    `.nilable (.cls "String")`, which no function from values to types can express.
    Every inversion below still recovers the exact type, because `subTy_atomic`
    says `subTy σ τ` *is* `σ = τ` at every arm but `.any` and `.nilable` — so the
    weakening is inert everywhere the old definition was used and is the whole
    content of the rung exactly where a join happens. -/
def ValueTy (h : Heap) (v : Value) (τ : Ty) : Prop :=
  ∃ σ, valueTy? h v = some σ ∧ subTy σ τ = true

/-- The exact-type constructor, which is what every producer rule has. -/
theorem ValueTy.exact {h : Heap} {v : Value} {τ : Ty} (he : valueTy? h v = some τ) :
    ValueTy h v τ := ⟨τ, he, by simp⟩

/-- And the weakening the join needs, which is one `subTy_trans`. -/
theorem ValueTy.weaken {h : Heap} {v : Value} {σ τ : Ty} (hv : ValueTy h v σ)
    (hs : subTy σ τ = true) : ValueTy h v τ :=
  ⟨hv.choose, hv.choose_spec.1, subTy_trans hv.choose_spec.2 hs⟩

/-- Inversion at an **atomic** type: the exact type is the declared one, which is
    what keeps every pre-L193 consumer working. -/
theorem ValueTy.atomic {h : Heap} {v : Value} {τ : Ty} (ha : τ ≠ .any)
    (hn : ∀ τ', τ ≠ .nilable τ') (hv : ValueTy h v τ) : valueTy? h v = some τ := by
  obtain ⟨σ, hσ, hs⟩ := hv
  rw [(subTy_atomic ha hn).mp hs] at hσ
  exact hσ

/-- **The `.ref` arm, read backwards** (L185). Two branches now, so the inversion
    is a disjunction and every consumer has to say which one it is about —
    `Locals.lean`'s own lesson from L142 applies to itself here: *an inversion
    principle is only as strong as the definition it inverts.* -/
theorem valueTy_ref_inv {h : Heap} {o : ObjId} {τ : Ty} (hv : ValueTy h (.ref o) τ) :
    (plainRecv h o = true ∧ subTy (.cls (className h (classOf h (.ref o)))) τ = true) ∨
      (classRecv h o = true ∧ subTy (.clsOf (className h o)) τ = true) := by
  obtain ⟨σ, hσ, hs⟩ := hv
  by_cases hp : plainRecv h o
  · refine Or.inl ⟨hp, ?_⟩
    rw [show σ = .cls (className h (classOf h (.ref o))) from by
      simpa [valueTy?, hp] using hσ.symm] at hs
    exact hs
  · by_cases hc : classRecv h o
    · refine Or.inr ⟨hc, ?_⟩
      rw [show σ = .clsOf (className h o) from by
        simpa [valueTy?, hp, hc] using hσ.symm] at hs
      exact hs
    · simp [valueTy?, hp, hc] at hσ

/-- Inversion at the `int` arm. Moved here from `Proof/Static/Konts.lean` in F1a:
    it is a fact about `ValueTy`, and `Proof/Static/Decls.lean` — which sits
    *below* `Konts.lean` now — needs it to build the base table's entries. -/
theorem valueTy_int {hp : Heap} {v : Value} (h : ValueTy hp v .int) : ∃ a, v = .int a := by
  cases v with
  | ref o =>
    exfalso
    rcases valueTy_ref_inv h with ⟨-, hne⟩ | ⟨-, hne⟩ <;>
      exact absurd hne (by simp [subTy])
  | _ => simp_all [ValueTy, valueTy?, subTy]

/-- **Every value with a type is an immediate or a plain ref.** F1a's version of
    this said *immediate*, full stop, and that was what let
    `Proof/Static/Decls.lean`'s `entry_dispatch` discharge `invoke`'s
    receiver-shape special cases for free — the fragment's own poverty doing the
    work of a proof (`HANDOFF.md` §F1b).

    **F1b pays that bill, and it turns out to be a case rather than an argument.**
    The `.ref` case is admitted with `plainRecv`, which is precisely the negation
    of the three special shapes, so the special cases are still closed — but now
    by a *hypothesis the type judgement carries* rather than by there being no
    inhabitant. That is the difference between the two rungs, and it is why
    `plainRecv` had to go into `valueTy?` rather than being assumed at the use
    site: an inversion principle is only as strong as the definition it inverts.

    **What did *not* come due, against expectation.** `HANDOFF.md` §F1b predicted
    this would want `crubySingletonShadow` back as a `ResolvesTo` clause. It does
    not: `invoke` consults that gate only on the `md.builtin = none` branch
    (`Interp/Send.lean:246`) and `ResolvesTo` pins `md.builtin = some bid`, so the
    F1a measurement survives an abstract `.ref` receiver unchanged. -/
theorem valueTy_shapes {h : Heap} {v : Value} {τ : Ty} (hv : ValueTy h v τ) :
    (∃ a, v = .int a) ∨ (∃ b, v = .bool b) ∨ v = .nil ∨ (∃ s, v = .sym s) ∨
      (∃ o, v = .ref o ∧ (plainRecv h o = true ∨ classRecv h o = true)) := by
  cases v with
  | ref o =>
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨o, Eq.refl _, ?_⟩)))
    rcases valueTy_ref_inv hv with ⟨hp, -⟩ | ⟨hc, -⟩
    · exact Or.inl hp
    · exact Or.inr hc
  | _ => simp_all [ValueTy, valueTy?]

/-- **A typed `.ref` is an id the heap actually has.** The point of `plainRecv`'s
    bound, isolated so that the transport lemmas can consume it without unfolding
    `valueTy?`: it is what will let `TypeAgree` be relativized to `< h.objs.size`
    and therefore hold across an `alloc`. -/
theorem valueTy_ref_lt {h : Heap} {o : ObjId} {τ : Ty} (hv : ValueTy h (.ref o) τ) :
    o < h.objs.size := by
  -- Both arms of the `.ref` case carry the bound: `plainRecv` as its first clause
  -- and `classRecv` as its first clause too (L185).
  by_cases hb : o < h.objs.size
  · exact hb
  · simp [ValueTy, valueTy?, plainRecv, classRecv, hb] at hv

/-- A `.ref` typed at a **class type** is a plain receiver — the old
    `valueTy_ref_plain`, restated at the arm it is about. -/
theorem valueTy_ref_plain {h : Heap} {o : ObjId} {n : String}
    (hv : ValueTy h (.ref o) (.cls n)) : plainRecv h o = true := by
  rcases valueTy_ref_inv hv with ⟨hp, -⟩ | ⟨-, hne⟩
  · exact hp
  · exact absurd hne (by simp [subTy])

/-- And a `.ref` typed at a **class-object type** is a class receiver. -/
theorem valueTy_ref_class {h : Heap} {o : ObjId} {n : String}
    (hv : ValueTy h (.ref o) (.clsOf n)) : classRecv h o = true := by
  rcases valueTy_ref_inv hv with ⟨-, hne⟩ | ⟨hc, -⟩
  · exact absurd hne (by simp [subTy])
  · exact hc

/-- **A plain receiver dispatches through its `klass` field.** `plainRecv`
    requires `eigen = none`, and that is the only case `classOf` distinguishes on
    a `.ref`. Isolated because the transport needs the *class* id, and needs it
    without unfolding `classOf` inside a `simp` set that is also rewriting
    `className`. -/
theorem plainRecv_classOf {h : Heap} {o : ObjId} (hp : plainRecv h o = true) :
    classOf h (.ref o) = (h.get o).klass := by
  unfold plainRecv at hp
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hp
  simp only [classOf, hp.1.1.2]

/-- **A plain receiver's class is a class** (L147). The clause `plainRecv` gained,
    read back out at the composite the resolution clause is indexed by. -/
theorem valueTy_ref_klass_isSome {h : Heap} {o : ObjId}
    (hp : plainRecv h o = true) : (h.classPayload? (classOf h (.ref o))).isSome := by
  rw [plainRecv_classOf hp]
  unfold plainRecv at hp
  simp only [Bool.and_eq_true] at hp
  exact hp.1.1.1.2

/-- **And therefore is an id the heap actually has**, since `classPayload?` answers
    `none` out of bounds. This is the L143 clause, now a consequence rather than a
    conjunct — which is why L147's strengthening costs nothing. -/
theorem classPayload?_isSome_lt {h : Heap} {k : ObjId}
    (hs : (h.classPayload? k).isSome) : k < h.objs.size := by
  by_cases hb : k < h.objs.size
  · exact hb
  · rw [classPayload?_oob h k hb] at hs
    exact absurd hs (by simp)

theorem valueTy_ref_klass_lt {h : Heap} {o : ObjId} (hp : plainRecv h o = true) :
    classOf h (.ref o) < h.objs.size :=
  classPayload?_isSome_lt (valueTy_ref_klass_isSome hp)

/-- **A typed `.ref` is not typed at a *ground* type.** L146's statement was the
    positive one — *a `.ref`'s type is a class type* — and L193 made that false: the
    relation admits `.any` and `.nilable` above the exact type. The negative form is
    what the consumer wanted anyway (`DeclsOk_grow`: a declaration at a ground type
    can only ever be about immediates, so an allocation gives it no new inhabitant),
    and it survives the weakening because `subTy σ τ` at a *ground* `τ` is equality
    (`subTy_atomic`) and no `.ref`'s exact type is ground.

    Unused today, which is why it is stated in the form that will still be true at
    the next widening rather than the form that reads best. -/
theorem valueTy_ref_not_ground {h : Heap} {o : ObjId} {τ : Ty}
    (hv : ValueTy h (.ref o) τ) :
    τ ≠ .int ∧ τ ≠ .bool ∧ τ ≠ .nilT ∧ τ ≠ .sym := by
  rcases valueTy_ref_inv hv with ⟨-, hs⟩ | ⟨-, hs⟩ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro heq <;> rw [heq] at hs <;> simp [subTy] at hs

/-- **An immediate's type does not depend on the heap.** Four constant arms; stated
    as a transport in the direction `DeclsOk_grow` reads it, which is the direction
    `ValueTy.congr` cannot supply for a growing heap. -/
theorem valueTy_immediate {h h' : Heap} {v : Value} {τ : Ty} (hnr : ∀ o, v ≠ .ref o)
    (hv : ValueTy h' v τ) : ValueTy h v τ := by
  cases v with
  | ref o => exact absurd rfl (hnr o)
  | _ => simpa [ValueTy, valueTy?] using hv

/-- Every value in the list conforms to the corresponding declared type.
    Pointwise, and length-forcing by the `_, _ => False` arm — the same shape as
    `FramesOk`, for the same reason: an arity mismatch must not be silently
    admissible.

    **Arguments against *declared parameters*** — and since L183 the match is
    `subTy` rather than equality, because a declared parameter may be the top type.

    At a **concrete** parameter this is the old proposition, by `subTy_concrete`, so
    every `baseDecls` row's conformance obligation is unchanged. The weakening lives
    here and in `KontOk.recvK`/`argsK`; `ValueTy` itself is untouched and no value
    is ever typed `any`, which is what keeps `CtlOk` and its 39 call sites out of
    it. -/
def ValuesTy (h : Heap) : List Value → List Ty → Prop
  | [], [] => True
  | v :: vs, τ :: τs => (∃ σ, ValueTy h v σ ∧ subTy σ τ = true) ∧ ValuesTy h vs τs
  | _, _ => False


/-- The frame currently executing. -/
def curFid (m : Machine) : FrameId := m.stack.headD 0

/-- The frame currently executing. -/
def curFrame (m : Machine) : Frame := m.frames.getD (curFid m) default

/-- A frame's binding for `x`, or `nil` — the value `getLocal` reads once the
    `captured` chain is known empty. -/
def localOf (f : Frame) (x : String) : Value :=
  match f.locals.find? (·.1 == x) with
  | some (_, v) => v
  | none => .nil

/-- One activation conforms to one environment. `captured = none` is what makes
    the frame *self-contained*: `getLocal`/`setLocal` otherwise walk into
    enclosing scopes (`Machine.lean:322–352`) and nothing about them reduces. -/
def FrameConforms (h : Heap) (Γ : Env) (f : Frame) : Prop :=
  f.captured = none ∧
  -- **The definee is a class** (L153's `NoHook` generalization cashed, L154). It
  -- used to be `f.defmod = Boot.objectId`, which is all a fragment with no `class`
  -- and no `module` can ever produce — and which makes a class-body frame
  -- *inexpressible*, since `enterClassBody` pushes a frame whose `defmod` is the
  -- class being opened.
  --
  -- What the `def` case actually needs of the definee is exactly this and no more:
  -- somewhere to instantiate `NoHook`'s quantifier, so the `method_added` lookup at
  -- the definee misses. Every other `defineMethod` lemma — `DeclsOk`, `Saturated`,
  -- `LitClsOk`, `TypeAgree` — is already stated `∀ cls`. Reading what the hypothesis
  -- was *used for* is what shrank it from an equation to a predicate.
  --
  -- Carried per-frame rather than for the current one only, because `frameK` resumes
  -- a *caller's* frame and `NoHook` has to survive that.
  (h.classPayload? f.defmod).isSome ∧
  ∀ x τ, envGet? Γ x = some τ → ValueTy h (localOf f x) τ

/-- **Per-frame conformance down the activation stack**, innermost first.

    The `∀ g ∈ fids, g < fid` clause buys frame-id **distinctness**, which is
    what makes `setLocal` provably local: it writes to `curFid` only, so every
    other frame on the stack is untouched. Distinctness is true of the real
    machine — a pushed id is `frames.size`, hence strictly greater than every id
    already on the stack — but it has to be *carried*, not rediscovered, so it
    rides here rather than being a side theorem (L91 predicted this clause).

    Equal lengths are forced by the `_, _ => False` arm, which is why this
    subsumes P0a's `stack ≠ []`. -/
def FramesOk (h : Heap) (frames : Array Frame) : List FrameId → List Env → Prop
  | [], [] => True
  | fid :: fids, Γ :: Γs =>
      fid < frames.size ∧ (∀ g ∈ fids, g < fid) ∧
      FrameConforms h Γ (frames.getD fid default) ∧ FramesOk h frames fids Γs
  | _, _ => False

/-- **The outermost activation is the toplevel one, and its definee is `Object`**
    (L155).

    This is the fact that makes `infer`'s `top` flag mean something. `CtlOk` reads
    the mode off the environment stack (`Γs.isEmpty`), `FramesOk` forces the
    environment stack and the frame stack to have equal length, so `Γs = []` says
    the frame stack is a *singleton* — and this predicate says the frame a
    singleton stack names has `defmod = Object`. Composed:
    *toplevel mode ⇒ the definee is `Object`*, which is exactly what
    `enterClassBody`'s `constOwn m.currentFrame.defmod` needs pinned before the
    reopen branch can be described by a heap clause.

    Stated as its own recursion over the stack rather than as a clause of
    `FramesOk` deliberately: `FramesOk`'s four-way destructuring is consumed by
    nine existing lemmas, and a fifth conjunct in its `cons` arm would churn every
    one of them for a fact none of them uses. -/
def BottomObj (frames : Array Frame) : List FrameId → Prop
  | [] => True
  | [fid] => (frames.getD fid default).defmod = Boot.objectId
  | _ :: rest => BottomObj frames rest

/-- What `getLocal`/`setLocal` need, derived from the head of `FramesOk`. Kept as
    its own definition so the local-access lemmas stay readable. -/
def FrameOk (m : Machine) : Prop :=
  m.stack ≠ [] ∧ curFid m < m.frames.size ∧ (curFrame m).captured = none

/-- Every variable the environment types holds a value of that type. Stated
    against `m.getLocal` — what the interpreter actually reads. -/
def LocalsOk (Γ : Env) (m : Machine) : Prop :=
  ∀ x τ, envGet? Γ x = some τ → ValueTy m.heap (m.getLocal x) τ

/-! ### 1.1 Two array facts, and local access on the current frame -/

theorem getD_set!_ne (a : Array Frame) (i j : Nat) (f : Frame) (h : j ≠ i) :
    (a.set! i f).getD j default = a.getD j default := by
  have hsz : (a.set! i f).size = a.size := by simp [Array.set!]
  by_cases hj : j < a.size
  · simp only [Array.getD]
    rw [dif_pos (hsz ▸ hj), dif_pos hj]
    exact Array.getElem_setIfInBounds_ne hj (Ne.symm h)
  · simp only [Array.getD]
    rw [dif_neg (hsz ▸ hj), dif_neg hj]

theorem getD_set!_self (a : Array Frame) (i : Nat) (f : Frame) (h : i < a.size) :
    (a.set! i f).getD i default = f := by
  simp [Array.getD, h]

/-- The pushed frame reads back at the id it was given. -/
theorem getD_push_lt_self (a : Array Frame) (f : Frame) :
    (a.push f).getD a.size default = f := by
  simp [Array.getD, Array.size_push]

theorem getD_push_lt (a : Array Frame) (j : Nat) (f : Frame) (h : j < a.size) :
    (a.push f).getD j default = a.getD j default := by
  simp only [Array.getD]
  rw [dif_pos h, dif_pos (show j < (a.push f).size by simp [Array.size_push]; omega)]
  exact Array.getElem_push_lt h

/-- **Each activation's definee, named** (F1b.9) — the static counterpart of
    `FrameConforms`'s *the definee is a class*, and the fact a declaration row
    needs.

    A row is keyed on a class **name**, because `infer` cannot name an `ObjId`.
    So the `def` rule keys its row on the context it was checked in, and the
    invariant has to tie that name to the class the step actually installs the
    method on — `(curFrame m).defmod`. That is this predicate, and it is carried
    for the whole stack rather than the current frame only for the same reason
    `FrameConforms` is: `frameK` resumes a *caller's* frame, and the caller's
    context has to survive the pop.

    **`defVis = .pub` rides here**, and it is not an afterthought. `evalExpr`'s
    `def` builds `visibility := if name == "initialize" then .priv else if kind ==
    .toplevel then .priv else defVis` (`Interp.lean:225`), while `ResolvesUser`
    requires `.pub` — so a row is witnessable only where the frame's default
    visibility is public. That also settles a question pricing raised and could
    not answer from the rules: **a toplevel `def` cannot carry a row at all**,
    because a toplevel method is private, which is exactly CRuby's behaviour and
    the reason `public def m …` exists. The first row therefore has to come from a
    `def` inside a class body, which is why the context stack is not avoidable.

    Stated as its own recursion, following `BottomObj` and for the reason its
    docstring gives: a further conjunct in `FramesOk`'s `cons` arm would churn
    nine lemmas for a fact none of them uses. -/
def defVisOfDef (f : Frame) : Visibility :=
  if f.kind == .toplevel then .priv else f.defVis

def StackCtx (h : Heap) (frames : Array Frame) : List FrameId → List FrameCtx → Prop
  | [], [] => True
  | fid :: fids, c :: cs =>
      (h.classPayload? (frames.getD fid default).defmod).isSome ∧
      className h (frames.getD fid default).defmod = c.cls ∧
      (fids ≠ [] → defVisOfDef (frames.getD fid default) = .pub) ∧
      -- **The activation's `self`, when the context claims one** (F1b.11). `some c`
      -- says this is a *method* body, where `self` is an instance of `c`; a class
      -- body says `none`, because there `self` is the class object and `plainRecv`
      -- gives it no type. The fact is not new work at the push — `user_dispatch`
      -- already has it as the send's own `ValueTy` on the receiver — it is the
      -- *carrying* of it across the body's steps that this clause is.
      (∀ sc, c.selfCls = some sc →
        ValueTy h (frames.getD fid default).self (.cls sc)) ∧
      -- **`Object` is on the frame's lexical constant scope** (L189), and it is the
      -- *whole* frame-side cost of the `.const` read rule. `evalExpr`'s `.const` walks
      -- `cref` before the ancestors (artifact 03 §4), and `ClassOk`'s sole-owner
      -- clause says any hit is `Object`'s — so the read is decided the moment `Object`
      -- is known to be *on* the list. It is, for every frame the fragment builds:
      -- `Machine.init` sets `cref := [Object]`, `enterClassBody` prepends the class
      -- (`Interp/Dispatch.lean:224`), and a method frame takes `md.cref` — which is
      -- the defining frame's, so `ResolvesUser` carries the clause across a call.
      --
      -- A membership rather than a shape, deliberately: nothing needs to know what
      -- else is on the list, because sole ownership makes the other entries answer
      -- `none`. That is the difference between this clause and the `CrefOk` an earlier
      -- draft priced — *nothing in front of `Object` owns anything* — which would have
      -- had to be re-established at every push.
      Boot.objectId ∈ (frames.getD fid default).cref ∧
      -- **A context that declares a return type is a *method* activation** (L198),
      -- and this is the whole frame-side cost of the `return` rule. `returnTarget`
      -- (`Interp/Support.lean:349`) answers the stack's head for every frame kind
      -- *except* `.block`, where it walks to the closure's home — so the rule needs to
      -- know the current activation is not a block, and `ret.isSome` is exactly when
      -- it needs to. Vacuous at a class body and at toplevel, both of which declare
      -- no return type; established at `user_dispatch`'s push, where `userFrame`
      -- builds a `.method` frame.
      ((frames.getD fid default).kind = .method ∨ c.ret = none) ∧
      StackCtx h frames fids cs
  | _, _ => False

theorem StackCtx.tail {h : Heap} {frames : Array Frame} {fids : List FrameId}
    {c : FrameCtx} {cs : List FrameCtx} (hs : StackCtx h frames fids (c :: cs)) :
    StackCtx h frames fids.tail cs := by
  cases fids with
  | nil => exact absurd hs (by simp [StackCtx])
  | cons fid rest => exact hs.2.2.2.2.2.2

theorem StackCtx.head {h : Heap} {frames : Array Frame} {fid : FrameId}
    {fids : List FrameId} {c : FrameCtx} {cs : List FrameCtx}
    (hs : StackCtx h frames (fid :: fids) (c :: cs)) :
    className h (frames.getD fid default).defmod = c.cls := hs.2.1

theorem StackCtx.headVis {h : Heap} {frames : Array Frame} {fid : FrameId}
    {fids : List FrameId} {c : FrameCtx} {cs : List FrameCtx}
    (hs : StackCtx h frames (fid :: fids) (c :: cs)) :
    fids ≠ [] → defVisOfDef (frames.getD fid default) = .pub := hs.2.2.1

/-- Pushing a frame leaves every stacked frame's entry alone, provided the ids
    already on the stack are in bounds — the same hypothesis `BottomObj_push`
    takes, and true of the real machine for the same reason. -/
theorem StackCtx.push {h : Heap} {frames : Array Frame} {f : Frame} :
    ∀ {st : List FrameId} {cs : List FrameCtx}, (∀ g ∈ st, g < frames.size) →
      StackCtx h frames st cs → StackCtx h (frames.push f) st cs
  | [], [], _, hs => hs
  | fid :: fids, c :: cs, hlt, hs => by
      have hb : (frames.push f).getD fid default = frames.getD fid default :=
        getD_push_lt _ _ _ (hlt fid (List.mem_cons_self ..))
      exact ⟨by rw [hb]; exact hs.1, by rw [hb]; exact hs.2.1,
        by rw [hb]; exact hs.2.2.1, by rw [hb]; exact hs.2.2.2.1,
        by rw [hb]; exact hs.2.2.2.2.1, by rw [hb]; exact hs.2.2.2.2.2.1,
        StackCtx.push (fun g hg => hlt g (List.mem_cons_of_mem _ hg)) hs.2.2.2.2.2.2⟩
  | [], _ :: _, _, hs => hs.elim
  | _ :: _, [], _, hs => hs.elim

theorem getLocal_cur {m : Machine} (hf : FrameOk m) (x : String) :
    m.getLocal x = localOf (curFrame m) x := by
  obtain ⟨_, _, hc⟩ := hf
  simp only [curFrame, curFid] at hc
  unfold Machine.getLocal
  unfold Machine.getLocal.go
  simp only [localOf, curFrame, curFid, hc]
  rfl

-- `find?_filter_ne` now lives in `Proof/HeapFacts.lean` — the `defineMethod`
-- chain needs it too, and one copy is better than two.
open RubyCore.Proof in

/-- With no captured chain, `setLocal`'s owner search returns the start frame on
    both branches, whichever frame that is. -/
theorem setLocal_owner_start {m : Machine} {start : FrameId}
    (hc : (m.frames.getD start default).captured = none) (x : String) (fuel : Nat) :
    Machine.setLocal.owner m x start start (fuel + 1) = start := by
  unfold Machine.setLocal.owner
  simp only [hc]
  split <;> rfl

/-- `setLocal` is a `set!` at `curFid`, and nothing else. -/
theorem setLocal_frames {m : Machine} (hf : FrameOk m) (x : String) (v : Value) :
    (m.setLocal x v).frames =
      m.frames.set! (curFid m)
        { curFrame m with locals := (x, v) :: (curFrame m).locals.filter (·.1 != x) } := by
  obtain ⟨_, _, hc⟩ := hf
  simp only [curFrame, curFid] at hc ⊢
  unfold Machine.setLocal
  simp only [setLocal_owner_start hc x m.frames.size]

theorem setLocal_stack {m : Machine} (x : String) (v : Value) :
    (m.setLocal x v).stack = m.stack := by simp [Machine.setLocal]

theorem curFid_setLocal {m : Machine} (x : String) (v : Value) :
    curFid (m.setLocal x v) = curFid m := by simp [Machine.setLocal, curFid]

theorem FrameOk.setLocal {m : Machine} (hf : FrameOk m) (x : String) (v : Value) :
    FrameOk (m.setLocal x v) := by
  have hfr := setLocal_frames hf x v
  obtain ⟨hne, hlt, hc⟩ := hf
  refine ⟨by rw [setLocal_stack]; exact hne, ?_, ?_⟩
  · rw [curFid_setLocal, hfr]; simpa [Array.set!] using hlt
  · rw [curFrame, curFid_setLocal, hfr, getD_set!_self _ _ _ (by simpa using hlt)]
    exact hc

/-- The one substantive fact about locals: assignment updates exactly `x`. -/
theorem localOf_setLocal {m : Machine} (hf : FrameOk m) (x y : String) (v : Value) :
    localOf (curFrame (m.setLocal x v)) y =
      if y = x then v else localOf (curFrame m) y := by
  have hlt := hf.2.1
  rw [curFrame, curFid_setLocal, setLocal_frames hf x v,
    getD_set!_self _ _ _ (by simpa using hlt)]
  by_cases hyx : y = x
  · subst hyx; simp [localOf, List.find?]
  · have hne : ((x, v).1 == y) = false := by
      simp only [beq_eq_false_iff_ne]; exact fun h => hyx h.symm
    simp only [localOf, List.find?, hne, if_neg hyx]
    rw [find?_filter_ne _ hyx]

theorem getLocal_setLocal {m : Machine} (hf : FrameOk m) (x y : String) (v : Value) :
    (m.setLocal x v).getLocal y = if y = x then v else m.getLocal y := by
  rw [getLocal_cur (FrameOk.setLocal hf x v) y, getLocal_cur hf y,
    localOf_setLocal hf x y v]

/-! ### 1.2 `FramesOk` implies what the old invariant asserted -/

theorem FramesOk.frameOk {m : Machine} {Γ : Env} {Γs : List Env}
    (h : FramesOk m.heap m.frames m.stack (Γ :: Γs)) : FrameOk m := by
  cases hst : m.stack with
  | nil => rw [hst] at h; exact absurd h (by simp [FramesOk])
  | cons fid fids =>
    rw [hst] at h
    obtain ⟨hlt, _, ⟨hc, _, _⟩, _⟩ := h
    refine ⟨by rw [hst]; simp, ?_, ?_⟩
    · simpa [curFid, hst] using hlt
    · simpa [curFrame, curFid, hst] using hc

/-- Popping the innermost activation: a suffix of a conforming stack conforms. -/
theorem FramesOk.tail {hp : Heap} {frames : Array Frame} {fids : List FrameId} {Γ : Env}
    {Γs : List Env} (h : FramesOk hp frames fids (Γ :: Γs)) :
    FramesOk hp frames fids.tail Γs := by
  cases fids with
  | nil => exact absurd h (by simp [FramesOk])
  | cons fid rest => exact h.2.2.2

/-- Every id on a conforming stack indexes a real frame. `FramesOk` says so of the
    head at each level; this collects it, which is what `BottomObj`'s transport
    across a `push` needs. -/
theorem FramesOk.mem_lt {hp : Heap} {frames : Array Frame} :
    ∀ {fids : List FrameId} {Γs : List Env}, FramesOk hp frames fids Γs →
      ∀ g ∈ fids, g < frames.size := by
  intro fids
  induction fids with
  | nil => intro _ _ g hg; exact absurd hg (by simp)
  | cons fid rest ih =>
    intro Γs h g hg
    cases Γs with
    | nil => exact absurd h (by simp [FramesOk])
    | cons Γ Γs' =>
      rcases List.mem_cons.mp hg with rfl | hm
      · exact h.1
      · exact ih h.2.2.2 g hm

/-- **A pushed frame disturbs no frame already on the stack** (L156). `FramesOk`
    reads frames by id and every stacked id is already in bounds
    (`FramesOk.mem_lt`), so `getD` answers the same object either side of a
    `push`. This is what `class'` and `enterUserMethod` both need, and it is the
    frames-side counterpart of `BottomObj_push`. -/
theorem FramesOk.push {hp : Heap} {frames : Array Frame} {f : Frame} :
    ∀ {fids : List FrameId} {Γs : List Env}, FramesOk hp frames fids Γs →
      FramesOk hp (frames.push f) fids Γs := by
  intro fids
  induction fids with
  | nil => intro Γs h; cases Γs with
    | nil => exact trivial
    | cons _ _ => exact absurd h (by simp [FramesOk])
  | cons fid rest ih =>
    intro Γs h
    cases Γs with
    | nil => exact absurd h (by simp [FramesOk])
    | cons Γ Γs' =>
      obtain ⟨hlt, hgt, hfc, htl⟩ := h
      exact ⟨by rw [Array.size_push]; exact Nat.lt_succ_of_lt hlt, hgt,
        by rw [getD_push_lt _ _ _ hlt]; exact hfc, ih htl⟩

/-- **The toplevel mode really does mean a single activation.** `FramesOk`'s
    `_, _ => False` arm forces the frame stack and the environment stack to have
    equal length, so an empty environment tail is a singleton frame stack — which
    with `BottomObj` is what pins the definee to `Object`. -/
theorem FramesOk.stack_singleton {hp : Heap} {frames : Array Frame}
    {fids : List FrameId} {Γ : Env} (h : FramesOk hp frames fids [Γ]) :
    ∃ fid, fids = [fid] := by
  cases fids with
  | nil => exact absurd h (by simp [FramesOk])
  | cons fid rest =>
    cases rest with
    | nil => exact ⟨fid, rfl⟩
    | cons a b => exact absurd h.2.2.2 (by simp [FramesOk])

/-! ### 1.2a `BottomObj` transports

Three lemmas, one per way the fragment touches `frames`/`stack`: a `set!` that
preserves the written frame's definee, a `push` under a non-empty stack, and a
pop. None mentions the heap. -/

/-- `BottomObj` only reads each stacked frame's `defmod`, so any array that agrees
    with the old one on those fields carries it. -/
theorem BottomObj_congr {f₁ f₂ : Array Frame} :
    ∀ {st : List FrameId},
      (∀ fid ∈ st, (f₂.getD fid default).defmod = (f₁.getD fid default).defmod) →
      BottomObj f₁ st → BottomObj f₂ st := by
  intro st
  induction st with
  | nil => intro _ h; exact h
  | cons a rest ih =>
    cases rest with
    | nil =>
      intro hd h
      show (f₂.getD a default).defmod = Boot.objectId
      rw [hd a (by simp)]; exact h
    | cons b rest' =>
      intro hd h
      show BottomObj f₂ (b :: rest')
      exact ih (fun fid hm => hd fid (List.mem_cons_of_mem a hm)) h

/-- A `push` leaves every id the stack already carries reading the same frame. -/
theorem BottomObj_push {frames : Array Frame} {st : List FrameId} {f : Frame}
    (hlt : ∀ g ∈ st, g < frames.size) (h : BottomObj frames st) :
    BottomObj (frames.push f) st :=
  BottomObj_congr (fun fid hm => by rw [getD_push_lt _ _ _ (hlt fid hm)]) h

/-- Pushing a *new* activation on a non-empty stack: the outermost frame is
    unchanged, and it is still the outermost one. -/
theorem BottomObj_cons {frames : Array Frame} {st : List FrameId} {fid : FrameId}
    (hne : st ≠ []) (h : BottomObj frames st) : BottomObj frames (fid :: st) := by
  cases st with
  | nil => exact absurd rfl hne
  | cons a rest => exact h

/-- Popping an activation from a stack of at least two frames. -/
theorem BottomObj_tail {frames : Array Frame} {st : List FrameId}
    (h : BottomObj frames st) : BottomObj frames st.tail := by
  cases st with
  | nil => exact h
  | cons a rest =>
    cases rest with
    | nil => exact trivial
    | cons b rest' => exact h

/-- **The toplevel mode really does pin the definee.** A singleton frame stack is
    the one `FramesOk` forces when the environment stack has an empty tail, and
    `BottomObj` names its definee. This is the composite the `class` rule consumes. -/
theorem BottomObj_curFrame {m : Machine} {fid : FrameId}
    (hst : m.stack = [fid]) (h : BottomObj m.frames m.stack) :
    (curFrame m).defmod = Boot.objectId := by
  rw [hst] at h
  simp only [curFrame, curFid, hst, List.headD_cons]
  exact h

theorem FramesOk.localsOk {m : Machine} {Γ : Env} {Γs : List Env}
    (h : FramesOk m.heap m.frames m.stack (Γ :: Γs)) : LocalsOk Γ m := by
  intro x τ hg
  rw [getLocal_cur h.frameOk x]
  cases hst : m.stack with
  | nil => rw [hst] at h; exact absurd h (by simp [FramesOk])
  | cons fid fids =>
    have hc : FrameConforms m.heap Γ (m.frames.getD fid default) := by
      rw [hst] at h; exact h.2.2.1
    have : curFrame m = m.frames.getD fid default := by
      simp [curFrame, curFid, hst]
    rw [this]
    exact hc.2.2 x τ hg

/-! ### 1.3 Environment update, and its agreement with `setLocal` -/

theorem envGet?_nil (y : String) : envGet? ([] : Env) y = none := rfl

theorem envGet?_cons (z : String) (σ : Ty) (Γ : Env) (y : String) :
    envGet? ((z, σ) :: Γ) y = if z = y then some σ else envGet? Γ y := by
  by_cases h : z = y
  · subst h; simp [envGet?, List.find?]
  · have hb : (z == y) = false := by simpa using h
    simp [envGet?, List.find?, hb, h]

theorem envSet_nil (x : String) (τ : Ty) : envSet [] x τ = [(x, τ)] := rfl

theorem envSet_cons (z : String) (σ : Ty) (Γ : Env) (x : String) (τ : Ty) :
    envSet ((z, σ) :: Γ) x τ =
      if z = x then (x, τ) :: Γ else (z, σ) :: envSet Γ x τ := by
  simp only [envSet, beq_iff_eq]

theorem envGet?_set (Γ : Env) (x y : String) (τ : Ty) :
    envGet? (envSet Γ x τ) y = if y = x then some τ else envGet? Γ y := by
  induction Γ with
  | nil =>
    rw [envSet_nil, envGet?_cons, envGet?_nil]
    by_cases h : y = x
    · subst h; simp
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]
  | cons a Γ ih =>
    obtain ⟨z, σ⟩ := a
    rw [envSet_cons]
    by_cases hzx : z = x
    · subst hzx
      rw [if_pos rfl, envGet?_cons, envGet?_cons]
      by_cases hyz : y = z
      · subst hyz; simp
      · rw [if_neg hyz, if_neg (fun hh => hyz hh.symm), if_neg (fun hh => hyz hh.symm)]
    · rw [if_neg hzx, envGet?_cons, envGet?_cons, ih]
      by_cases hzy : z = y
      · subst hzy
        rw [if_pos rfl, if_pos rfl, if_neg (fun hh => hzx hh)]
      · rw [if_neg hzy, if_neg hzy]

/-! ### 1.4 `FramesOk` under the fragment's updates -/

/-- Conformance only reads the frames the stack names, so an array change that
    leaves those alone transports it. -/
theorem FramesOk.frames_congr {hp : Heap} {a b : Array Frame} :
    ∀ {fids : List FrameId} {Γs : List Env}, FramesOk hp a fids Γs →
      (∀ g ∈ fids, g < b.size) → (∀ g ∈ fids, b.getD g default = a.getD g default) →
      FramesOk hp b fids Γs
  | [], [], h, _, _ => h
  | fid :: fids, Γ :: Γs, h, hb, heq => by
    obtain ⟨_, hlt2, hcf, hrest⟩ := h
    exact ⟨hb fid (by simp), hlt2,
      by rw [heq fid (by simp)]; exact hcf,
      FramesOk.frames_congr hrest (fun g hg => hb g (by simp [hg]))
        (fun g hg => heq g (by simp [hg]))⟩
  | [], _ :: _, h, _, _ => absurd h (by simp [FramesOk])
  | _ :: _, [], h, _, _ => absurd h (by simp [FramesOk])

theorem FramesOk.setLocal {m : Machine} {Γ : Env} {Γs : List Env} {x : String}
    {τ : Ty} {v : Value} (hfs : FramesOk m.heap m.frames m.stack (Γ :: Γs))
    (hv : ValueTy m.heap v τ) :
    FramesOk m.heap (m.setLocal x v).frames (m.setLocal x v).stack
      (envSet Γ x τ :: Γs) := by
  have hf := hfs.frameOk
  have hlt := hf.2.1
  rw [setLocal_stack]
  cases hst : m.stack with
  | nil => rw [hst] at hfs; exact absurd hfs (by simp [FramesOk])
  | cons fid fids =>
    have hcur : curFid m = fid := by simp [curFid, hst]
    rw [hst] at hfs
    obtain ⟨hfl, hgt, hcf, hrest⟩ := hfs
    have hsz : (m.setLocal x v).frames.size = m.frames.size := by
      rw [setLocal_frames hf x v]; simp [Array.set!]
    refine ⟨by rw [hsz]; exact hfl, hgt, ⟨?_, ?_, ?_⟩, ?_⟩
    -- the head frame: captured survives, and the binding is updated at `x` only
    · have := (FrameOk.setLocal hf x v).2.2
      simpa [curFrame, curFid_setLocal, hcur] using this
    · -- `defmod` rides through `setLocal`, which only rewrites `locals`
      have := setLocal_frames hf x v
      rw [this, hcur, getD_set!_self _ _ _ hfl]
      -- L154: the clause is now `classPayload?` at the definee. `setLocal` rewrites
      -- `locals` and touches neither `defmod` nor the heap, so it still rides
      -- through — but the goal no longer reduces by `show`, because the definee is
      -- under a structure-update literal rather than being a constant.
      have hcf' : curFrame m = m.frames.getD fid default := by simp [curFrame, hcur]
      have := hcf.2.1
      rw [← hcf'] at this
      exact this
    · intro y σ hg
      have hy : localOf ((m.setLocal x v).frames.getD fid default) y
          = localOf (curFrame (m.setLocal x v)) y := by
        simp [curFrame, curFid_setLocal, hcur]
      rw [envGet?_set] at hg
      rw [hy, localOf_setLocal hf x y v]
      by_cases hyx : y = x
      · rw [if_pos hyx] at hg ⊢
        rw [Option.some.injEq] at hg; subst hg; exact hv
      · rw [if_neg hyx] at hg ⊢
        have := hcf.2.2 y σ hg
        simpa [curFrame, hcur] using this
    -- the frames below: every id there is `< fid = curFid`, so `set!` missed them
    · refine FramesOk.frames_congr hrest (fun g hg => by rw [hsz]; exact Nat.lt_trans (hgt g hg) hfl)
        (fun g hg => ?_)
      rw [setLocal_frames hf x v, hcur]
      exact getD_set!_ne _ _ _ _ (Nat.ne_of_lt (hgt g hg))
/-! ### 1.5 Heap congruence — what the threading costs

Once the typing judgement is indexed by a heap, every heap-writing step owes a
*transport*: the `ValueTy` facts already stored in frames and continuations must
still hold in the new heap. `TypeAgree` is the condition that discharges it, and
it is deliberately stated as **exactly what a nominal `Ty` will read** rather than
as what today's four ground types read (which is nothing):

* `classOf` — the dispatch class of a value, what `T.instance C` must consult;
* `className` — the name a nominal type is written with (`Sub` as the `ancestors`
  walk, `PLAN.md` W5 T2, will need `ancestors` here too);
* `classPayload?`-ness — whether an id is a class at all, what `T.class_of C`
  needs.

`defineMethod` satisfies all three (`Proof/HeapFacts.lean`), which is why the
`def` case of preservation can discharge the transport today; a step that
`alloc`s or splices `includes` will not, and that is F1's real cost showing up
here rather than being discovered inside a 300-line case analysis.
-/

/-- The heap facts a nominal type language reads. Reflexive, and `defineMethod`
    is an instance.

    **The fourth clause is F1b's**, and it is the one place the class arm cost
    something that was not already written down: `valueTy?`'s `.ref` arm reads
    `plainRecv`, which reads the object's `eigen` and `payload`, and neither is
    determined by the first three. It is stated per-object rather than per-value
    for the same reason `className`'s clause is stated per-id — the transport is
    needed for values the *heap* holds, not only for the one in hand.

    **Relativized to `o < h.objs.size` in L143, which is the whole content of the
    producer's bill item 2.** Unrelativized, the condition is *false* for any step
    that grows the heap: L142 fixed the value at the fresh id having a type, but
    the equalities were still asserted **at** the fresh id, where they are false
    the moment the allocated object is a class (`className h k = "Object"` out of
    bounds, `className h' k = C` in it). Relativized, `alloc` satisfies every
    clause from one fact — `Array.push` does not move an existing index — and
    nothing is lost, because `ValueTy` implies the value is in bounds
    (`valueTy_ref_lt`) and its class is too (`valueTy_ref_klass_lt`). The
    transport is only ever asked about facts the *old* heap could state.

    **The `plainRecv` clause is an implication, not an equality, and that
    asymmetry is forced.** `plainRecv` reads `h.objs.size` twice — once for `o`
    and once, since L143, for `o`'s class — so a growing heap can turn a
    *non*-plain receiver plain, and does exactly that for an object whose class is
    the id being allocated. Nothing needs the other direction: transport is asked
    to carry facts *forward*, so what it needs is that a receiver the old heap
    typed is still typed. Read the four clauses as "everything the old heap could
    say about an id it had, it can still say", which is the weakest thing
    `ValueTy.congr` will accept. -/
def TypeAgree (h h' : Heap) : Prop :=
  (∀ o, o < h.objs.size → classOf h' (.ref o) = classOf h (.ref o)) ∧
    (∀ k, k < h.objs.size → className h' k = className h k) ∧
    (∀ k, k < h.objs.size → (h'.classPayload? k).isSome = (h.classPayload? k).isSome) ∧
    (∀ o, o < h.objs.size → plainRecv h o = true → plainRecv h' o = true) ∧
    -- **L185's fifth clause**, and it is the class-object arm's whole transport
    -- bill: a class receiver stays one. Cheap for every step in the fragment —
    -- `PlainGrow`'s *nothing became a class* pins the payload and `defineMethod`
    -- rewrites `methods` — and stated here rather than derived at the use site for
    -- the fourth time, which is `plainRecv`'s own pattern.
    (∀ o, o < h.objs.size → classRecv h o = true → classRecv h' o = true)

theorem TypeAgree.rfl' (h : Heap) : TypeAgree h h :=
  ⟨fun _ _ => Eq.refl _, fun _ _ => Eq.refl _, fun _ _ => Eq.refl _, fun _ _ hp => hp,
   fun _ _ hc => hc⟩

/-- **Transport across a frame-array rewrite**, the counterpart of
    `BottomObj_congr`. `setLocal` writes one frame's `locals`, and this predicate
    reads only `defmod` and `defVis`, so a step that moves neither leaves it
    alone. -/
theorem StackCtx_congr {h : Heap} {f₁ f₂ : Array Frame} :
    ∀ {st : List FrameId} {cs : List FrameCtx},
      (∀ fid ∈ st, (f₂.getD fid default).defmod = (f₁.getD fid default).defmod) →
      (∀ fid ∈ st, defVisOfDef (f₂.getD fid default) = defVisOfDef (f₁.getD fid default)) →
      (∀ fid ∈ st, (f₂.getD fid default).self = (f₁.getD fid default).self) →
      -- L189: the `cref` clause needs its own agreement, for the same reason the
      -- other three do — `setLocal` writes `locals` and moves neither.
      (∀ fid ∈ st, (f₂.getD fid default).cref = (f₁.getD fid default).cref) →
      -- L198's clause needs its own agreement, for the four before it: the `kind` a
      -- frame was built with does not move either.
      (∀ fid ∈ st, (f₂.getD fid default).kind = (f₁.getD fid default).kind) →
      StackCtx h f₁ st cs → StackCtx h f₂ st cs
  | [], [], _, _, _, _, _, hs => hs
  | fid :: fids, c :: cs, hd, hv, hsf, hcr, hkd, hs => by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_,
        StackCtx_congr (fun g hg => hd g (List.mem_cons_of_mem _ hg))
          (fun g hg => hv g (List.mem_cons_of_mem _ hg))
          (fun g hg => hsf g (List.mem_cons_of_mem _ hg))
          (fun g hg => hcr g (List.mem_cons_of_mem _ hg))
          (fun g hg => hkd g (List.mem_cons_of_mem _ hg)) hs.2.2.2.2.2.2⟩
      · rw [hd fid (List.mem_cons_self ..)]; exact hs.1
      · rw [hd fid (List.mem_cons_self ..)]; exact hs.2.1
      · rw [hv fid (List.mem_cons_self ..)]; exact hs.2.2.1
      · rw [hsf fid (List.mem_cons_self ..)]; exact hs.2.2.2.1
      · rw [hcr fid (List.mem_cons_self ..)]; exact hs.2.2.2.2.1
      · rw [hkd fid (List.mem_cons_self ..)]; exact hs.2.2.2.2.2.1

/-! ### ~~`TypeAgree.symm`~~, ~~`TypeAgree.of_equalities`~~, ~~`typeAgree_defineMethod'`~~ — all withdrawn

The backward transport has no consumers left, and the sequence is worth keeping
visible because each step was a *correction of the previous one*:

* L137 had `TypeAgree.symm`, true because the relation was four unrelativized
  equalities;
* L143 relativized the relation, which made `symm` **false** for a growing step, and
  replaced it with `TypeAgree.of_equalities` — both directions from what a `set!`-shaped
  step proves — exposed as `typeAgree_defineMethod'`;
* L146 removed `ConformsAt`'s heap index, which retired one of the two callers;
* L147 made resolution class-indexed, which retired the other: the hypothesis
  `DeclsOk_defineMethod` reads backwards is now `TyClass`, not `ValueTy`, and `TyClass`
  transports both ways for any step preserving `className` and `classPayload?`-ness.

So the invariant's transport is now **entirely forward**, and the machinery for the
other direction is deleted rather than kept "in case". What that machinery was really
paying for was an inhabitant-indexed clause; the clause was the defect.
-/

/-- A `setClassPayload` leaves a `.cls` payload at the written id — which is the
    only thing `plainRecv` reads there. Stated about the payload rather than about
    the whole `Object` so that the record literal `defineMethod` builds never has to
    be written out. -/
theorem payload_setClassPayload (h : Heap) (o : ObjId) (c : ClassPayload)
    (hb : o < h.objs.size) : ((h.setClassPayload o c).get o).payload = .cls c := by
  simp only [Heap.setClassPayload, Heap.get, Heap.set]
  rw [objs_getD_set!_self _ _ _ hb]

/-- **What `plainRecv` reads, as a congruence.** Three facts, one per clause, and
    they are exactly what a step that rewrites one object in place can supply.
    L147 introduced it because the `klass`-is-a-class clause made the two
    `defineMethod` cases diverge, and the divergence is real: at the written id the
    object *does* change. -/
theorem plainRecv_congr {h h' : Heap} {o : ObjId}
    (hsz : h'.objs.size = h.objs.size) (hget : h'.get o = h.get o)
    (hcp : ∀ k, (h'.classPayload? k).isSome = (h.classPayload? k).isSome) :
    plainRecv h' o = plainRecv h o := by
  unfold plainRecv
  rw [hget, hsz, hcp]

/-- A `defineMethod` at a *different* id leaves the object alone. -/
theorem get_defineMethod_ne (h : Heap) (cls o : ObjId) (name : String)
    (md : MethodDef) (hk : ¬ o = cls) :
    (defineMethod h cls name md).get o = h.get o := by
  unfold defineMethod
  split
  · simp only [Heap.setClassPayload, Heap.get, Heap.set]
    rw [objs_getD_set!_ne _ _ _ _ hk]
  · rfl

/-- **`defineMethod` cannot change whether an object is dispatched uniformly.**
    The fourth clause of `TypeAgree`, and the F1b analogue of
    `classPayload?_isSome_defineMethod`. It is *not* the statement that the payload
    is unchanged — at `o = cls` the payload really does change, since that is what
    `defineMethod` is for — only that it stays a `.cls`, which is all `plainRecv`
    asks. `eigen` is untouched because `setClassPayload` is a `with` on the payload
    field alone.

    Kept here rather than in `Proof/HeapFacts.lean` (where the rest of the
    `defineMethod` chain lives) because `plainRecv` is part of the *type
    judgement's* vocabulary — it exists to say which receivers `valueTy?` admits —
    and separating a definition from its only consumer costs more than the
    symmetry buys. -/
theorem plainRecv_defineMethod (h : Heap) (cls o : ObjId) (name : String)
    (md : MethodDef) : plainRecv (defineMethod h cls name md) o = plainRecv h o := by
  by_cases hk : o = cls
  · subst hk
    -- Both sides are `false`, and for the same reason: `o` is a class object before
    -- the write and still one after it. Neither side reads `eigen`.
    unfold defineMethod
    split
    · rename_i c hc
      have hb : o < h.objs.size := classPayload?_isSome_lt (by rw [hc]; simp)
      have hpay : (h.get o).payload = .cls c := by
        unfold Heap.classPayload? at hc
        split at hc <;> simp_all
      unfold plainRecv
      rw [payload_setClassPayload h o _ hb, hpay]
      simp
    · rfl
  · exact plainRecv_congr (objs_size_defineMethod h cls name md)
      (get_defineMethod_ne h cls o name md hk)
      (fun k => classPayload?_isSome_defineMethod h cls k name md)

/-- **`defineMethod`'s transport.** The four facts are equalities and unrelativized —
    a method-table write moves no id — so the relativized clauses are satisfied at
    every id, not only the old ones.

    The third clause is `classPayload?_isSome_defineMethod` in
    `Proof/HeapFacts.lean`, beside the rest of the `defineMethod` chain — it is a fact
    about the heap, not about the type judgement (F1a). The fourth is F1b's and is
    directly above, for the reason recorded there. -/
theorem typeAgree_defineMethod (h : Heap) (cls : ObjId) (name : String)
    (md : MethodDef) : TypeAgree h (defineMethod h cls name md) :=
  ⟨fun o _ => classOf_defineMethod h cls name md (.ref o),
    fun k _ => className_defineMethod h cls k name md,
    fun k _ => classPayload?_isSome_defineMethod h cls k name md,
    fun o _ hp => (plainRecv_defineMethod h cls o name md).trans hp,
    -- L185's fifth clause. `defineMethod` writes `methods` inside a `.cls`
    -- payload, so a class stays a class and the two receiver-id refusals are about
    -- `o` alone — the same one-line argument the fourth clause makes.
    -- L185's fifth clause. `defineMethod` writes `methods` *inside* a `.cls`
    -- payload, so a class stays a class — which is exactly
    -- `classPayload?_isSome_defineMethod`, the lemma the third clause already uses
    -- — and the size and the two id comparisons are untouched.
    fun o _ hc => by
      unfold classRecv at hc ⊢
      rw [show (defineMethod h cls name md).objs.size = h.objs.size from by
            unfold defineMethod
            split
            · simp [Heap.setClassPayload, Heap.set]
            · rfl,
        classPayload?_isSome_defineMethod h cls o name md]
      exact hc⟩

/-- **`alloc` satisfies the relativized transport, and this is what item 2 was
    for.** One fact does all four clauses: `Array.push` leaves every existing
    index where it was, so every function the type language reads answers the same
    at every id the old heap had. Unrelativized, this statement is *false* — at the
    fresh id `className` moves from `"Object"` to the allocated class's name — and
    that falsity, not `ancestors_congr`'s fuel, is what blocked the producer (L142,
    `scripts/alloc_probe.lean`).

    Stated over the pushed heap rather than over `Heap.alloc`'s pair so that the
    producer's consecution case can use it after destructuring; `alloc` is
    literally `(h.objs.size, ⟨h.objs.push obj⟩)`. -/
theorem typeAgree_of_get {h h' : Heap} (hsz : h.objs.size ≤ h'.objs.size)
    (hget : ∀ o, o < h.objs.size → h'.get o = h.get o) : TypeAgree h h' := by
  refine ⟨fun o ho => ?_, fun k hk => ?_, fun k hk => ?_, fun o ho hp => ?_,
    fun o ho hc => ?_⟩
  · simp only [classOf, hget o ho]
  · simp only [className, Heap.classPayload?, hget k hk]
  · simp only [Heap.classPayload?, hget k hk]
  · -- The `plainRecv` clause is where the *implication* earns its keep: the bound
    -- gets wider, so the two `Bool`s are not equal in general — an object whose
    -- class is the fresh id can *become* plain — and only this direction holds.
    unfold plainRecv at hp ⊢
    rw [hget o ho]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp ⊢
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, hfz⟩, h4⟩ := hp
    refine ⟨⟨⟨⟨Nat.lt_of_lt_of_le h1 hsz, ?_⟩, h3⟩, hfz⟩, h4⟩
    -- L147: the class clause transports because being a class puts the id *in
    -- bounds* (`classPayload?_isSome_lt`), which is where `get` agreement applies.
    have hb : (h.get o).klass < h.objs.size := classPayload?_isSome_lt h2
    simp only [Heap.classPayload?, hget _ hb]
    exact h2
  · -- L185's clause, and the `get` agreement does all of it: `classRecv` reads the
    -- bound, two id comparisons and the payload, and all four are functions of
    -- `h.get o`.
    unfold classRecv at hc ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hc ⊢
    refine ⟨⟨⟨Nat.lt_of_lt_of_le hc.1.1.1 hsz, hc.1.1.2⟩, hc.1.2⟩, ?_⟩
    simp only [Heap.classPayload?, hget o ho]
    exact hc.2

/-- The four field facts, for `bindIvar` specifically (L191). `Heap.set` rewrites one
    slot with an object that differs from it in `ivars` alone, and `Array.set!` leaves
    the size where it was. -/
theorem bindIvar_fields {m : Machine} {x : String} {v : Value} :
    IvarOnly m.heap (bindIvar m x v).heap := by
  unfold bindIvar
  cases hs : m.currentFrame.self with
  | ref o =>
    refine ⟨by simp [Heap.set], ?_, ?_, ?_, ?_⟩ <;>
      (intro j
       by_cases hj : j = o
       · subst hj
         by_cases hb : j < m.heap.objs.size
         · simp only [Heap.get, Heap.set]
           rw [objs_getD_set!_self _ _ _ hb]
         · simp only [Heap.get, Heap.set]
           rw [objs_getD_set!_oob _ _ _ hb]
       · simp only [Heap.get, Heap.set]
         rw [objs_getD_set!_ne _ _ _ _ hj])
  | _ => exact ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- **What `bindIvar` writes, read back** (L196). Three facts, and they are the three
    cases the `@x = e` consecution splits on now that a row can claim something about
    the slot: another object is untouched, the written object's *other* names read the
    old list (the `filter` removes only `x`), and the written name reads the new value.

    `find?_filter_ne` is reused rather than reproved — it was written at F1a for the
    *method* table, which is the same association-list shape. -/
theorem bindIvar_get_ne {m : Machine} {x : String} {v : Value} {o o' : ObjId}
    (hsf : m.currentFrame.self = .ref o) (hne : o' ≠ o) :
    (bindIvar m x v).heap.get o' = m.heap.get o' := by
  unfold bindIvar
  rw [hsf]
  simp only [Heap.get, Heap.set]
  rw [objs_getD_set!_ne _ _ _ _ hne]

theorem bindIvar_ivars_self {m : Machine} {x : String} {v : Value} {o : ObjId}
    (hsf : m.currentFrame.self = .ref o) (hb : o < m.heap.objs.size) :
    ((bindIvar m x v).heap.get o).ivars
      = (x, v) :: (m.heap.get o).ivars.filter (·.1 != x) := by
  unfold bindIvar
  rw [hsf]
  simp only [Heap.get, Heap.set]
  rw [objs_getD_set!_self _ _ _ hb]

/-- **A write that touches only `ivars`** (L191). Every function `TypeAgree` reads —
    `classOf`, `className`, `classPayload?`, `plainRecv`, `classRecv` — is a function
    of `{size, klass, eigen, payload, frozen}`, and an instance-variable write moves
    none of them. Stated over those four fields rather than over `get`, because
    `get` *does* change at the written id: that is the whole difference between this
    lemma and `typeAgree_of_get`. -/
theorem typeAgree_of_fields {h h' : Heap} (hsz : h.objs.size = h'.objs.size)
    (hkl : ∀ o, (h'.get o).klass = (h.get o).klass)
    (hei : ∀ o, (h'.get o).eigen = (h.get o).eigen)
    (hpl : ∀ o, (h'.get o).payload = (h.get o).payload)
    (hfz : ∀ o, (h'.get o).frozen = (h.get o).frozen) : TypeAgree h h' := by
  have hcp : ∀ k, h'.classPayload? k = h.classPayload? k := by
    intro k; simp only [Heap.classPayload?, hpl k]
  refine ⟨fun o _ => ?_, fun k _ => ?_, fun k _ => ?_, fun o _ hp => ?_, fun o _ hc => ?_⟩
  · simp only [classOf, hei o, hkl o]
  · simp only [className, hcp k]
  · rw [hcp k]
  · unfold plainRecv at hp ⊢
    rw [hkl o, hei o, hpl o, hfz o, hcp _, ← hsz]
    exact hp
  · unfold classRecv at hc ⊢
    rw [hcp o, ← hsz]
    exact hc

theorem typeAgree_alloc (h : Heap) (obj : Object) : TypeAgree h ⟨h.objs.push obj⟩ :=
  typeAgree_of_get (by simp) (fun o ho => by
    simp only [Heap.get, Array.getD_eq_getD_getElem?, Array.getElem?_push,
      if_neg (Nat.ne_of_lt ho)])

/-- **And so does anything that only grows the heap** (L145). `PlainGrow`'s extra
    clause — `classPayload?` agrees at *every* id — is what resolution needs and the
    type transport does not, so the type half of a producer's step is discharged by
    the two weaker fields. Recorded here rather than in `Proof/HeapGrow.lean` because
    `TypeAgree` is the type judgement's vocabulary, not the heap's. -/
theorem typeAgree_of_plainGrow {h h' : Heap} (hg : PlainGrow h h') : TypeAgree h h' :=
  typeAgree_of_get hg.size hg.get

/-- Transport of the value judgement. **No longer `id`** (F1b): the `.ref` arm
    reads three of `TypeAgree`'s four clauses, which is what L137 threaded the
    heap in for and what it predicted would happen here rather than at the use
    sites. The immediate arms are still `id`, and that asymmetry is the whole
    reason the class arm could land as one commit. -/
theorem ValueTy.congr {h h' : Heap} {v : Value} {τ : Ty} (ha : TypeAgree h h')
    (hv : ValueTy h v τ) : ValueTy h' v τ := by
  -- L193: the *exact* type is what transports, and `τ` rides along untouched —
  -- which is why the relation cost this lemma nothing but a `refine` at the top.
  obtain ⟨σ, hσ, hs⟩ := hv
  refine ⟨σ, ?_, hs⟩
  cases v with
  | ref o =>
    -- L143: each clause is instantiated at an id the *hypothesis* supplies, which
    -- is the whole point of the relativization — the two bounds come from
    -- `valueTy?` itself (`plainRecv`'s two clauses read back out), so the
    -- transport is never asked about an id the old heap did not have.
    have hb : o < h.objs.size := valueTy_ref_lt ⟨σ, hσ, hs⟩
    -- **Two branches since L185**, and they read different clauses of `TypeAgree`:
    -- the plain one needs `classOf`/`className` agreement at the *class* id, the
    -- class-object one needs only `className` at `o` itself — because its type is
    -- keyed on the object's own name rather than on its dispatch class.
    by_cases hp : plainRecv h o
    · have hk : classOf h (.ref o) < h.objs.size := valueTy_ref_klass_lt hp
      rw [show σ = Ty.cls (className h (classOf h (.ref o))) from by
        simpa [valueTy?, hp] using hσ.symm]
      simp [valueTy?, ha.2.2.2.1 o hb hp, ha.1 o hb, ha.2.1 _ hk]
    · by_cases hc : classRecv h o
      · -- A class receiver is not a plain one, so the `if` chain takes the second
        -- branch in `h'` too — `plainRecv` refuses a `.cls` payload and `classRecv`
        -- *is* having one.
        have hc' : classRecv h' o = true := ha.2.2.2.2 o hb hc
        have hnp : plainRecv h' o = false := by
          unfold classRecv at hc'
          unfold plainRecv
          simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hc' ⊢
          obtain ⟨cp, hcp⟩ := hc'.2
          unfold Heap.classPayload? at hcp
          cases hpl : (h'.get o).payload <;> simp_all
        rw [show σ = Ty.clsOf (className h o) from by
          simpa [valueTy?, hp, hc] using hσ.symm]
        simp [valueTy?, hnp, hc', ha.2.1 o hb]
      · simp [valueTy?, hp, hc] at hσ
  | _ => simp_all [valueTy?]

/-- **Transport across a heap-writing step.** The in-bounds clause is what makes
    it available: `TypeAgree` relativizes every one of its equalities to ids the
    old heap had (L143), so a predicate that names an `ObjId` has to say the id is
    one of them. `classPayload?`-ness supplies the bound
    (`classPayload?_isSome_lt`), which is why that clause is here rather than
    borrowed from `FrameConforms` — the two lists are different, so the borrow
    would need a lemma relating them for no gain. -/
theorem StackCtx.heap_congr {h h' : Heap} (ha : TypeAgree h h') {frames : Array Frame} :
    ∀ {st : List FrameId} {cs : List FrameCtx},
      StackCtx h frames st cs → StackCtx h' frames st cs
  | [], [], hs => hs
  | fid :: fids, c :: cs, hs => by
      have hlt : (frames.getD fid default).defmod < h.objs.size :=
        classPayload?_isSome_lt hs.1
      refine ⟨?_, ?_, hs.2.2.1, fun sc hsc => ValueTy.congr ha (hs.2.2.2.1 sc hsc),
        hs.2.2.2.2.1, hs.2.2.2.2.2.1, StackCtx.heap_congr ha hs.2.2.2.2.2.2⟩
      · rw [ha.2.2.1 _ hlt]; exact hs.1
      · rw [ha.2.1 _ hlt]; exact hs.2.1
  | [], _ :: _, hs => hs.elim
  | _ :: _, [], hs => hs.elim

theorem ValuesTy.congr {h h' : Heap} (ha : TypeAgree h h') :
    ∀ {vs : List Value} {τs : List Ty}, ValuesTy h vs τs → ValuesTy h' vs τs
  | [], [], hv => hv
  | _ :: _, _ :: _, hv =>
      ⟨⟨hv.1.choose, ValueTy.congr ha hv.1.choose_spec.1, hv.1.choose_spec.2⟩,
       ValuesTy.congr ha hv.2⟩
  | [], _ :: _, hv => absurd hv (by simp [ValuesTy])
  | _ :: _, [], hv => absurd hv (by simp [ValuesTy])

theorem FrameConforms.congr {h h' : Heap} {Γ : Env} {f : Frame}
    (ha : TypeAgree h h') (hc : FrameConforms h Γ f) : FrameConforms h' Γ f :=
  -- L154's definee clause transports by `TypeAgree`'s **third** component, which was
  -- already there for `TyClass` — the bound it needs comes from the clause itself,
  -- since `classPayload?` answers `none` out of bounds.
  ⟨hc.1, by rw [ha.2.2.1 f.defmod (classPayload?_isSome_lt hc.2.1)]; exact hc.2.1,
   fun x τ hg => ValueTy.congr ha (hc.2.2 x τ hg)⟩

theorem FramesOk.heap_congr {h h' : Heap} {frames : Array Frame}
    (ha : TypeAgree h h') :
    ∀ {fids : List FrameId} {Γs : List Env}, FramesOk h frames fids Γs →
      FramesOk h' frames fids Γs
  | [], [], hf => hf
  | _ :: fids, _ :: Γs, hf =>
      ⟨hf.1, hf.2.1, FrameConforms.congr ha hf.2.2.1, FramesOk.heap_congr ha hf.2.2.2⟩
  | [], _ :: _, hf => absurd hf (by simp [FramesOk])
  | _ :: _, [], hf => absurd hf (by simp [FramesOk])

/-- `setLocal` writes `locals`, so the heap rides through — needed wherever
    `FramesOk` is re-established at a machine `setLocal` produced. -/
theorem setLocal_heap {m : Machine} (x : String) (v : Value) :
    (m.setLocal x v).heap = m.heap := by simp [Machine.setLocal]


end Static
end Proof
end RubyCore
