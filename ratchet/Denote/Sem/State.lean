import Ratchet.Judge
import Denote.Grow
import Denote.Sem.Trans

/-!
# `Denote/Sem/State.lean` — evaluation, and what it means for a machine to *match* a
judgment's state

`Judge κ Γ I e τ Γ' I'` is a claim about seven things, six of which are state: a context, an
incoming local environment and ivar spine, an outgoing pair of the same. `Denote/Den.lean`
gave one of the seven — `τ` — a meaning. This file gives the other six theirs, and defines the
one primitive every obligation is phrased over: **what it is to evaluate `e`**.

## `Evals` — running one expression

`evalFrom m e` redirects `m` to evaluate `toRuby e` with an **empty continuation**, so the
expression's own value becomes the machine's result (`applyKont` on `[]` is `.done`). It is
`Denote/Apply.lean`'s `applyIn` move without the pushed frame: the frame stack is left exactly
as it was, because `Γ` and `I` are claims about the *current* frame and its `self`, and a
judgment about `x + 1` has to be evaluated where `x` is bound.

`Evals m e v m'` is then "evaluating `e` from `m` returns `v`, leaving `m'`", existentially
over fuel — which is not a weakening (a run that has landed on `.value` stays there), just the
model's own iteration discipline.

**Everything downstream is partial correctness.** A run that raises, diverges, gates
(`.unsupported`) or jumps imposes no obligation, for the same reason `Denote/Den.lean`'s arrow
is stated over `.value` outcomes only: `Ty` has no totality or effect discipline, and
`Ty.never` — the type of an expression that *does not return* — is defined by exactly this
asymmetry. Ruling out the type-stuck outcomes is a **different theorem** on a different axis
(`../type-safety-by-reachability.md`, and `Semantics/Interp.lean`'s `typeStuck`), and mixing
the two into one obligation would make every rung carry both burdens at once. `StuckFree`
below states that axis so it is on file rather than implied, and nothing in the ladder uses
it yet.

## `StateOk` — conformance

The judgment's state is a *description*; a machine is the thing described. `StateOk κ Γ I m`
is the conjunction of one component per piece of that description, and the components are
separate definitions rather than an inlined `∧`-chain for a reason that will matter at every
clink: a rule's proof needs to *use* two or three of them and *re-establish* the same two or
three, so each one wants its own name, its own monotonicity lemma, and its own place to record
what it is not saying.

Two of them deserve their reasoning up front.

**`EnvOk` gives `Ty.sameAs` its meaning.** The alias type (`Ratchet/Ty.lean`, tier 12) is
documented as "a fact about a binding, not about a value" — `Judge.var` strips it, no
expression has it. Under a denotation the fact becomes statable: `x : sameAs y τ` means the
two locals hold **the same object** (`Value.identEq`, the model's own `equal?`) *and* that
object is in `τ`. That is the first time the alias has had a meaning outside the checker's
own bookkeeping, and it is what a proof of `Judge.narrowEnvs`' soundness will have to consume.

**`ClosuresOk` closes `Denote/Den.lean`'s stated `idx` gap.** `Ty.clos idx` indexes
`Ctx.closures`, a table of `Ratchet.Expr` block literals; a live Proc holds a
`RubyCore.Closure`. With `toRuby` (`Denote/Sem/Trans.lean`) those are comparable, so
`closTblOk` can say what `denM`'s `clos` arm could not: this Proc *is* the block literal the
type names.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## Evaluating one expression -/

/-- `m`, redirected to evaluate `e` with an empty continuation. The frame stack is untouched
(unlike `applyIn`, which pushes one) so that `Γ`/`I` still describe the frame the expression
is evaluated in. -/
def evalFrom (m : Machine) (e : Ratchet.Expr) : Machine :=
  { m with ctl := .eval (toRuby e), kont := [] }

/-- "Evaluating `e` from `m` returns `v`, leaving machine `m'`." -/
def Evals (m : Machine) (e : Ratchet.Expr) (v : Value) (m' : Machine) : Prop :=
  ∃ fuel, Interp.run fuel (evalFrom m e) = .value v m'

/-- **The other axis, stated and unused.** Evaluating `e` from `m` never lands on a type-stuck
outcome — the `NoMethodError`/`ArgumentError`/`TypeError` family `Semantics/Interp.lean`'s
`typeStuck` names. This is what `../type-safety-by-reachability.md` is about, and it is
deliberately *not* part of `SemJudge`: a rung that had to prove both value-typing and
stuck-freedom would be two rungs wearing one number. Kept here so the second axis is on file
with the first, and so the eventual composed statement has a name to compose. -/
def StuckFree (m : Machine) (e : Ratchet.Expr) : Prop :=
  ∀ fuel, Semantics.typeStuck (Interp.run fuel (evalFrom m e)) = false

/-! ## Calling a named method

`AsmsOk` is a claim about *calls*, so it needs the send counterpart of
`Denote/Apply.lean`'s `applyIn`: a machine that performs an implicit-self send with
pre-bound argument values. Same trick for the same reason (values are not syntax), and the
same frame discipline — `frames` is extended, never rewritten — with one difference: the
pushed frame inherits `m`'s `self`, `defmod` and `cref`, because *which* method an
implicit-self send finds depends on all three. -/

/-- `m`, redirected to evaluate `name(args…)` as an implicit-self send from `m`'s own `self`. -/
def sendIn (m : Machine) (name : String) (args : List Value) : Machine :=
  let n := args.length
  let fr : RubyCore.Frame :=
    { m.currentFrame with
      locals := (List.range n).map (fun i => (argName i, args.getD i .nil)),
      kind := .toplevel, meth := "", blk := none, callBlk := none, captured := none }
  { m with
    ctl := .eval (.send none name ((List.range n).map (fun i => .var .lvar (argName i))) none),
    kont := [],
    stack := [m.frames.size],
    frames := m.frames.push fr }

/-- "The implicit-self send `name(args…)` from `m` returns `v`, leaving `m'`." -/
def SendReturns (m : Machine) (name : String) (args : List Value) (v : Value)
    (m' : Machine) : Prop :=
  ∃ fuel, Interp.run fuel (sendIn m name args) = .value v m'

/-! ## Conformance, component by component -/

/-- The locals match `Γ`: every name `Γ` types holds a value of that type, and an **alias**
additionally holds the *same object* as its target.

`Value.identEq` is the model's `equal?` (identity for refs, value identity for immediates) —
the right relation, because what `sameAs` claims is that a later assignment through one name is
visible through the other, and that is object identity, not `==`. -/
def EnvOk (Γ : Env) (m : Machine) : Prop :=
  ∀ x τ, envGet? Γ x = some τ →
    denM (stripAlias τ) m (m.getLocal x) ∧
    (∀ y ρ, τ = .sameAs y ρ → (m.getLocal x).identEq (m.getLocal y) = true)

/-- `self`'s instance variables match the spine `I`. -/
def SelfSpineOk (I : Ty) (m : Machine) : Prop :=
  denSpine I m (ivarOf m.heap m.currentFrame.self)

/-- A `Ty.clos` really names *this* Proc: the heap closure's parameters and body are the
translation of the table entry `idx` points at.

The captured environment and creation `self` are **not** compared here — `denM`'s `clos` arm
already does that (`closLocal`/`closSelf`), and the split is the one `Ty.clos`'s docstring
draws: the *table* holds `(params, body)`, which two syntactically identical blocks share, and
the *type* holds the environment, which they do not. -/
def closTblOk (K : ClosTable) (idx : Nat) (m : Machine) (f : Value) : Prop :=
  ∃ c cl, closGet? K idx = some c ∧ procClosure? m.heap f = some cl ∧
    cl.params = toRubyParams c.params ∧ cl.body = toRuby c.body

/-- The class table describes real classes. Per entry: a class object of that name exists,
its superclass is the one recorded (`none` meaning `Object`), and every method the table lists
is installed on it with the translated parameters and body.

`.smethods` (singleton methods) are checked on the class's eigenclass. Modules
(`Cls.isMod`) are the classes `ctorGet?` refuses to allocate; that refusal is a *precision*
fact about `Judge.newInst` rather than a conformance fact about the heap, so it is not here. -/
def ClassesOk (C : CTable) (m : Machine) : Prop :=
  ∀ c ∈ C, ∃ k, classNamed? m.heap c.name = some k ∧
    (∀ d ∈ c.methods, ∃ md, (m.heap.classPayload? k).bind
        (fun cp => (cp.methods.find? (·.1 == d.name)).map (·.2)) = some md ∧
      md.params = toRubyParams d.params ∧ md.body = toRuby d.body ∧ md.undefined = false)

/-- The top-level `def` table describes methods installed on `Object`, and *only* the ones a
preceding statement performed — which is the whole soundness content of `DefTable`'s
"already", per its docstring: a whole-program table would certify `foo(); def foo; end`. -/
def DefsOk (D : DefTable) (m : Machine) : Prop :=
  ∀ d ∈ D, ∃ md, (m.heap.classPayload? Boot.objectId).bind
      (fun cp => (cp.methods.find? (·.1 == d.name)).map (·.2)) = some md ∧
    md.params = toRubyParams d.params ∧ md.body = toRuby d.body ∧ md.undefined = false

/-- **The assumption table's semantic content**, and the one component that is itself a
statement about running the semantics rather than about the shape of the heap.

`Asm ⟨name, argTys, ret⟩` is the checker's device for breaking the cycle a recursive method
creates: "assume a call to `name` on arguments of these types returns `ret`". `Judge`'s own
docstring says to read a derivation with a non-empty `κ.asms` as a **conditional claim**, and
this is that condition, made precise: every such call that returns, returns a value in `ret`.

So `AsmsOk` is not a hypothesis a clink discharges — it is a hypothesis a clink *carries*, and
the eventual `Judge.callDef` obligation is where the circularity is cut for real (by induction
on something that decreases, not by assuming the conclusion). Recording it as a component of
`StateOk` is what makes the conditionality visible in every obligation's statement instead of
in a comment.

**The `∀ m₂, Ext m m₂` quantifier** is here for the reason `denM`'s arrow arm has it
(`Denote/Den.lean` §The arrow arm point 5), and this is the *other* component that quantifies
over runs: a run from a heap with one more object in it is not the run from the heap without
it, so the unquantified form does not survive an allocating step and no rung that allocates
could re-establish it. Quantifying over `Ext`-futures makes it monotone by `Ext.trans`;
`Ext.refl` recovers the unquantified reading, so this is a strengthening of the assumption a
`Judge.callDef` rung will have to discharge, not a weakening. -/
def AsmsOk (Δ : AsmTable) (m : Machine) : Prop :=
  ∀ a ∈ Δ, ∀ m₂, Ext m m₂ → ∀ (args : List Value), DenAll a.argTys m₂ args →
    ∀ v m', SendReturns m₂ a.name args v m' → denM a.ret m' v

/-- The running frame is the one `Ctx.frame` describes: same method name, and `self`'s class
is the recorded receiver class. `none` means "outside any method body", i.e. the frame is a
toplevel or class-body frame. -/
def FrameOk (fr : Option Ratchet.Frame) (m : Machine) : Prop :=
  match fr with
  | none => m.currentFrame.kind ≠ .method
  | some f =>
      m.currentFrame.meth = f.methName ∧
      isAName m.heap m.currentFrame.self f.recvClass = true

/-- `self`'s type. `none` is top level, where `Judge` declines to type `self'` at all. -/
def SelfTyOk (σ? : Option Ty) (m : Machine) : Prop :=
  match σ? with
  | none => True
  | some σ => denM σ m m.currentFrame.self

/-- The block the running method was called with, as a `Ty.clos`. `none` means the frame has
none, and that has to be checked too: `yield` with no block raises `LocalJumpError`, so a
context claiming `blockTy = none` while a block is present would be describing a different
program, not a smaller one. -/
def BlockTyOk (β? : Option Ty) (m : Machine) : Prop :=
  match β? with
  | none => m.currentFrame.blk = none
  | some β => ∃ b, m.currentFrame.blk = some b ∧ denM β m b

/-- Every closure in the whole-program table is a real block literal of the program. Vacuous
as stated — the table is syntax, and its *use* is `closTblOk`, applied where a `Ty.clos`
appears. Kept as a named component so `StateOk` has one field per `Ctx` field and a future
clink that needs a table invariant has somewhere to put it. -/
def ClosuresOk (_K : ClosTable) (_m : Machine) : Prop := True

/-- `"::LIMIT"` -> `"LIMIT"`: `Ctx.consts` is keyed by absolute path, the heap's toplevel
constant table is not. Spelled out rather than using `String.stripPrefix` (deprecated, and its
replacement returns a `Slice`). -/
def stripColons (p : String) : String :=
  if p.startsWith "::" then String.ofList (p.toList.drop 2) else p

/-- The constant table: each entry's absolute path resolves in the heap to a value of the
recorded type. Keys are absolute (`"::LIMIT"`), so the leading `::` is stripped for the
heap's toplevel constant lookup. -/
def ConstsOk (cs : Env) (m : Machine) : Prop :=
  ∀ p τ, envGet? cs p = some τ →
    ∃ v, constLookup m.heap (stripColons p) = some v ∧ denM τ m v

/-- `private_constant`'s hidden keys. `Judge.constPath`'s own docstring calls this *precision
rather than soundness*: hiding a constant can only make the checker refuse a program, never
accept a bad one. So there is nothing for a machine to conform to. -/
def PrivConstsOk (_ps : List String) (_m : Machine) : Prop := True

/-! ## The heap itself

Two components that correspond to no `Ctx` field, because they are not claims about the
*description* — they are the two facts about the machine that a rule allocating an object
needs and that nothing else supplies. Both were forced by `Judge.strLit`
(`Denote/Sem/notes.md` §The fourth stall point, item 1: "`StateOk` says nothing about the
boot classes"). -/

/-- **The ancestor walk has finished before its fuel runs out.** `ancestors` is fuel-bounded
by `h.objs.size + 1` (`RubyCore/Heap.lean`, L73: a `partial def` would be opaque to the
kernel), so *growing the heap grows the fuel* — and without this, the walk at a machine and
the walk at the same machine one allocation later are two different computations. Named
`Saturated` and proved to do exactly this job in the model's own metatheory
(`RubyCore/Proof/AncestorsGrow.lean`), which is why it is imported rather than restated.

Not free, and not hygiene: `RubyCore.Proof.saturatedB` is the `Bool` that checks it, measured
`true` at the prelude-booted heap. -/
abbrev HeapSaturated (m : Machine) : Prop := Proof.Saturated m.heap

/-- **The core classes are what they are.**

`Judge.strLit` concludes `.cls "String"`, whose denotation resolves the *name* `"String"`
through the heap's own constant table (`classNamed?`). A machine conformant with
`(κ, Γ, I)` is not otherwise required to have a class named `String` at all — `κ.classes` is
the *program*'s class table — so without this component the rule's conclusion is not
derivable from its hypothesis. That is a real gap in the description, not a missing lemma:
the heap's core classes are what they are, and saying so is a conformance fact.

Four clauses, and each is used once by the `strLit` rung: the name resolves to the boot id;
`String` is its own ancestor (the conclusion `isA … stringId`); `String` is a `BasicObject`
and `BasicObject` is only itself (together, `Ext.freshBasic` at the pushed object — see
`Denote/Ext.lean` on why a *dangling* reference is what makes that clause necessary).

**This will grow.** `arrayLit`, `hashLit` and most of `prim` conclude a builtin class type
too, and each will want its own row here. Kept as a structure with named fields rather than
a table so that a rung cites the clause it needs and an unused clause is visible. -/
structure CoreOk (h : Heap) : Prop where
  /-- `BasicObject` has no superclass and no mixins, so its ancestor list is just itself. -/
  basicSelf : ancestors h Boot.basicObjectId = [Boot.basicObjectId]
  /-- The name `String` resolves to the boot `String` class. -/
  stringNamed : classNamed? h "String" = some Boot.stringId
  /-- `String` is a `String` … -/
  stringSelf : (ancestors h Boot.stringId).contains Boot.stringId = true
  /-- … and a `BasicObject`. -/
  stringBasic : (ancestors h Boot.stringId).contains Boot.basicObjectId = true

theorem CoreOk.ext {h h' : Heap} {m m₂ : Machine} (hm : m.heap = h) (hm₂ : m₂.heap = h')
    (he : Ext m m₂) (hc : CoreOk h) : CoreOk h' where
  basicSelf := by subst hm; subst hm₂; rw [he.ancestors]; exact hc.basicSelf
  stringNamed := by subst hm; subst hm₂; rw [he.classNamed?_eq]; exact hc.stringNamed
  stringSelf := by subst hm; subst hm₂; rw [he.ancestors]; exact hc.stringSelf
  stringBasic := by subst hm; subst hm₂; rw [he.ancestors]; exact hc.stringBasic

/-- **Conformance**: one conjunct per `Ctx` field, plus the two threaded pieces `Γ` and `I`,
plus the two heap facts above.

Nine `Ctx` fields, nine components, and the two that are `True` say so with a docstring rather
than by omission — a `StateOk` that quietly skipped a field would be a place for an unsound
rule to hide. -/
structure StateOk (κ : Ctx) (Γ : Env) (I : Ty) (m : Machine) : Prop where
  sat : HeapSaturated m
  core : CoreOk m.heap
  env : EnvOk Γ m
  selfSpine : SelfSpineOk I m
  classes : ClassesOk κ.classes m
  defs : DefsOk κ.defs m
  asms : AsmsOk κ.asms m
  frame : FrameOk κ.frame m
  closures : ClosuresOk κ.closures m
  blockTy : BlockTyOk κ.blockTy m
  selfTy : SelfTyOk κ.selfTy m
  consts : ConstsOk κ.consts m
  privConsts : PrivConstsOk κ.privConsts m

/-! ## Conformance survives an allocation

The theorem every allocating rung needs, and the one that pays for `Denote/Ext.lean` and
`Denote/Grow.lean`. Component by component, and the shape of each proof is the finding:

* Nine components are **rewrites** — they read the heap through `classPayload?`,
  `constLookup` or an in-range `Heap.get`, and read the frames through `currentFrame`, all of
  which `Ext` pins outright.
* `env`, `selfSpine`, `blockTy`, `selfTy` and `consts` additionally transport a `denM`, which
  is `denM_ext`.
* `frame` is the one that is only *monotone* (`isAName`), and `asms` is the one that is free
  by construction (`Ext.trans`) rather than proved — see its own docstring.

Nothing here is specific to a string literal: an allocating rung supplies the `Ext` and this
does the rest. -/
theorem StateOk_ext {κ : Ctx} {Γ : Env} {I : Ty} {m m₂ : Machine} (h : StateOk κ Γ I m)
    (he : Ext m m₂) : StateOk κ Γ I m₂ where
  sat := Proof.Saturated_grow he.shapeAgree he.size h.sat
  core := CoreOk.ext rfl rfl he h.core
  env := by
    intro x τ hx
    obtain ⟨hd, hid⟩ := h.env x τ hx
    refine ⟨?_, ?_⟩
    · rw [he.getLocal_eq]; exact denM_ext he hd
    · intro y ρ hτ; rw [he.getLocal_eq, he.getLocal_eq]; exact hid y ρ hτ
  selfSpine := by
    have := h.selfSpine
    unfold SelfSpineOk at this ⊢
    rw [he.currentFrame_eq, funext (he.ivarOf_eq m.currentFrame.self)]
    exact denSpine_ext he this
  classes := by
    intro c hc
    obtain ⟨k, hk, hm⟩ := h.classes c hc
    refine ⟨k, by rw [he.classNamed?_eq]; exact hk, ?_⟩
    intro d hd
    obtain ⟨md, h1, h2⟩ := hm d hd
    exact ⟨md, by rw [he.payload]; exact h1, h2⟩
  defs := by
    intro d hd
    obtain ⟨md, h1, h2⟩ := h.defs d hd
    exact ⟨md, by rw [he.payload]; exact h1, h2⟩
  asms := by
    intro a ha m₃ he₃ args hargs v m' hs
    exact h.asms a ha m₃ (he.trans he₃) args hargs v m' hs
  frame := by
    have h2 := h.frame
    unfold FrameOk at h2 ⊢
    cases hf : κ.frame with
    | none => rw [hf] at h2; rw [he.currentFrame_eq]; exact h2
    | some f =>
      rw [hf] at h2
      exact ⟨by rw [he.currentFrame_eq]; exact h2.1,
             by rw [he.currentFrame_eq]; exact he.isAName_mono h2.2⟩
  closures := trivial
  blockTy := by
    have h2 := h.blockTy
    unfold BlockTyOk at h2 ⊢
    cases hb : κ.blockTy with
    | none => rw [hb] at h2; rw [he.currentFrame_eq]; exact h2
    | some β =>
      rw [hb] at h2
      obtain ⟨b, hb1, hb2⟩ := h2
      exact ⟨b, by rw [he.currentFrame_eq]; exact hb1, denM_ext he hb2⟩
  selfTy := by
    have h2 := h.selfTy
    unfold SelfTyOk at h2 ⊢
    cases hσ : κ.selfTy with
    | none => trivial
    | some σ => rw [hσ] at h2; rw [he.currentFrame_eq]; exact denM_ext he h2
  consts := by
    intro p τ hp
    obtain ⟨v, hv1, hv2⟩ := h.consts p τ hp
    exact ⟨v, by rw [he.constLookup_eq]; exact hv1, denM_ext he hv2⟩
  privConsts := trivial

#print axioms StateOk_ext

end Ratchet.Denote
