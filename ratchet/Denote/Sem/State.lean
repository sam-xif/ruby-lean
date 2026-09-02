import Ratchet.Judge
import Denote.Local
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
two locals hold **the same object** (`Value` equality — see `EnvOk` on why not `identEq`) *and* that
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

What `sameAs` claims is that a later assignment through one name is visible through the
other, and that is **object identity**, not `==`. In this model a `Value` *is* the object
reference — `.ref o` for a heap object, the immediate itself otherwise — so object identity is
`Value` equality, and that is what this states.

**Not `Value.identEq`** (the model's own `equal?`), which was the first reading and is wrong in
both directions at `Float` (clink 47). `identEq (.flt a) (.flt b)` is `a == b`, so it calls
`0.0` and `-0.0` the same object (they are two different values, and assigning through one is
not visible through the other) and calls `NaN` and itself *different* ones (`Float`'s `==` is
false at `NaN`, so `identEq v v` is not reflexive) — which made `Judge.vasgnAlias`'s obligation
false at a local holding `NaN`, for a reason that has nothing to do with aliasing. The `equal?`
quirk is the model's and is recorded in `found-issues.md`; the denotation should not inherit
it. -/
def EnvOk (Γ : Env) (m : Machine) : Prop :=
  (∀ x τ, envGet? Γ x = some τ →
    denM (stripAlias τ) m (m.getLocal x) ∧
    (∀ y ρ, τ = .sameAs y ρ → m.getLocal x = m.getLocal y)) ∧
  -- **…and the environment is complete**: a name it does not mention reads as `nil`.
  --
  -- Forced by `Judge.if'` (clink 55), and it is `SelfSpineOk`'s second conjunct one piece of
  -- state over — same shape, same reason. `joinEnv` joins a name bound in only one branch
  -- against **`.nilT`**, deliberately ("the parser declares a local at the assignment's
  -- syntactic position, so `if false then y = 1 end; y` evaluates to `nil`"), so using a
  -- branch's `StateOk` to establish the join's requires knowing that a name the branch's `Γ`
  -- is silent about reads as `nil`. The first conjunct is a lower bound and says nothing
  -- about such a name.
  --
  -- This **strengthens `StateOk`**, which sits on the left of `SemJudge`'s implication, so it
  -- weakens all 83 obligations at once — the cost `notes.md` warns about for `Evals`. It is
  -- the right move here for the reason `SelfSpineOk`'s was: the completeness is the
  -- *checker's own convention*, stated where the semantics can see it, rather than a
  -- convenience. `Denote/Sanity.lean`'s boot machine satisfies it.
  (∀ x, envGet? Γ x = none → m.getLocal x = .nil)

/-- `self`'s instance variables match the spine `I`, **and the spine is complete**: an ivar
the spine does not mention reads as `nil`.

The second conjunct was forced by `Judge.ivarRead` (clink 48), and it is the invariant that
rule's own docstring already named — *"the default is sound only because the spine is complete
— every ivar the object has ever been given a value for appears in it"*. `Judge.ivarRead`
types `@x` as `(ivarGet? I x).getD .nilT`, so at a spine that is silent about `@x` it claims
`@x : Nil`; the first conjunct alone is a **lower** bound (`Denote/Den.lean` says so of
`denM`'s `inst` arm: "ivars the type does not mention are unconstrained"), so without this
clause a conformant machine could hold `@x = 7` at `I = .ivar0` and the rule would be false of
the semantics.

Stated as "reads as `nil`" rather than "is absent from the object", because that is what the
rule needs and it is the weaker of the two: CRuby's `@x = nil` and an unset `@x` are
indistinguishable to a read, and `Judge.ivarAsgn` at a `nil` right-hand side would have to
re-establish the stronger form without being able to remove the entry.

Note the asymmetry with `EnvOk`, which needs no completeness clause: there is no rule that
types an *unbound local* — `Judge.var` requires `envGet? Γ x = some τ` — while `ivarRead` is
total in `x` on purpose, because in Ruby reading an unset ivar is legal and yields `nil`. -/
def SelfSpineOk (I : Ty) (m : Machine) : Prop :=
  denSpine I m (ivarOf m.heap m.currentFrame.self) ∧
  ∀ x, ivarGet? I x = none → ivarOf m.heap m.currentFrame.self x = .nil

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

**The `∀ m₂, Later m m₂` quantifier** is here for the reason `denM`'s arrow arm has it
(`Denote/Den.lean` §The arrow arm point 5), and this is the *other* component that quantifies
over runs: a run from a heap with one more object in it is not the run from the heap without
it, so the unquantified form does not survive an allocating step and no rung that allocates
could re-establish it. The same is true of a **rebinding**: `sendIn` pushes a frame that
captures nothing, but the frame *array* it runs against is the caller's, and a Proc in the
heap can reference a frame the assignment just mutated. Quantifying over `Later`-futures makes
it monotone by `Later.trans`; `Later.refl` recovers the unquantified reading, so this is a
strengthening of the assumption a `Judge.callDef` rung will have to discharge, not a
weakening. -/
def AsmsOk (Δ : AsmTable) (m : Machine) : Prop :=
  ∀ a ∈ Δ, ∀ m₂, Later m m₂ → ∀ (args : List Value), DenAll a.argTys m₂ args →
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

/-! ## Reading a constant *from where the machine is standing*

`Denote/Val.lean`'s nominal probes (`classNamed?`, `isAName`, `isClassRefNamed`) all resolve a
name through **the toplevel constant table** — `constLookup`, which is `Object`'s own `consts`.
The machine does not: `evalExpr`'s `.const` arm runs CRuby's two-phase rule, the *lexical*
phase over the current frame's `cref` first and the *inheritance* phase from its `defmod`
second. The two agree at a toplevel frame and can disagree anywhere else, and the gap is not
cosmetic — it is exactly `class A; class Foo; end; end`, where `Foo` inside `A` names a
different object from the toplevel `Foo`.

So the three `.const` rules (`constCls`, `constBuiltin`, `constExc`) each conclude `.clsOf n`,
whose denotation is the *toplevel* class object, about a value the machine produced by the
*lexical* walk. Nothing in `Ctx` records where the frame is standing, so nothing in `StateOk`
made those two the same value, and the rules' obligations were not derivable. That is stall
point (1) again — a missing conformance component, not a missing lemma. -/

/-- The machine's own constant resolution for `n`, transcribed from `Interp.evalExpr`'s
`.const` arm so a rung can rewrite with it. Lexical phase (each `cref` scope's *own*
constants, innermost first), then the inheritance phase from `defmod`. -/
def constResolveAt (m : Machine) (n : String) : Option Value :=
  (m.currentFrame.cref.firstM (fun c => constOwn m.heap c n)).orElse
    (fun _ => constLookupFrom m.heap m.currentFrame.defmod n)

/-- **The current scope resolves constants exactly as the toplevel table does.**

Both directions are used, and both by the same three rungs:

* *left to right* — the machine produced a value, and the rule's conclusion is about the value
  `classNamed?` finds. Without this the two are unrelated.
* *right to left* — `ClassesOk`/`CoreOk` say the toplevel table has the class, and the rung
  needs the machine's `.const` arm to *find* it rather than raise `NameError`.

What it costs, stated rather than hidden: a machine standing inside `class A; class Foo; end;
… end` is not conformant, so the three `.const` obligations say nothing there. That is the
honest scope of the rules as written — none of `constCls`/`constBuiltin`/`constExc` has a
premise about the frame, and each of them concludes about the *toplevel* `Foo`. A rule that
wants the nested reading needs `Ctx` to record the cref, which it does not; see
`Denote/Sem/notes.md` §The eighth stall point.

It is satisfiable at the real booted machine and `Denote/Sanity.lean` proves it there, from a
decidable three-clause `Bool`: `cref = [Object]`, `defmod = Object`, and every *other* ancestor
of `Object` (`Kernel`, `BasicObject`) owns no constants — which is what makes the inheritance
phase agree with `Object`'s own table rather than overshoot it. -/
def ConstScopeOk (m : Machine) : Prop :=
  ∀ n, constResolveAt m n = constLookup m.heap n

/-- Both resolutions read the heap only through `classPayload?` and `ancestors`, and the frame
only through `currentFrame` — the three things `Ext` pins outright. -/
theorem ConstScopeOk.ext {m m₂ : Machine} (he : Ext m m₂) (h : ConstScopeOk m) :
    ConstScopeOk m₂ := by
  intro n
  have hl : constLookup m₂.heap n = constLookup m.heap n := by
    simp only [constLookup, he.payload]
  have hr : constResolveAt m₂ n = constResolveAt m n := by
    simp only [constResolveAt, constOwn, constLookupFrom, he.payload, he.ancestors,
      he.currentFrame_eq]
  rw [hr, hl]; exact h n

/-- A rebinding writes `locals` and nothing else, so every field either resolution reads is
copied (`currentFrame_setLocal_cref`/`_defmod`, `setLocal_heap`). -/
theorem ConstScopeOk.setLocal {m : Machine} (x : String) (w : Value) (h : ConstScopeOk m) :
    ConstScopeOk (m.setLocal x w) := by
  intro n
  have hr : constResolveAt (m.setLocal x w) n = constResolveAt m n := by
    simp only [constResolveAt, setLocal_heap, currentFrame_setLocal_cref,
      currentFrame_setLocal_defmod]
  rw [hr, setLocal_heap]; exact h n

/-- The constant table, **stated over the lookup function rather than over the table**
(clink 49): a name the checker resolves to `τ` is a name the *machine* resolves to a value in
`τ`.

The first cut of this component quantified over the entries (`∀ p τ, envGet? cs p = some τ →
… constLookup m.heap (stripColons p) …`), and that was wrong in a way `Judge.constEnv`'s rung
made visible. `Ctx.consts` is keyed by **absolute path** — `"::LIMIT"` at toplevel, but
`"::A::X"` for a constant declared in the body of `class A` — and no heap has a toplevel
constant literally spelled `A::X`. So the entry-wise form was unsatisfiable at any context
with a nested constant (vacuity, not falsity), and at the same time it said nothing about the
name `constGet?` actually consults when the rule fires.

Quantifying over `constGet?` fixes both, and it is the shape `Denote/Sem/notes.md`'s sixth
stall point recommends for `DefsOk`/`ClassesOk` too ("the checker only ever consults the first
match … the fix is to state the components over the lookup function"). It also makes the
component depend on the whole `Ctx` rather than on one field — `constGet?` consults
`κ.frame`'s class before the toplevel path — which is why it takes `κ`. -/
def ConstsOk (κ : Ctx) (m : Machine) : Prop :=
  ∀ n τ, constGet? κ n = some τ →
    ∃ v, constResolveAt m n = some v ∧ denM τ m v

/-- **Constants under a path**, which is `ConstsOk` for the `A::B` form.

`ConstsOk` is about *lexical* resolution — `constGet? κ n` against `constResolveAt m n`, which
is what the `Judge.const` family consumes. `Judge.constPath` asks a different question: the
type recorded at the **keyed** entry `constKeyIn owner n` (i.e. `"::owner::n"`) against what
the interpreter finds by looking `n` up *inside* the class named `owner`. Nothing related the
two, and that is what stopped the rung (clink 54).

Stated as an implication with `classNamed?` on the left, so a context entry naming a class the
machine does not have is no claim at all — the shape `CoreOk.coreNamed` took (clink 50), for
the same reason. -/
def ConstPathsOk (κ : Ctx) (m : Machine) : Prop :=
  ∀ owner n τ k, envGet? κ.consts (constKeyIn owner n) = some τ →
    classNamed? m.heap owner = some k →
      ∀ v, constLookupFrom m.heap k n = some v → denM τ m v

/-- `ConstPathsOk` reads the heap only through `classPayload?` and the ancestor walk, both of
which `Ext` pins, plus a `denM` which is `denM_ext`. -/
theorem ConstPathsOk.ext {κ : Ctx} {m m₂ : Machine} (he : Ext m m₂) (h : ConstPathsOk κ m) :
    ConstPathsOk κ m₂ := by
  intro owner n τ k hk hcn v hv
  rw [he.classNamed?_eq] at hcn
  simp only [constLookupFrom, he.payload, he.ancestors] at hv
  exact denM_ext he (h owner n τ k hk hcn v hv)

/-- …and a rebinding writes `locals` only, so the heap side is untouched. -/
theorem ConstPathsOk.setLocal {κ : Ctx} {m : Machine} {x : String} {w : Value} {τ' : Ty}
    (hw : denM τ' m w) (hcs : ∀ owner n σ, envGet? κ.consts (constKeyIn owner n) = some σ →
      capStale x τ' σ = false)
    (h : ConstPathsOk κ m) : ConstPathsOk κ (m.setLocal x w) := by
  intro owner n τ k hk hcn v hv
  rw [setLocal_heap] at hcn hv
  exact denM_setLocal hw (hcs owner n τ hk) (h owner n τ k hk hcn v hv)

/-- **A nested class is reachable through its container's constant table.**

`ClassesOk` says a class in the table has a name the machine resolves — through `classNamed?`,
i.e. the *toplevel* lookup at the full path `"A::B"`. `Judge.constPathCls` needs the other
direction of the same fact: that looking `B` up **inside** `A` finds that same class. Nothing
related the two, and this is the clause that does (clink 54).

Stated with both lookups on the left, so it is a claim about agreement and not an existence
claim — a machine that has neither is not being described. -/
def NestedClassesOk (C : CTable) (m : Machine) : Prop :=
  ∀ owner n c, clsGet? C (owner ++ "::" ++ n) = some c →
    ∀ k v, classNamed? m.heap owner = some k → constLookupFrom m.heap k n = some v →
      isClassRefNamed m.heap v (owner ++ "::" ++ n) = true

theorem NestedClassesOk.ext {C : CTable} {m m₂ : Machine} (he : Ext m m₂)
    (h : NestedClassesOk C m) : NestedClassesOk C m₂ := by
  intro owner n c hc k v hcn hlk
  rw [he.classNamed?_eq] at hcn
  simp only [constLookupFrom, he.payload, he.ancestors] at hlk
  rw [he.isClassRefNamed_eq]
  exact h owner n c hc k v hcn hlk

theorem NestedClassesOk.setLocal {C : CTable} {m : Machine} (x : String) (w : Value)
    (h : NestedClassesOk C m) : NestedClassesOk C (m.setLocal x w) := by
  intro owner n c hc k v hcn hlk
  rw [setLocal_heap] at hcn hlk ⊢
  exact h owner n c hc k v hcn hlk

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

/-- **There is a current frame.** `Machine.currentFrame` and `Machine.getLocal` both start at
`m.stack.headD 0`, and both are *total*: out of range they answer the default frame and `nil`.
So a machine with an empty stack, or a stack head past the end of the frame array, is not an
error — it is a machine where every local reads `nil` and `setLocal` is a no-op, and `Γ` would
be describing bindings that do not exist.

Forced by `Judge.vasgnAlias` (clink 47): `getLocal_setLocal_self` — "the value `x` names after
`x = e` is the value assigned" — is *false* at such a machine, and it is what the rule's
outgoing environment claims. One inequality, checked at the booted machine by
`Denote/Sanity.lean`'s guard along with the other two. -/
abbrev FrameInRange (m : Machine) : Prop := m.stack ≠ [] ∧ m.stack.headD 0 < m.frames.size

/-- The current frame, read the way a *closure* reads it. `Machine.currentFrame` matches on
the stack and answers `default` at `[]`, while everything that captures a frame captures
`m.stack.headD 0` — an id, which at `[]` is `0`, a frame that may well exist. So the two
readings agree exactly when the stack is non-empty, which is `FrameInRange`'s first conjunct
and the reason it has one (added in clink 52 for `Judge.lambdaLit`; the docstring above always
described "there is a current frame", and the inequality alone did not say it). -/
theorem currentFrame_headD {m : Machine} (h : m.stack ≠ []) :
    m.currentFrame = m.frames.getD (m.stack.headD 0) default := by
  cases hs : m.stack with
  | nil => exact absurd hs h
  | cons fid rest => simp [Machine.currentFrame, hs]

/-- The class names the three `.const` rules can conclude about without the program having
declared anything: `BuiltinCls`'s nine (`Judge.constBuiltin`) and `ExcCls`'s thirteen
(`Judge.constExc`). A **list** rather than a predicate, so `CoreOk`'s clause about them is one
decidable `Bool` at the booted heap (`Denote/Sanity.lean`) instead of a quantifier over
`String`. -/
def coreClsNames : List String :=
  ["Integer", "Float", "String", "Symbol", "NilClass", "TrueClass", "FalseClass", "Array",
   "Hash",
   "StandardError", "RuntimeError", "ArgumentError", "TypeError", "NameError",
   "NoMethodError", "ZeroDivisionError", "IndexError", "KeyError", "RangeError",
   "IOError", "FrozenError", "NotImplementedError"]

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
  /-- The name `Regexp` resolves to the boot `Regexp` class (`Judge.regexpLit`, clink 48 —
      the second allocating literal, and the first row this structure grew as its docstring
      predicted it would). -/
  regexpNamed : classNamed? h "Regexp" = some Boot.regexpId
  /-- `Regexp` is a `Regexp` … -/
  regexpSelf : (ancestors h Boot.regexpId).contains Boot.regexpId = true
  /-- … and a `BasicObject`. -/
  regexpBasic : (ancestors h Boot.regexpId).contains Boot.basicObjectId = true
  /-- `Proc` is a `BasicObject` (`Judge.lambdaLit`, clink 52 — the third allocating rule, and
      the third row this structure's docstring predicted). No `procNamed`/`procSelf` twin: the
      rule concludes `.clos`, not `.cls "Proc"`, so the only thing spent is `ext_push`'s
      descendant clause. -/
  procBasic : (ancestors h Boot.procId).contains Boot.basicObjectId = true
  /-- **A core class name, if it is bound at all, is bound to a class** (clink 49).

      The two `.const` rules that need no declaration (`constBuiltin`, `constExc`) conclude
      `.clsOf n` for a name out of a fixed list, and `isClassRefNamed` answers `false` unless
      the name resolves to something carrying a class payload. Stated as an implication rather
      than as "the class exists", because one of the twenty-two does **not** exist in the
      booted heap: the model has no `IOError`. At an unbound name `evalExpr` gates
      (`.unsupported`) or raises, so no value is produced and `Judge.constExc`'s obligation at
      `"IOError"` is discharged by having no case rather than by a fact about the heap. -/
  coreNamed : ∀ n ∈ coreClsNames, ∀ v, constLookup h n = some v →
    ∃ o, v = .ref o ∧ (h.classPayload? o).isSome = true

theorem CoreOk.ext {h h' : Heap} {m m₂ : Machine} (hm : m.heap = h) (hm₂ : m₂.heap = h')
    (he : Ext m m₂) (hc : CoreOk h) : CoreOk h' where
  basicSelf := by subst hm; subst hm₂; rw [he.ancestors]; exact hc.basicSelf
  stringNamed := by subst hm; subst hm₂; rw [he.classNamed?_eq]; exact hc.stringNamed
  stringSelf := by subst hm; subst hm₂; rw [he.ancestors]; exact hc.stringSelf
  stringBasic := by subst hm; subst hm₂; rw [he.ancestors]; exact hc.stringBasic
  regexpNamed := by subst hm; subst hm₂; rw [he.classNamed?_eq]; exact hc.regexpNamed
  regexpSelf := by subst hm; subst hm₂; rw [he.ancestors]; exact hc.regexpSelf
  regexpBasic := by subst hm; subst hm₂; rw [he.ancestors]; exact hc.regexpBasic
  procBasic := by subst hm; subst hm₂; rw [he.ancestors]; exact hc.procBasic
  coreNamed := by
    subst hm; subst hm₂; intro n hn v hv
    exact hc.coreNamed n hn v (by rw [← he.constLookup_eq]; exact hv) |>.imp
      (fun o ho => ⟨ho.1, by rw [he.payload]; exact ho.2⟩)

/-! ## "And nothing more" — the exactness component

Every component above is a **lower** bound: each thing `κ` records is really there. None says
there is nothing else, and three rungs stalled on that (`Denote/Sem/notes.md`, sixth and ninth
stall points). `MethodsExact` is the upper bound. The frame rule it belongs to, and what it
does and does not buy, are in [`Denote/Sem/Frame.lean`](Frame.lean); the definitions live here
because `StateOk` has a field for one of them. -/

/-- Every method name `κ` records anywhere: a top-level `def`, or an instance or singleton
method of a declared class or module. `Judge`'s tables are the only places a method name can
enter the checker's world, so this is the complete list.

**Name-global on purpose** — it forgets which class a name was declared on. Sharpening it to a
per-owner claim is possible and nothing asks: the rules that consume exactness are asking "did
the program define this name *at all*?", which is what a negative premise like
`defDeclared? κ.defs m = none` is trying to say. -/
def declaresName (κ : Ctx) (n : String) : Bool :=
  κ.defs.any (·.name == n) ||
  κ.classes.any (fun c => c.methods.any (·.name == n) || c.smethods.any (·.name == n))

/-- **"And nothing more", for methods.** Every method installed anywhere in the heap is the
model's own — an axiomatized builtin (`MethodDef.builtin`) or Ruby's core library written in
RubyCore (`MethodDef.fromPrelude`) — or a name `κ` records.

The model's own two discriminators do the work of saying which methods are not the user's
program, which is why this needs no new machinery in `RubyCore`.

Stated over the heap rather than over `lookup`, and that is the useful direction: `lookup`,
`methodOn` and `lookupAbove` all find their answer in some class payload's `methods`, so the
heap-global form implies the statement at every one of them (`MethodsExact.lookup`,
`Denote/Sem/Frame.lean`) while being a single decidable `Bool` at a concrete heap.

Measured before it was stated: at the real prelude-booted heap the number of installed methods
that are neither builtin nor prelude is **zero** (`Denote/Sanity.lean`'s `methodsExactB`), so
this is a fact about the machine the ladder starts from rather than a hopeful invariant, and
`declaresName` is exactly the room a program grows into it. -/
def MethodsExact (κ : Ctx) (m : Machine) : Prop :=
  ∀ k cp, m.heap.classPayload? k = some cp →
    ∀ n md, (n, md) ∈ cp.methods →
      md.fromPrelude = true ∨ md.builtin.isSome = true ∨ declaresName κ n = true

/-- **`self` is a real object.** Every reference `StateOk` describes has to be one the heap
actually holds, and this is the one place it was not said: `Machine.currentFrame.self`.

Forced by `NameFreeOk`'s transport across an allocation. `classOf` reads `(h.get o).eigen` and
`.klass`, and `Heap.get` is *total* — past the end it answers `default`, whose class is
`BasicObject` (`Denote/Sem/notes.md` §The fourth stall point, "the one genuinely surprising
cost"). So at a machine whose `self` is a **dangling** reference, an allocation *changes what
`self` is an instance of*, and a claim about the methods reachable from `self` does not
survive the push. Requiring the reference to be live is the honest fix and it is what
`Ext.get` then pins.

Stated as an implication so an **immediate** `self` is admitted rather than excluded:
`classOf` answers a boot id for `.int`/`.sym`/`.nil`/booleans without reading the heap at all,
so those are stable across allocation for free — and `1.instance_eval { … }` is a machine the
model can be in, even though no `Judge` rule types it. -/
def SelfLive (m : Machine) : Prop :=
  ∀ o, m.currentFrame.self = .ref o → o < m.heap.objs.size

/-- `self`'s dispatch class is unmoved by an allocation, given that `self` is real. -/
theorem classOf_self_ext {m m₂ : Machine} (he : Ext m m₂) (hl : SelfLive m) :
    classOf m₂.heap m₂.currentFrame.self = classOf m.heap m.currentFrame.self := by
  rw [he.currentFrame_eq]
  cases hs : m.currentFrame.self with
  | ref o => simp only [classOf, he.get o (hl o hs)]
  | bool b => cases b <;> rfl
  | _ => rfl

/-- The names whose *absence* a rule reasons from: `BareNameError`'s one row
(`Judge.bareName`) and `nameFree`'s two (`Judge.lambdaLit`). A list, so the component below
is one decidable `Bool` at a concrete machine — `CoreOk`'s trade, for the same reason.

Why a list at all rather than "every name": the honest general claim is `MethodsExact`, and it
allows a **prelude** method. `Judge.bareName` needs `x` to resolve to *nothing*, which is a
strictly stronger thing than "not the user's", and it is only true name by name. Measured at
the booted machine: the toplevel ancestor chain carries ~40 prelude-written methods (`tap`,
`format`, `Integer`, `!=`, and the `__`-prefixed helpers) and **none of these three**. -/
def shadowableNames : List String := ["lambda", "proc", "x"]

/-- **"And nothing more", sharpened on `shadowableNames` and localised to the chain.** A
method of one of those names that dispatch can *reach from the current `self`* is an
axiomatized builtin, a tombstone, or a name `κ` records.

Three things about the shape, each of which could have gone another way and did not:

* **Chain-local, not heap-global.** The heap-global version is **false**: the prelude really
  does define a method named `proc` — `T.proc`, the sorbet shim's type constructor, installed
  as a *singleton* method on the `T` module, i.e. on `#<Class:T>`. That is off the toplevel
  chain (`extend`/`include` move a module's *instance* methods, never its singleton ones), so
  the model's own shadowing test — which walks `methodOn (classOf recv)` — is right about it,
  and this component has to be stated at the same walk to say so.
* **`builtin.isSome ∨ undefined`, not `fromPrelude`.** This is the `MethodsExact` disjunction
  with the prelude escape removed, which is exactly what makes it strong enough for a rule
  claiming *absence*; and it is the same `md.builtin.isNone && !md.undefined` test
  `finishSend` uses to decide whether a user definition shadows `lambda`/`proc`.
* **The `declaresName` escape stays.** Without it a program that really does `def lambda`
  would make `StateOk` *unsatisfiable* rather than making the rule inapplicable — vacuity
  instead of falsity, which is the failure mode `Denote/Sanity.lean` exists to police. With
  it, such a program is perfectly conformant and it is `nameFree`'s premise that fails. -/
def NameFreeOk (κ : Ctx) (m : Machine) : Prop :=
  ∀ n ∈ shadowableNames, ∀ o md,
    Interp.methodOn m.heap (classOf m.heap m.currentFrame.self) n = some (o, md) →
      md.builtin.isSome = true ∨ md.undefined = true ∨ declaresName κ n = true

/-- **What a bare name at top level must not find** (`Judge.bareName`).

`NameFreeOk` above is not enough for that rule, and the reason is the shape of its
disjunction rather than its name list: it admits `md.builtin.isSome`, and a *builtin* named
`x` would send `invokeDispatch` into `Builtins.run` — a call that returns a value and can move
the heap, so the rule's `.any` conclusion and its unchanged outgoing `Γ`/`I` would both be
claims about a real run. `Judge.bareName` needs `x` to resolve to **nothing at all**, which is
the `lookup = none` branch of `invokeDispatch` and nothing weaker.

**Stated at exactly the rule's own premises**, and that is the decision worth recording. The
escape is `defDeclared? κ.defs n = none` and `κ.selfTy = none` — the rule's second and third
premises verbatim — rather than `NameFreeOk`'s wider `declaresName κ n = true`. Two
consequences, in both directions:

* It is what makes the component *usable*: `declaresName` also reads `κ.classes`, and
  `Judge.bareName` has no premise about those, so a component with the wider escape would
  hand the rung nothing at a context where some class happens to declare an `x`.
* It is a real restriction on conformant machines: a machine at top level whose `self` can
  dispatch an `x` that `κ.defs` does not record is **not** conformant. That machine is
  precisely the one at which the rule is wrong (`found-issues.md` §F4 is the same shape one
  name over), so declaring it non-conformant is the honest statement rather than a dodge —
  but it is a conformance gap, in the ninth stall point's sense, and `Judge.bareName` says
  nothing there.

Quantified over the `BareNameError` **inductive** rather than over a copied list of names, so
a row added to that table is covered here the same day — and `Denote/Sanity.lean`'s `Bool` is
then what has to be re-measured. -/
def BareNameFree (κ : Ctx) (m : Machine) : Prop :=
  ∀ n, Ratchet.BareNameError n → defDeclared? κ.defs n = none → κ.selfTy = none →
    lookup m.heap m.currentFrame.self n = none

/-- **No *user* `method_missing` is reachable from `self`** (`Judge.bareName`).

The second half of the same rule, and it is `found-issues.md` §F4: a bare name that resolves
nowhere reaches `dispatchMiss`, whose last question before raising `NameError` is whether the
receiver has a `method_missing`. If it does, the call **returns** and its body runs — so the
rule's `.any` and its unchanged `I` are both false, which is the wrong answer that entry
records.

Two things about the shape:

* **No `undefined` escape**, unlike `NameFreeOk`. `dispatchMiss` tests `mm.builtin.isNone` and
  nothing else, so an `undef method_missing` tombstone with no builtin behind it would be
  *entered* by this interpreter. Stating the component at the interpreter's own test rather
  than at the sharper test it could have made is the point: a component is a claim about what
  the machine does, and inventing a check the machine does not perform would make the rung a
  proof about a different interpreter.
* **The escape is the rule's own premise**, `nameFree κ "method_missing" = true` — the premise
  clink 52 added — for the same reason `BareNameFree`'s is. -/
def MissFree (κ : Ctx) (m : Machine) : Prop :=
  nameFree κ "method_missing" = true → κ.selfTy = none →
    ∀ o md, Interp.methodOn m.heap (classOf m.heap m.currentFrame.self) "method_missing"
      = some (o, md) → md.builtin.isSome = true

/-! ## The query builtins

`Judge.isAQuery`/`caseEqQuery`/`classOf`/`clsToS` all have the same shape: a *send* whose
answer is a boot builtin's, and whose conclusion type does not depend on the builtin's
signature — only on the fact that a boolean (or a class, or a string) comes out. What they need
from the machine is the **dispatch precondition** `invokeDispatch` reads, and that is what this
component states.

Both halves are needed and both are true at the booted machine (computed — see
`Denote/Sanity.lean`'s `queryOkB`):

* whatever the machine resolves the name to **is** the boot builtin, public, not a tombstone,
  not prelude-defined, and not shadowed by an unmodeled CRuby method between the receiver and
  the owner — the five things `invokeDispatch` tests before it runs a builtin;
* and where the machine resolves the name to *nothing*, it has no non-builtin
  `method_missing` to fall into. That second half is not redundant: the boot heap really does
  have three prelude-defined `method_missing`s (measured), and `dispatchMiss` **enters** one
  when there is no builtin behind it — so without this clause a miss could *return* a value of
  any type at all. What makes it satisfiable is that those three classes all resolve `is_a?`
  through `Object`, so they never reach the miss path.

Quantified over **class ids** rather than receivers, for `MissFree`'s reason: `classOf` of a
dangling reference changes under an allocation, so a claim about receivers is not `Ext`-stable
while a claim about classes is.

The name table grows one entry per rung, exactly as `CoreOk`'s rows do. -/
def queryBuiltins : List (String × String) :=
  [("is_a?", "Object#is_a?"), ("class", "Object#class")]

def QueryOk (κ : Ctx) (m : Machine) : Prop :=
  ∀ mname bid, (mname, bid) ∈ queryBuiltins → nameFree κ mname = true → ∀ k,
    (∀ owner md, Interp.methodOn m.heap k mname = some (owner, md) →
        md.builtin = some bid ∧ md.undefined = false ∧ md.visibility = .pub ∧
        md.fromPrelude = false ∧
        Interp.crubyShadow m.heap
          ((ancestors m.heap k).takeWhile (fun x => x != owner)) mname = none) ∧
    (Interp.methodOn m.heap k mname = none →
      ∀ o md, Interp.methodOn m.heap k "method_missing" = some (o, md) →
        md.builtin.isSome = true)

/-- `QueryOk` for the names dispatched at a **class object** receiver — `Module#===`, which
`case x when C` desugars to. Same five facts and the same miss clause; the difference is where
the walk starts. `classOf` of a class object is its *eigenclass*, so the claim is indexed by
the class object rather than by a class id, and it is conditioned on the object actually being
a class (which also pins the reference live, so `Ext` can transport it).

Measured at the booted machine before each row was written down: all 87 class objects resolve
`===` to `Module#===` and `to_s` to `Module#to_s`, public and unshadowed in both cases. (Over
*arbitrary* receivers neither name is clean — `===` fails at 43 classes and `to_s` at 63 — which
is why the component is indexed by the receiver rather than by its class, and why `QueryOk`'s
own list cannot simply absorb these two rows.) -/
def clsQueryBuiltins : List (String × String) :=
  [("===", "Module#==="), ("to_s", "Module#to_s")]

def ClsQueryOk (κ : Ctx) (m : Machine) : Prop :=
  ∀ mname bid, (mname, bid) ∈ clsQueryBuiltins → nameFree κ mname = true → ∀ o,
    (m.heap.classPayload? o).isSome = true →
    (∀ owner md, Interp.methodOn m.heap (classOf m.heap (.ref o)) mname = some (owner, md) →
        md.builtin = some bid ∧ md.undefined = false ∧ md.visibility = .pub ∧
        md.fromPrelude = false ∧
        Interp.crubyShadow m.heap
          ((ancestors m.heap (classOf m.heap (.ref o))).takeWhile (fun x => x != owner))
          mname = none) ∧
    (Interp.methodOn m.heap (classOf m.heap (.ref o)) mname = none →
      ∀ o₂ md, Interp.methodOn m.heap (classOf m.heap (.ref o)) "method_missing"
        = some (o₂, md) → md.builtin.isSome = true)

theorem QueryOk.ext {κ : Ctx} {m m₂ : Machine} (he : Ext m m₂) (h : QueryOk κ m) :
    QueryOk κ m₂ := by
  intro mname bid hmem hfree k
  have hm : ∀ n, Interp.methodOn m₂.heap k n = Interp.methodOn m.heap k n := by
    intro n; simp only [Interp.methodOn, he.payload, he.ancestors]
  obtain ⟨h1, h2⟩ := h mname bid hmem hfree k
  refine ⟨?_, ?_⟩
  · intro owner md hfound
    rw [hm] at hfound
    obtain ⟨hb, hu, hv, hp, hsh⟩ := h1 owner md hfound
    refine ⟨hb, hu, hv, hp, ?_⟩
    simp only [Interp.crubyShadow, className, he.payload, he.ancestors] at hsh ⊢
    exact hsh
  · intro hnone o md hfound
    rw [hm] at hnone hfound
    exact h2 hnone o md hfound

/-- A class payload pins its reference **live**: past the end of the heap `Heap.get` answers
`default`, whose payload is `.none`. -/
theorem lt_size_of_classPayload {h : Heap} {o : ObjId}
    (hp : (h.classPayload? o).isSome = true) : o < h.objs.size := by
  by_cases hk : o < h.objs.size
  · exact hk
  · exfalso
    simp only [Heap.classPayload?, Heap.get, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (by simpa using hk), Option.getD_none] at hp
    exact absurd hp (by decide)

theorem ClsQueryOk.ext {κ : Ctx} {m m₂ : Machine} (he : Ext m m₂) (h : ClsQueryOk κ m) :
    ClsQueryOk κ m₂ := by
  intro mname bid hmem hfree o hp
  have hlt : o < m.heap.objs.size := by
    rw [he.payload] at hp; exact lt_size_of_classPayload hp
  have hco : classOf m₂.heap (.ref o) = classOf m.heap (.ref o) := by
    simp only [classOf, he.get o hlt]
  have hm : ∀ n, Interp.methodOn m₂.heap (classOf m₂.heap (.ref o)) n
      = Interp.methodOn m.heap (classOf m.heap (.ref o)) n := by
    intro n; simp only [hco, Interp.methodOn, he.payload, he.ancestors]
  rw [he.payload] at hp
  obtain ⟨h1, h2⟩ := h mname bid hmem hfree o hp
  refine ⟨?_, ?_⟩
  · intro owner md hfound
    rw [hm] at hfound
    obtain ⟨hb, hu, hv, hpre, hsh⟩ := h1 owner md hfound
    refine ⟨hb, hu, hv, hpre, ?_⟩
    simp only [hco, Interp.crubyShadow, className, he.payload, he.ancestors] at hsh ⊢
    exact hsh
  · intro hnone o₂ md hfound
    rw [hm] at hnone hfound
    exact h2 hnone o₂ md hfound

theorem ClsQueryOk.setLocal {κ : Ctx} {m : Machine} (x : String) (w : Value)
    (h : ClsQueryOk κ m) : ClsQueryOk κ (m.setLocal x w) := by
  intro mname bid hmem hfree o hp
  simp only [setLocal_heap] at hp ⊢
  exact h mname bid hmem hfree o hp

theorem QueryOk.setLocal {κ : Ctx} {m : Machine} (x : String) (w : Value) (h : QueryOk κ m) :
    QueryOk κ (m.setLocal x w) := by
  intro mname bid hmem hfree k
  simp only [setLocal_heap]
  exact h mname bid hmem hfree k

/-- **Conformance**: one conjunct per `Ctx` field, plus the two threaded pieces `Γ` and `I`,
plus the three machine facts above.

Nine `Ctx` fields, nine components, and the two that are `True` say so with a docstring rather
than by omission — a `StateOk` that quietly skipped a field would be a place for an unsound
rule to hide. -/
structure StateOk (κ : Ctx) (Γ : Env) (I : Ty) (m : Machine) : Prop where
  sat : HeapSaturated m
  core : CoreOk m.heap
  frameInRange : FrameInRange m
  env : EnvOk Γ m
  selfSpine : SelfSpineOk I m
  classes : ClassesOk κ.classes m
  defs : DefsOk κ.defs m
  asms : AsmsOk κ.asms m
  frame : FrameOk κ.frame m
  closures : ClosuresOk κ.closures m
  blockTy : BlockTyOk κ.blockTy m
  selfTy : SelfTyOk κ.selfTy m
  consts : ConstsOk κ m
  constPaths : ConstPathsOk κ m
  nested : NestedClassesOk κ.classes m
  privConsts : PrivConstsOk κ.privConsts m
  constScope : ConstScopeOk m
  exact : MethodsExact κ m
  nameFree : NameFreeOk κ m
  bareFree : BareNameFree κ m
  missFree : MissFree κ m
  query : QueryOk κ m
  clsQuery : ClsQueryOk κ m
  selfLive : SelfLive m

/-! ## Conformance survives an allocation

The theorem every allocating rung needs, and the one that pays for `Denote/Ext.lean` and
`Denote/Grow.lean`. Component by component, and the shape of each proof is the finding:

* Nine components are **rewrites** — they read the heap through `classPayload?`,
  `constLookup` or an in-range `Heap.get`, and read the frames through `currentFrame`, all of
  which `Ext` pins outright.
* `env`, `selfSpine`, `blockTy`, `selfTy` and `consts` additionally transport a `denM`, which
  is `denM_ext`.
* `frame` is the one that is only *monotone* (`isAName`), and `asms` is the one that is free
  by construction (`Ext.later` then `Later.trans`) rather than proved — see its own docstring.

Nothing here is specific to a string literal: an allocating rung supplies the `Ext` and this
does the rest. -/
/-- The ancestor walk `lookup` performs reads the heap only through `classPayload?`, so two
heaps that agree there agree on it. One induction, and the reason it is needed rather than
being a `simp` step is that `lookup.go` carries the heap as a captured argument. -/
theorem lookup_go_payload {h h' : Heap} (hp : ∀ k, h'.classPayload? k = h.classPayload? k)
    (n : String) : ∀ ks, lookup.go h' n ks = lookup.go h n ks
  | [] => rfl
  | k :: rest => by
    rw [lookup.go, lookup.go, hp k]
    cases hc : h.classPayload? k with
    | none => simp only [hc]; exact lookup_go_payload hp n rest
    | some cp =>
      simp only [hc]
      cases cp.methods.find? (·.1 == n) with
      | none => exact lookup_go_payload hp n rest
      | some p => rfl

/-- `lookup` **is** `methodOn` at the receiver's dispatch class: the same ancestor walk,
written once as an explicit `go` (`RubyCore/Heap.lean`) and once as a `firstM`
(`Interp/Dispatch.lean`). Needed because the two components below are stated at the walk the
interpreter performs and the interpreter performs both. -/
theorem lookup_eq_methodOn (h : Heap) (v : Value) (n : String) :
    lookup h v n = Interp.methodOn h (classOf h v) n := by
  simp only [lookup, Interp.methodOn]
  induction (RubyCore.ancestors h (classOf h v)) with
  | nil => rfl
  | cons k rest ih =>
    rw [lookup.go, List.firstM]
    cases hp : h.classPayload? k with
    | none => simp [ih]
    | some cp =>
      cases hf : cp.methods.find? (·.1 == n) with
      | none => simp [hf, ih]
      | some p => simp [hf]

theorem StateOk_ext {κ : Ctx} {Γ : Env} {I : Ty} {m m₂ : Machine} (h : StateOk κ Γ I m)
    (he : Ext m m₂) : StateOk κ Γ I m₂ where
  sat := Proof.Saturated_grow he.shapeAgree he.size h.sat
  core := CoreOk.ext rfl rfl he h.core
  frameInRange := by
    have := h.frameInRange
    unfold FrameInRange at this ⊢
    rw [he.stack, he.frames]; exact this
  env := by
    refine ⟨?_, ?_⟩
    · intro x τ hx
      obtain ⟨hd, hid⟩ := h.env.1 x τ hx
      refine ⟨?_, ?_⟩
      · rw [he.getLocal_eq]; exact denM_ext he hd
      · intro y ρ hτ; rw [he.getLocal_eq, he.getLocal_eq]; exact hid y ρ hτ
    · -- completeness travels with the locals, which `Ext` does not touch
      intro x hx
      rw [he.getLocal_eq]
      exact h.env.2 x hx
  selfSpine := by
    have := h.selfSpine
    unfold SelfSpineOk at this ⊢
    rw [he.currentFrame_eq, funext (he.ivarOf_eq m.currentFrame.self)]
    exact ⟨denSpine_ext he this.1, this.2⟩
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
    exact h.asms a ha m₃ (he.later.trans he₃) args hargs v m' hs
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
  constPaths := ConstPathsOk.ext he h.constPaths
  nested := NestedClassesOk.ext he h.nested
  consts := by
    intro n τ hn
    obtain ⟨v, hv1, hv2⟩ := h.consts n τ hn
    refine ⟨v, ?_, denM_ext he hv2⟩
    rw [show constResolveAt m₂ n = constResolveAt m n by
      simp only [constResolveAt, constOwn, constLookupFrom, he.payload, he.ancestors,
        he.currentFrame_eq]]
    exact hv1
  privConsts := trivial
  constScope := ConstScopeOk.ext he h.constScope
  exact := by
    intro k cp hk
    exact h.exact k cp (by rw [he.payload] at hk; exact hk)
  nameFree := by
    intro n hn o md hm
    refine h.nameFree n hn o md ?_
    rw [← hm]
    simp only [Interp.methodOn, classOf_self_ext he h.selfLive, he.payload, he.ancestors]
  bareFree := by
    intro n hn hdef hself
    rw [show lookup m₂.heap m₂.currentFrame.self n
          = lookup m.heap m.currentFrame.self n by
      simp only [lookup, classOf_self_ext he h.selfLive, he.ancestors]
      exact lookup_go_payload he.payload n _]
    exact h.bareFree n hn hdef hself
  query := QueryOk.ext he h.query
  clsQuery := ClsQueryOk.ext he h.clsQuery
  missFree := by
    intro hfree hself o md hm
    refine h.missFree hfree hself o md ?_
    rw [← hm]
    simp only [Interp.methodOn, classOf_self_ext he h.selfLive, he.payload, he.ancestors]
  selfLive := by
    intro o ho
    rw [he.currentFrame_eq] at ho
    exact Nat.lt_of_lt_of_le (h.selfLive o ho) he.size

/-! ### Reading the environment the rule builds

Four one-line inductions, so that `StateOk_setLocal` can talk about
`envSet (killClosOver (killAliasesTo Γ x) x τ) x ρ` one binding at a time. -/

theorem envGet?_cons_self (y : String) (σ : Ty) (Γ : Env) :
    envGet? ((y, σ) :: Γ) y = some σ := by simp [envGet?, List.find?]

theorem envGet?_cons_ne {y x : String} (σ : Ty) (Γ : Env) (h : ¬ (y = x)) :
    envGet? ((y, σ) :: Γ) x = envGet? Γ x := by
  have hb : (y == x) = false := by simpa using h
  simp [envGet?, List.find?, hb]

/-- The same, with the pair left whole — the form `rw` can use when the entry's *type* is a
`match` the rewriter would otherwise have to guess. -/
theorem envGet?_cons_ne' {p : String × Ty} {x : String} (Γ : Env) (h : ¬ (p.1 = x)) :
    envGet? (p :: Γ) x = envGet? Γ x := by
  have hb : (p.1 == x) = false := by simpa using h
  simp [envGet?, List.find?, hb]

theorem envGet?_envSet_self : ∀ (Γ : Env) (x : String) (ρ : Ty),
    envGet? (envSet Γ x ρ) x = some ρ
  | [], x, ρ => by simp [envSet, envGet?_cons_self]
  | (y, σ) :: Γ, x, ρ => by
    by_cases h : y = x
    · subst h; simp [envSet, envGet?_cons_self]
    · have hb : (y == x) = false := by simpa using h
      rw [envSet, if_neg (by simp [hb]), envGet?_cons_ne σ _ h]
      exact envGet?_envSet_self Γ x ρ

theorem envGet?_envSet_ne : ∀ (Γ : Env) (x y : String) (ρ : Ty), ¬ (y = x) →
    envGet? (envSet Γ x ρ) y = envGet? Γ y
  | [], x, y, ρ, hy => by
    rw [envSet, envGet?_cons_ne ρ _ (fun h => hy h.symm)]
  | (z, σ) :: Γ, x, y, ρ, hy => by
    by_cases h : z = x
    · subst h
      rw [envSet, if_pos (by simp)]
      by_cases h2 : z = y
      · exact absurd h2.symm hy
      · rw [envGet?_cons_ne ρ _ h2, envGet?_cons_ne σ _ h2]
    · have hb : (z == x) = false := by simpa using h
      rw [envSet, if_neg (by simp [hb])]
      by_cases h2 : z = y
      · subst h2; rw [envGet?_cons_self, envGet?_cons_self]
      · rw [envGet?_cons_ne σ _ h2, envGet?_cons_ne σ _ h2]
        exact envGet?_envSet_ne Γ x y ρ hy

theorem envGet?_killClosOver : ∀ (Γ : Env) (x : String) (τ : Ty) (y : String),
    envGet? (killClosOver Γ x τ) y
      = (envGet? Γ y).map (fun σ => if capStale x τ σ then .any else σ)
  | [], x, τ, y => rfl
  | (z, σ) :: Γ, x, τ, y => by
    simp only [killClosOver]
    by_cases h : z = y
    · subst h; rw [envGet?_cons_self, envGet?_cons_self]; rfl
    · rw [envGet?_cons_ne' (p := (z, _)) _ h, envGet?_cons_ne' (p := (z, σ)) _ h]
      exact envGet?_killClosOver Γ x τ y

theorem envGet?_killAliasesTo : ∀ (Γ : Env) (x : String) (y : String),
    envGet? (killAliasesTo Γ x) y = (envGet? Γ y).map (killAliasTy x)
  | [], x, y => rfl
  | (z, σ) :: Γ, x, y => by
    simp only [killAliasesTo]
    by_cases h : z = y
    · subst h; rw [envGet?_cons_self, envGet?_cons_self]; rfl
    · rw [envGet?_cons_ne' (p := (z, _)) _ h, envGet?_cons_ne' (p := (z, σ)) _ h]
      exact envGet?_killAliasesTo Γ x y

theorem envGet?_mem : ∀ {Γ : Env} {y : String} {σ : Ty}, envGet? Γ y = some σ →
    ∃ z, (z, σ) ∈ Γ
  | [], y, σ, h => absurd h (by simp [envGet?])
  | (z, ρ) :: Γ, y, σ, h => by
    by_cases hz : z = y
    · subst hz
      rw [envGet?_cons_self] at h
      exact ⟨z, by rw [show σ = ρ from (Option.some.inj h).symm]; exact List.mem_cons_self⟩
    · rw [envGet?_cons_ne _ _ hz] at h
      obtain ⟨q, hq⟩ := envGet?_mem h
      exact ⟨q, List.mem_cons_of_mem _ hq⟩

/-- `constGet?` is a `findSome?` over `envGet? κ.consts`, so an answer comes from *some*
entry — which is what `StateOk_setLocal`'s `capStaleCtx` side condition (a claim about every
entry) has to be applied at. -/
theorem findSome?_entry {α β : Type} : ∀ (l : List α) (f : α → Option β) {b : β},
    l.findSome? f = some b → ∃ a, f a = some b
  | [], _, _, h => by simp [List.findSome?] at h
  | a :: l, f, b, h => by
    simp only [List.findSome?] at h
    cases hf : f a with
    | some c => rw [hf] at h; exact ⟨a, by rw [hf]; exact h⟩
    | none => rw [hf] at h; exact findSome?_entry l f h

theorem constGet?_entry {κ : Ctx} {n : String} {τ : Ty} (h : constGet? κ n = some τ) :
    ∃ p, envGet? κ.consts p = some τ :=
  findSome?_entry _ _ h

/-! ### What `killAliasTy` leaves behind

Three facts, so the `env` component can reason about the entry `killAliasesTo` produced
without unfolding a `match` three times. -/

/-- Reading through an alias is reading the payload — so `stripAlias` and `killAliasTy`, which
both only remove `sameAs` wrappers, are invisible to `denM`. -/
theorem denM_stripAlias {σ : Ty} {m : Machine} {v : Value} :
    denM (stripAlias σ) m v ↔ denM σ m v := by
  cases σ <;> simp [stripAlias, denM]

theorem denM_deAlias : ∀ {σ : Ty} {m : Machine} {v : Value},
    denM (deAlias σ) m v ↔ denM σ m v
  | .sameAs n ρ, m, v => by rw [deAlias, denM]; exact denM_deAlias
  | .int, _, _ | .bool, _, _ | .nilT, _, _ | .sym, _, _ | .float, _, _ | .any, _, _
  | .never, _, _ | .cls _, _, _ | .clsOf _, _, _ | .nilable _, _, _ | .union _ _, _, _
  | .arrayOf _, _, _ | .hashOf _ _, _, _ | .inst _ _, _, _ | .ivar0, _, _
  | .ivarCons .., _, _ | .arrow0 _, _, _ | .arrowCons .., _, _
  | .clos .., _, _ => Iff.rfl

theorem denM_killAliasTy {x : String} : ∀ {σ : Ty} {m : Machine} {v : Value},
    denM (killAliasTy x σ) m v ↔ denM σ m v
  | .sameAs n ρ, m, v => by
    simp only [killAliasTy]
    split
    · rw [denM]; exact denM_deAlias
    · rfl
  | .int, _, _ | .bool, _, _ | .nilT, _, _ | .sym, _, _ | .float, _, _ | .any, _, _
  | .never, _, _ | .cls _, _, _ | .clsOf _, _, _ | .nilable _, _, _ | .union _ _, _, _
  | .arrayOf _, _, _ | .hashOf _ _, _, _ | .inst _ _, _, _ | .ivar0, _, _
  | .ivarCons .., _, _ | .arrow0 _, _, _ | .arrowCons .., _, _
  | .clos .., _, _ => Iff.rfl

theorem capStale_stripAlias {x : String} {τ σ : Ty} (h : capStale x τ σ = false) :
    capStale x τ (stripAlias σ) = false := by
  cases σ <;> simp_all [stripAlias, capStale]

/-- An alias survives `killAliasesTo x` only if it points somewhere other than `x` — which is
what the environment component needs to know that both sides of its `identEq` read back
unchanged. It is also why `killAliasTy` peels *repeatedly*: one layer is not enough. -/
theorem deAlias_ne_sameAs : ∀ (σ : Ty) (z : String) (ρ : Ty), deAlias σ = .sameAs z ρ → False := by
  intro σ
  induction σ with
  | sameAs n ρ' ih => intro z ρ h; rw [deAlias] at h; exact ih z ρ h
  | _ => intro z ρ h; simp [deAlias] at h

theorem sameAs_of_killAliasTy {x : String} : ∀ {σ : Ty} {z : String} {ρ : Ty},
    killAliasTy x σ = .sameAs z ρ → σ = .sameAs z ρ ∧ ¬ (z = x)
  | .sameAs n ρ', z, ρ, h => by
    simp only [killAliasTy] at h
    split at h
    · exact (deAlias_ne_sameAs _ _ _ h).elim
    · rename_i hn
      cases h
      exact ⟨rfl, by simpa using hn⟩
  | .int, _, _, h | .bool, _, _, h | .nilT, _, _, h | .sym, _, _, h | .float, _, _, h
  | .any, _, _, h | .never, _, _, h | .cls _, _, _, h | .clsOf _, _, _, h
  | .nilable _, _, _, h | .union _ _, _, _, h | .arrayOf _, _, _, h | .hashOf _ _, _, _, h
  | .inst _ _, _, _, h | .ivar0, _, _, h | .ivarCons .., _, _, h | .arrow0 _, _, _, h
  | .arrowCons .., _, _, h | .clos .., _, _, h => absurd h (by simp [killAliasTy])

/-- Widening a spine entry to `.any` keeps it denoting, and leaving it keeps it denoting by
`denM_setLocal`. One induction, and it is the `selfSpine` component's whole proof. -/
theorem denSpineFrom_killClosOverSpine {τ : Ty} {m : Machine} {x : String} {w : Value}
    (hw : denM τ m w) : ∀ (I : Ty) (seen : List String) {g : String → Value},
    denSpineFrom seen I m g →
    denSpineFrom seen (killClosOverSpine I x τ) (m.setLocal x w) g := by
  intro I
  induction I with
  | ivarCons n σ rest ihσ ihrest =>
    intro seen g h
    rw [denSpineFrom] at h
    rw [killClosOverSpine, denSpineFrom]
    -- `killClosOverSpine` maps entry types and leaves keys alone, so `seen` threads through
    -- unchanged and a shadowed entry needs nothing.
    refine ⟨?_, ihrest _ h.2⟩
    rcases h.1 with hin | h1
    · exact Or.inl hin
    refine Or.inr ?_
    by_cases hs : capStale x τ σ
    · rw [if_pos hs]; simp [denM]
    · rw [if_neg hs]
      exact denM_setLocal hw (by simpa using hs) h1
  | ivar0 => intro seen g h; simpa [killClosOverSpine, denSpineFrom] using h
  | _ => intro seen g h; exact absurd h (by simp [denSpineFrom])

theorem denSpine_killClosOverSpine {I τ : Ty} {m : Machine} {x : String} {w : Value}
    {g : String → Value} (hw : denM τ m w) (h : denSpine I m g) :
    denSpine (killClosOverSpine I x τ) (m.setLocal x w) g :=
  denSpineFrom_killClosOverSpine hw I [] h

/-- **Widening a spine does not change which names it mentions.** `killClosOverSpine` maps
entry types and leaves the keys alone, so `SelfSpineOk`'s completeness clause transports
across it unchanged. -/
theorem ivarGet?_killClosOverSpine_none : ∀ (I : Ty) {x : String} {τ : Ty} {y : String},
    ivarGet? (killClosOverSpine I x τ) y = none → ivarGet? I y = none
  | .ivarCons n σ rest, x, τ, y, h => by
    simp only [killClosOverSpine, ivarGet?] at h ⊢
    by_cases hn : n = y
    · subst hn; simp at h
    · have hb : (n == y) = false := by simpa using hn
      rw [hb, if_neg (by simp)] at h ⊢
      exact ivarGet?_killClosOverSpine_none rest h
  | .ivar0, _, _, _, _ => rfl
  | .int, _, _, _, _ | .float, _, _, _, _ | .bool, _, _, _, _ | .nilT, _, _, _, _
  | .sym, _, _, _, _ | .any, _, _, _, _ | .never, _, _, _, _ | .cls _, _, _, _, _
  | .clsOf _, _, _, _, _ | .nilable _, _, _, _, _ | .arrayOf _, _, _, _, _
  | .hashOf _ _, _, _, _, _ | .union _ _, _, _, _, _ | .arrow0 _, _, _, _, _
  | .arrowCons _ _, _, _, _, _ | .inst _ _, _, _, _, _ | .clos _ _ _, _, _, _, _
  | .sameAs _ _, _, _, _, _ => rfl

/-! ## Conformance survives a rebinding

The other half, and the one with a side condition. `Judge.vasgn`/`vasgnAlias` rebind a local,
and `Ratchet/Ty.lean`'s `capStale` is what decides which recorded facts that falsifies. The
theorem below is the semantic reading of the fix: it asks for exactly the `capStale` clauses
the two rules carry, and the outgoing state it produces is exactly the one they conclude.

Component by component, and again the shapes are the finding:

* **Heap-only** — `sat`, `core`, `classes`, `defs`, `consts` — `rfl`, because `setLocal`
  writes frames.
* **Frame fields other than `locals`** — `frame`, `blockTy`, `selfTy`, and the `self` that
  `selfSpine` reads — rewrites, because `setLocal` copies every field but `locals`.
  `blockTy`/`selfTy` additionally transport a `denM`, which is where `capStaleCtx` is spent.
* **`env`** is the one that does work: the assigned name reads back as the assigned value
  (`getLocal_setLocal_self`, and this is where `frameInRange` is spent), every other name is
  untouched (`getLocal_setLocal_ne`), and the types are transported by `denM_setLocal` — with
  `killClosOver`'s `.any` covering exactly the bindings for which it would not hold.
* **`asms`** is free by `Later.trans`, as it was across an allocation. -/
theorem StateOk_setLocal {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {x : String}
    {τ ρ : Ty} {w : Value}
    (h : StateOk κ Γ I m)
    (hw : denM τ m w)
    (hcap : capStale x τ τ = false)
    (hctx : capStaleCtx x τ κ = false)
    (hρ : stripAlias ρ = τ)
    (halias : ∀ y σ, ρ = .sameAs y σ → w = (m.setLocal x w).getLocal y) :
    StateOk κ (envSet (killClosOver (killAliasesTo Γ x) x τ) x ρ) (killClosOverSpine I x τ)
      (m.setLocal x w) := by
  simp only [capStaleCtx, Bool.or_eq_false_iff] at hctx
  obtain ⟨⟨hslf, hblk⟩, hcst⟩ := hctx
  exact
    { sat := h.sat
      core := h.core
      frameInRange := by
        have := h.frameInRange
        unfold FrameInRange at this ⊢
        simpa using this
      env := by
        refine ⟨?_, ?_⟩
        · intro y σ hy
          by_cases hyx : y = x
          · -- The assigned name: it reads back as the assigned value, and that value has the
            -- type the rule bound (`hρ` strips the alias `vasgnAlias` wraps it in).
            subst hyx
            rw [envGet?_envSet_self] at hy
            rw [getLocal_setLocal_self m y w h.frameInRange.2, ← Option.some.inj hy]
            exact ⟨by rw [hρ]; exact denM_setLocal hw hcap hw, halias⟩
          · -- Every other name is untouched; its type is either widened to `.any` or
            -- transported by `denM_setLocal`.
            rw [envGet?_envSet_ne _ _ _ _ hyx, envGet?_killClosOver, envGet?_killAliasesTo] at hy
            rw [getLocal_setLocal_ne m x w hyx]
            cases hΓ : envGet? Γ y with
            | none => rw [hΓ] at hy; exact absurd hy (by simp)
            | some σ₁ =>
              rw [hΓ] at hy
              simp only [Option.map_some] at hy
              obtain ⟨hd, hid⟩ := h.env.1 y σ₁ hΓ
              by_cases hst : capStale x τ (killAliasTy x σ₁)
              · rw [if_pos hst] at hy
                have hσ := Option.some.inj hy; subst hσ
                exact ⟨by simp [stripAlias, denM], by intro z ρ₂ hz; exact absurd hz (by simp)⟩
              · rw [if_neg hst] at hy
                have hσ := Option.some.inj hy; subst hσ
                have hK : capStale x τ (killAliasTy x σ₁) = false := by simpa using hst
                refine ⟨?_, ?_⟩
                · refine denM_stripAlias.mpr (denM_setLocal hw hK ?_)
                  exact denM_killAliasTy.mpr (denM_stripAlias.mp hd)
                · intro z ρ₂ hz
                  obtain ⟨hσ₁, hzx⟩ := sameAs_of_killAliasTy hz
                  rw [getLocal_setLocal_ne m x w hzx]
                  exact hid z ρ₂ hσ₁
        · -- **completeness**, and it is the easy direction: a name the outgoing environment
          -- is silent about is not `x` (which `envSet` bound), is silent in `Γ` too (the two
          -- `kill*` walks preserve keys), and the write does not touch it.
          intro y hy
          have hyx : y ≠ x := by
            intro h'
            subst h'
            rw [envGet?_envSet_self] at hy
            exact absurd hy (by simp)
          rw [envGet?_envSet_ne _ _ _ _ hyx, envGet?_killClosOver, envGet?_killAliasesTo] at hy
          rw [getLocal_setLocal_ne m x w hyx]
          cases hΓ : envGet? Γ y with
          | none => exact h.env.2 y hΓ
          | some σ₁ => rw [hΓ] at hy; exact absurd hy (by simp)
      selfSpine := by
        have h2 := h.selfSpine
        unfold SelfSpineOk at h2 ⊢
        rw [currentFrame_setLocal_self, setLocal_heap]
        exact ⟨denSpine_killClosOverSpine hw h2.1,
               fun y hy => h2.2 y (ivarGet?_killClosOverSpine_none _ hy)⟩
      classes := h.classes
      defs := h.defs
      asms := fun a ha m₃ he₃ => h.asms a ha m₃ ((setLocal_later m x w).trans he₃)
      frame := by
        have h2 := h.frame
        unfold FrameOk at h2 ⊢
        cases hf : κ.frame with
        | none => rw [hf] at h2; rw [currentFrame_setLocal_kind]; exact h2
        | some f =>
          rw [hf] at h2
          exact ⟨by rw [currentFrame_setLocal_meth]; exact h2.1,
                 by rw [currentFrame_setLocal_self]; exact h2.2⟩
      closures := trivial
      blockTy := by
        have h2 := h.blockTy
        unfold BlockTyOk at h2 ⊢
        cases hb : κ.blockTy with
        | none => rw [hb] at h2; rw [currentFrame_setLocal_blk]; exact h2
        | some β =>
          rw [hb] at h2
          obtain ⟨b, hb1, hb2⟩ := h2
          refine ⟨b, by rw [currentFrame_setLocal_blk]; exact hb1, ?_⟩
          exact denM_setLocal hw (by rw [hb] at hblk; exact hblk) hb2
      selfTy := by
        have h2 := h.selfTy
        unfold SelfTyOk at h2 ⊢
        cases hσ : κ.selfTy with
        | none => trivial
        | some σ =>
          rw [hσ] at h2
          rw [currentFrame_setLocal_self]
          exact denM_setLocal hw (by rw [hσ] at hslf; exact hslf) h2
      nested := NestedClassesOk.setLocal x w h.nested
      constPaths := by
        -- `capStaleCtx`'s third disjunct is exactly this: no constant's recorded type may
        -- carry a capture spine keyed by the name being written
        refine ConstPathsOk.setLocal hw (fun owner n σ hσ => ?_) h.constPaths
        have hmem := envGet?_mem hσ
        have hall : ∀ (a : String) (b : Ty), (a, b) ∈ κ.consts → capStale x τ b = false := by
          simpa using hcst
        obtain ⟨z, hz⟩ := hmem
        exact hall z σ hz
      consts := by
        intro n σ hn
        obtain ⟨v, hv1, hv2⟩ := h.consts n σ hn
        refine ⟨v, ?_, denM_setLocal hw ?_ hv2⟩
        · rw [show constResolveAt (m.setLocal x w) n = constResolveAt m n by
            simp only [constResolveAt, setLocal_heap, currentFrame_setLocal_cref,
              currentFrame_setLocal_defmod]]
          exact hv1
        · obtain ⟨p, hp⟩ := constGet?_entry hn
          obtain ⟨q, hq⟩ := envGet?_mem hp
          simpa using (List.any_eq_false.mp hcst) (q, σ) hq
      privConsts := trivial
      constScope := ConstScopeOk.setLocal x w h.constScope
      exact := h.exact
      nameFree := by
        intro n hn o md hm
        refine h.nameFree n hn o md ?_
        rw [← hm]
        simp only [Interp.methodOn, classOf, setLocal_heap, currentFrame_setLocal_self]
      bareFree := by
        intro n hn hdef hself
        rw [show lookup (m.setLocal x w).heap (m.setLocal x w).currentFrame.self n
              = lookup m.heap m.currentFrame.self n by
          simp only [lookup, classOf, setLocal_heap, currentFrame_setLocal_self]]
        exact h.bareFree n hn hdef hself
      query := QueryOk.setLocal x w h.query
      clsQuery := ClsQueryOk.setLocal x w h.clsQuery
      missFree := by
        intro hfree hself o md hm
        refine h.missFree hfree hself o md ?_
        rw [← hm]
        simp only [Interp.methodOn, classOf, setLocal_heap, currentFrame_setLocal_self]
      selfLive := by
        intro o ho
        rw [currentFrame_setLocal_self m x w] at ho
        exact h.selfLive o ho }

#print axioms StateOk_ext
#print axioms StateOk_setLocal

end Ratchet.Denote
