import RubyCore.Proof.Static.Locals
import RubyCore.Proof.Static.Mono

/-!
# F1a — the refinement invariant

`PLAN.md` **D10**, `homebrew/typing-a-mutable-method-table.md` §2 and §7. The
heap-side clause of the machine invariant, restated from an equality into a lower
bound:

> **For every method the declarations name, `lookup` resolves it to something
> conforming to its declared signature.**

## Why this, and not "the table matches the declarations"

The equality reading excludes ordinary Ruby, and — the counterexample that forced
the change — it excludes **`sorbet-runtime` itself**, which installs a `sig` by
replacing the method-table entry with a validating wrapper. So the
declaration-matching fragment could not type a single annotated method
(`Types/Fragment.lean`'s header, L139).

The lower bound has the property the equality was reaching for anyway: a
type-stuck outcome comes from a method being **missing** or **wrong-typed**, never
from one being present and unmentioned. So `DeclsOk` says nothing at all about
undeclared names, is therefore **monotone in the method table**, and every
additive step preserves it with no side condition. `DeclsOk_defineMethod` is that
statement, and the only side condition it carries is that the `def` does not
displace a *declared* name — a redefinition, which is F1c's checkable case.

## The decomposition, which is the substance rather than the restatement

Each entry splits into two clauses that behave differently under a heap write:

* **`ResolvesTo`** — resolution: the name reaches a builtin, live, public,
  unshadowed. Heap-dependent, and the *only* thing preservation has to re-derive.
  `Proof/HeapFacts.lean`'s `defineMethod` chain is exactly what discharges it.
* **`ConformsAt`** — conformance: applied to arguments of the declared parameter
  types, that builtin answers a value of the declared return type. Its two
  conclusions are **heap-uniform** (`∀ h'`), which is what makes it transport for
  free; its hypotheses read the invariant's heap, which is where F1b's nominal
  types will need to read it.

That split is why P0's three `int_*_dispatch` rewrites collapse into one
`entry_dispatch`, and why §7's *"the ~128 `builtinSig` conformance lemmas become
per-entry witnesses of the invariant rather than a parallel obligation"* is now
literally true: a new entry is a `ConformsAt` proof and nothing else.

`TableOk` is kept, unchanged, as the **certificate-shaped** form of the same fact
— `heapOkB` decides it and `scripts/heapok_probe.lean` reports it, so F0 is
untouched — and `tableOk_declsOk` is the bridge. That direction (concrete ⇒
general) is deliberate: the invariant carries the general statement, and the
runtime checks the concrete one.
-/

namespace RubyCore
namespace Proof
namespace Static

open Interp
open RubyCore.Types

set_option maxRecDepth 100000

/-! ## 1. Resolution and conformance -/

/-- **Resolution.** In heap `h`, sending `mname` to `recv` reaches the builtin
    `bid`: the table resolves it, the entry is live, public and not
    prelude-suppressed, and neither shadow gate fires.

    Generalizes `IntBuiltinResolves` from the fixed receiver `.int 0` to an
    arbitrary value, and costs **no** extra clause, which is worth recording
    because it was not obvious: `crubySingletonShadow` looked like it would need
    carrying for an abstract receiver, and does not — `invoke` consults that gate
    only when lookup did *not* resolve to a builtin, so an entry satisfying this
    predicate never reaches it. Measured by the proof of `entry_dispatch` not
    using it.

    **Re-measured at F1b and still true** (L141), against a prediction that it
    would not be: `HANDOFF.md` expected an object receiver to bring the singleton
    gate back. It does not, because the gate is a fact about which *branch* runs
    (`md.builtin = none`) and not about which *receiver* arrives, and this
    predicate pins the branch. -/
def ResolvesTo (h : Heap) (recv : Value) (mname bid : String) : Prop :=
  ∃ owner md,
    lookup h recv mname = some (owner, md) ∧
    md.builtin = some bid ∧
    md.undefined = false ∧
    md.visibility = .pub ∧
    md.fromPrelude = false ∧
    crubyShadow h ((ancestors h (classOf h recv)).takeWhile (· != owner)) mname = none

/-- The method-table walk from a **class**, which is all `lookup` ever does with a
    receiver (`lookup h v m = lookup.go h m (ancestors h (classOf h v))`, definitionally). -/
def lookupIn (h : Heap) (k : ObjId) (mname : String) : Option (ObjId × MethodDef) :=
  lookup.go h mname (ancestors h k)

/-- **Resolution, indexed by the dispatch class instead of by a receiver** (L147).
    Every clause of `ResolvesTo` is this predicate at `classOf h recv` — L145's
    `ResolvesTo_classOf` is the observation, and this is the observation taken
    seriously.

    Why it matters, and it is not aesthetics: the inhabitant-indexed clause is
    **not preservable across an allocation**. A fresh object of a declared class
    needs resolution, and the only receiver-shaped hypothesis available is about
    receivers the *old* heap had — of which there may be none, because a class can be
    declared before it has any instances. Indexed by the class, the same fact is
    carried by a hypothesis a growing heap can transport, and `DeclsOk_grow` loses
    its side condition entirely. -/
def ResolvesAt (h : Heap) (k : ObjId) (mname bid : String) : Prop :=
  ∃ owner md,
    lookupIn h k mname = some (owner, md) ∧
    md.builtin = some bid ∧
    md.undefined = false ∧
    md.visibility = .pub ∧
    md.fromPrelude = false ∧
    crubyShadow h ((ancestors h k).takeWhile (· != owner)) mname = none

/-- The two are the same statement at `k = classOf h recv`, definitionally — which is
    why every existing consumer of `ResolvesTo` keeps working unchanged. -/
theorem resolvesTo_of_resolvesAt {h : Heap} {recv : Value} {mname bid : String}
    (hr : ResolvesAt h (classOf h recv) mname bid) : ResolvesTo h recv mname bid := hr

/-- **The dispatch classes a type names.** The ground arms are boot ids and read no
    heap at all; the class arm is a name *and* the requirement that the id really is
    a class — without which an out-of-bounds id would satisfy `.cls "Object"`
    (`className` answers `"Object"` there) and the clause would demand resolution
    from a heap slot that does not exist.

    `valueTy_tyClass` is the bridge from the value judgement, and `plainRecv`'s L147
    clause is what makes the class arm's first component available there. -/
def TyClass (h : Heap) (τ : Ty) (k : ObjId) : Prop :=
  match τ with
  | .int => k = Boot.integerId
  -- L202: `.int`'s twin. A boot id, not a `classPayload?` obligation, which is what
  -- makes the arm free in every transport lemma below (`TyClass_grow` and
  -- `TyClass_defineMethod` both discharge the ground arms by `rfl`).
  | .float => k = Boot.floatId
  | .bool => k = Boot.trueClassId ∨ k = Boot.falseClassId
  | .nilT => k = Boot.nilClassId
  | .sym => k = Boot.symbolId
  | .cls n => (h.classPayload? k).isSome ∧ className h k = n
  -- **The top type dispatches from nowhere** (L183). `tyClassNames .any = []`, so
  -- `declFor` never answers at it and `DeclsOk` never obliges anything — this arm
  -- exists to make the match total, and `False` is the honest content: no value is
  -- typed `any`, so no receiver arrives with it.
  | .any => False
  -- L193, and it is `.any`'s arm for `.any`'s reason: `tyClassNames .nilable = []`,
  -- so `declFor` never answers at a nilable and `DeclsOk` never obliges anything
  -- here. `False` is the honest content — a nilable value may be `nil`, so there is
  -- no one class it dispatches from.
  | .nilable _ => False
  -- **A class object dispatches from `classOf`, whatever `classOf` says** (L184),
  -- and that phrasing is the measurement rather than a choice
  -- (`scripts/classobj_probe.lean`): only 27 of the booted heap's 87 class objects
  -- have a materialized eigenclass, and the split runs through the classes the
  -- slice uses — `String`/`Array`/`Regexp` have one, `Integer`/`Float`/`Hash` do
  -- not and dispatch through `Class`. So *the eigenclass of the class named `n`* is
  -- not a total description and this cannot be stated that way.
  --
  -- The class object itself is pinned by name, which is what `ClassOk`'s uniqueness
  -- clause makes single-valued for every name the table can be keyed on.
  | .clsOf n => ∃ o, (h.classPayload? o).isSome ∧ className h o = n ∧
      k = classOf h (.ref o)
  -- **L238: an `arrayOf` dispatches from `Array`**, and unlike `.any`/`.nilable` this
  -- arm is *inhabited* — `tyClassNames` names `Array`, so `declFor` does answer at it
  -- and `DeclsOk` will oblige every `Array` row over these receivers. The obligation is
  -- the same one `.cls "Array"` carries, which is what makes the arm cost nothing until
  -- a row mentions the element type.
  | .arrayOf _ => (h.classPayload? k).isSome ∧ className h k = "Array"
  -- L269: `.nilable`'s arm for `.nilable`'s reason — a union value may be either
  -- side, so there is no one class it dispatches from; `tyClassNames` is `[]` at
  -- it and `DeclsOk` obliges nothing.
  | .union _ _ => False

/-- **A receiver hands over its dispatch class** — but only at a type dispatch can
    start from, and since L193 that is a hypothesis rather than a fact about every
    `Ty`. `ValueTy` is a relation now, so `ValueTy h v (.nilable σ)` is satisfiable
    while `TyClass h (.nilable σ) k` is `False` — as it must be, since the receiver
    may be `nil`. The two side conditions are exactly `subTy_atomic`'s, and every
    caller gets them from the *declaration*: `declFor` answers `none` at both arms
    (`tyClassNames` is `[]` there), which is what `sigOf_atomic` below reads back. -/
theorem valueTy_tyClass {h : Heap} {v : Value} {τ : Ty} (ha : τ ≠ .any)
    (hn : ∀ τ', τ ≠ .nilable τ')
    -- **L239**: and not an array type, which is `ValueTy.atomic`'s new side condition —
    -- `tyClassNames` is `[]` at the arm today, so every caller reads it back from
    -- `declFor`'s `none` exactly as it reads the other two.
    (hnar : ∀ σ, τ ≠ .arrayOf σ) (hv : ValueTy h v τ) :
    TyClass h τ (classOf h v) := by
  have hex := hv.atomic ha hn hnar
  clear hv
  cases v with
  | int a => cases τ <;> simp_all [valueTy?, TyClass, classOf]
  | bool b =>
    have : τ = .bool := by simpa [valueTy?] using hex.symm
    subst this
    cases b
    · exact Or.inr rfl
    · exact Or.inl rfl
  | nil => have : τ = .nilT := by simpa [valueTy?] using hex.symm
           subst this; rfl
  | sym s => have : τ = .sym := by simpa [valueTy?] using hex.symm
             subst this; rfl
  | ref o =>
    have hv : ValueTy h (.ref o) τ := ValueTy.exact hex
    -- **Two arms since L185**, and they land in different `TyClass` cases: a plain
    -- receiver dispatches from its `klass` and its type names *that* class, while a
    -- class object dispatches from `classOf` — its eigenclass, or `Class` when it
    -- has none — and its type names the object's own class. The second is the whole
    -- content of the class-object arm and the reason `TyClass` says `classOf`
    -- rather than naming a chain.
    rcases valueTy_ref_inv (subTy_any_false ha hn)
      (fun σ => by
        by_cases hq : subTy (.arrayOf σ) τ = true
        · exact absurd ((subTy_atomic ha hn).mp hq) (Ne.symm (hnar σ))
        · simpa using hq) hv with ⟨hp, hs⟩ | ⟨hc, hs⟩
    · rw [← (subTy_atomic ha hn).mp hs]
      exact ⟨valueTy_ref_klass_isSome hp, rfl⟩
    · rw [← (subTy_atomic ha hn).mp hs]
      refine ⟨o, ?_, rfl, rfl⟩
      unfold classRecv at hc
      simp only [Bool.and_eq_true] at hc
      exact hc.2
  -- L202: the ground arm is a boot id on both sides, so the case is `rfl` once the
  -- type equation is used. `classOf` answers `Boot.floatId` for a `.flt` by
  -- definition (`Heap.lean:471`), which is `TyClass`'s `.float` clause verbatim.
  | flt f => cases hex; rfl

/-! ### Resolution to a **user-defined** method

`ResolvesAt` pins `md.builtin = some bid`, and that is not a restriction anyone
chose — it is what `ConformsAt`'s conclusion forces (`Builtins.run … m = .ok w m`,
the machine back unchanged in one step). A method with `builtin = none` reaches
`enterUserMethod`, which **pushes a frame**: the send produces no value at all,
and the declared return type is a claim about what the activation eventually
returns.

So `EntryOk` has to become a disjunction, and this is the second disjunct's
resolution half. Every clause is a gate on `invoke`'s path to `enterUserMethod`,
read off `Interp/Send.lean` in order, and there is nothing here that is not one:

| clause | gate |
|---|---|
| `lookupIn … = some (owner, md)` | the walk resolves |
| `builtin = none` | takes the user branch rather than `Builtins.run` |
| `undefined = false` | not an `undef` tombstone |
| `visibility = .pub` | `visError?` at an `.explicit` site |
| `crubyShadow … = none` | the between-classes fidelity gate |
| `params = []`, `declared = []` | `enterUserMethod` binds nothing, so the callee's environment is `[]` |
| `capturedFrame = none` | `FrameConforms`'s first clause — the frame is self-contained |
| `(classPayload? md.owner).isSome` | `FrameConforms`'s definee clause; the frame's `defmod` **is** `md.owner` |

**Note what is absent: `fromPrelude`.** `ResolvesAt` requires
`fromPrelude = false` because a prelude method has no `bid` to run. The user arm
has no such need — a prelude-Ruby method is *exactly* a `MethodDef` with
`builtin = none`, and every gate above is one it can pass. That is D8's dominant
category (`widening-the-fragment.md` §5.1: 153 of 285 prelude methods rising to
269) becoming **expressible**, which `HANDOFF.md` §constraint 1 records as
blocked. The shadow clause keeps the `fromPrelude` conditional `invokeDispatch`
itself applies, rather than dropping it.

`crubySingletonShadow` — the other gate on this branch, and the one three rungs
predicted would come back — costs nothing again: it answers `none` unless the
receiver's payload is `.cls`, which `plainRecv` refutes. Third prediction, third
time it is free. -/
def ResolvesUser (h : Heap) (k : ObjId) (mname : String) (md : MethodDef) : Prop :=
  ∃ owner,
    lookupIn h k mname = some (owner, md) ∧
    md.builtin = none ∧
    md.undefined = false ∧
    md.visibility = .pub ∧
    md.params = [] ∧
    md.declared = [] ∧
    md.capturedFrame = none ∧
    (h.classPayload? md.owner).isSome ∧
    crubyShadow h
      (if md.fromPrelude then [] else (ancestors h k).takeWhile (· != owner)) mname = none ∧
    -- **L189: the callee's lexical constant scope contains `Object`.** A method frame
    -- takes `md.cref` (`Interp/Dispatch.lean:154`), so the `StackCtx` clause the
    -- `.const` read rule needs has to cross the call — and this is where it crosses.
    -- Heap-independent, so both transports carry it for free; established by the `def`
    -- step from the defining frame's own clause, since `evalExpr` sets
    -- `cref := m.currentFrame.cref` (`Interp.lean:228`).
    Boot.objectId ∈ md.cref ∧
    -- **L209: the definee is on the dispatch chain it was found from.** `super`'s
    -- whole frame-side cost, and it crosses the call here for the same reason the
    -- `cref` clause does: the callee's frame takes `defmod := md.owner`, and
    -- `doSuper` walks `(ancestors h (classOf h self)).dropWhile (· != defmod)` — which
    -- empties the list, and raises `NoMethodError`, if the definee is *not* on it.
    --
    -- Not derivable from `lookupIn h k mname = some (owner, md)` above, and the reason
    -- is a gap the existential hides: `lookup.go` returns a member of the list it
    -- walked, so *`owner`* is on the chain, but the frame is built with **`md.owner`**
    -- and nothing in the fragment pins the two together. So it is stated, and the one
    -- production site (`def`'s consecution, where `md.owner = defmod` by construction
    -- and `ClassOk`'s head clause puts `defmod` first on its own chain) has it for
    -- free.
    md.owner ∈ ancestors h k ∧
    -- **L210: the method carries no alias name.** `userFrame` builds the activation
    -- with `meth := md.superName.getD mname`, and the *context* the body was checked in
    -- says `meth := some mname` — so the two agree exactly when `superName` is unset.
    -- It is set only by the `alias` rule (`Interp.lean:277`); a plain `def` leaves it at
    -- its default, and `alias` has no `infer` arm. So the clause is free at the one
    -- production site and a prelude method that *is* an alias simply cannot witness a
    -- row, which is sound.
    md.superName = none

/-- **Conformance for a user method is discharged by the checker, not by running
    anything**: the body infers at the declared return type in the environment
    `enterUserMethod` builds, which for a zero-parameter method is the empty one.

    This is the reflexive step, and it is worth naming as such. Every obligation
    the invariant has carried until now is a fact about a *Lean builtin*, proved
    once, externally, and independent of the checker. This one makes `infer`'s own
    verdict on a method body a conjunct of the soundness invariant — the checker
    appears inside the statement of its own soundness theorem. That is sound (the
    recursion is on the *heap*, not on the proof), and it is the reason a user
    witness cannot be a lemma about `startArgs` the way `ConformsAt` is: the fact
    it asserts is not about one step.

    **The body's output table must be the one it was checked at** (F1b.8). A
    method whose body itself declares a method would leave rows in force that the
    caller's continuation was not typed against, and `frameK` — which resumes the
    caller at a table fixed when the frame was pushed — has no way to carry them.
    Requiring `md.body` to leave the table alone is what makes the pop total, and
    it is the same shape as `LoopOk`'s stability condition and for the same
    reason. It costs nothing today, since no rule grows the table at all. -/
def UserConforms (D : Decls) (c mname : String) (md : MethodDef) (d : MethodDecl) : Prop :=
  -- **L242**, for `ConformsAt`'s reason at the other witness: the body below is checked
  -- by `infer` at a context with no block channel at all (`FrameCtx` has no `blk`
  -- field), so a row declaring a block would oblige a `yield` rule that does not exist.
  d.params = [] ∧ d.blk = none ∧ defFree md.body = true ∧
    -- **L198: the context's `ret` is carried, not fixed**, and that is what breaks a
    -- circularity rather than papering over it.
    --
    -- `return e` checks `e` against `ctx.ret` — the *declared* return type — so a body
    -- containing one has to be checked at a context that already names it. But the
    -- `def` rule *computes* the return type from the body, so it cannot name it
    -- before checking: `infer` at `ret := none` is all it has. Fixing this predicate
    -- at `some d.ret` would make the `def` rule unable to discharge its own row;
    -- fixing it at `none` would make `KontOk.frameK`'s agreement vacuous and
    -- `RetOk` underivable.
    --
    -- Carrying `r` is the resolution. `def` supplies `r = none`, which is exactly
    -- "this body contains no `return`". A **declared** signature (`PLAN.md` W8's
    -- `sig`) supplies `r = some d.ret`, and that is the rung at which a `return`
    -- inside a *running* method becomes reachable — the rule and its consecution case
    -- are proved either way, which is what keeps this honest rather than speculative.
    -- **L210: the context names the method.** `infer`'s `def` arm builds exactly this
    -- context, and the machine's activation carries the same name by `ResolvesUser`'s
    -- `superName` clause — which is what lets a `super` in the body be typed against a
    -- row keyed on *this* method's name.
    -- **L229: the body's own type is *below* the declared return, not equal to it.**
    --
    -- The equality was right while `inferBody` reported the body's last expression; it is
    -- wrong once the reported type is the **join of the method's exits**. A body ending in
    -- an `Integer` with a bare `return` in it has type `Integer` and declares
    -- `T.nilable(Integer)`, and there is no reading of that pair as an equality.
    --
    -- Nothing downstream had to widen to accept it: `CtlOk`'s eval clause has allowed the
    -- continuation to sit at a wider type than the expression's since L193, so the frame
    -- push spends this `subTy` exactly where that clause already expected one.
    ∃ Γ' r τb, infer D [] md.body false
        { cls := c, selfCls := some c, ret := r, meth := some mname, params := some [] }
      = some (τb, Γ', D) ∧ subTy τb d.ret = true ∧ (∀ σ, r = some σ → σ = d.ret)

/-- **Conformance to a declared signature.** On a receiver of the declared class
    and arguments of the declared parameter types, `bid` answers a value of the
    declared return type without touching the machine, and defers to no prelude
    twin.

    The name clause excludes `send`/`public_send`/`__send__`, which `invoke` treats
    specially: their *first argument* is the real method name, so a declared
    signature for them would describe the wrong call. This is the same exclusion
    `int_bin_dispatch` carried as an explicit hypothesis, promoted to part of what
    conformance means.

    The deferral clause is `∀ h'` on purpose. L116 put a **prelude-twin deferral**
    in front of every builtin — one whose answer would need a dispatch it cannot
    perform hands the call to prelude Ruby instead of running — and `deferTwin?`
    reads the *method table*, so a heap write can change it. Requiring the
    deferral to be absent in every heap is what makes conformance survive a `def`;
    for arithmetic over two Integers it is true by computation, and an entry for
    which it is false does not belong in the table at all.

    **Heap-uniform since L146, and that is a change of statement rather than of
    strength.** It used to be indexed by the invariant's heap, with the machine
    quantified *inside* the existential — so `∀ m, run … m = .ok w m` (heap-uniform
    conclusion) sat under `ValueTy h recv τr` (heap-*dependent* hypothesis). The
    asymmetry cost a transport: `ConformsAt_defineMethod` had to read its hypotheses
    in the old heap and its conclusion in the new one, which is the only reason
    `TypeAgree` needed a backward direction at all (L143) — and the backward
    direction **does not exist for a growing heap**, so the producer could not have
    had it.

    Quantifying the machine over the whole statement fixes both: conformance is now
    a fact about a builtin and a declaration, mentioning no heap, so it is not a
    clause preservation has to re-establish. `DeclsOk`'s heap-dependent half is
    exactly `ResolvesTo` — which is what L140's split said it should be, one level
    more honestly than L140 achieved. Every witness's *proof* is unchanged: the
    hypotheses it actually used were `valueTy_int`-shaped inversions, and those are
    heap-independent. -/
def ConformsAt (τr : Ty) (mname bid : String) (d : MethodDecl) : Prop :=
  (mname == "send" || mname == "public_send" || mname == "__send__") = false ∧
  bid ≠ "Object#raise" ∧
  -- **L242: the row takes no block**, and this is where the new field's inertness is
  -- stated rather than assumed. `Builtins.run bid recv args m` below is a *blockless*
  -- call — the signature has no slot for a `Proc` and `invoke` reaches this path only
  -- with `blk = none` — so a row declaring a block would be a claim about a step this
  -- conjunction does not describe. Free at both shipped tables (every row defaults the
  -- field), and it is the exact place the bill lands: a block-taking row is witnessed by
  -- a **third** arm of `EntryOk`, the native iterator, not by widening this one.
  d.blk = none ∧
  -- **`new` is excluded** (L185), and it is the third of exactly this kind of
  -- clause. `invoke` intercepts a `.cls` receiver at `invokeMaybeNew` when the name
  -- is `"new"` (`Interp/Send.lean:106`) and allocates rather than dispatching, so a
  -- row named `new` would be a claim about a step `entry_dispatch` does not
  -- describe. Costs nothing — no row is named `new` — and it is what lets the
  -- class-object receiver case be a `simp`. `Class#new` is Wall 2's item anyway
  -- (`slice-verdict.md` §4a: it allocates).
  mname ≠ "new" ∧
  ∀ (m : Machine) recv args, ValueTy m.heap recv τr → ValuesTy m.heap args d.params →
    (∀ h' : Heap, Builtins.deferTwin? h' bid recv args = none) ∧
    -- **L215: the conclusion may allocate**, and that is Wall 2's first half.
    --
    -- It used to be `Builtins.run … m = .ok w m` — *the machine unchanged* — which is
    -- what `slice-verdict.md` §4 names as the wall: a builtin that allocates cannot be
    -- tabulated, and both remaining populations need one. `Class#new` allocates by
    -- definition; and a **block send allocates before it dispatches at all**, because
    -- `finishSend` reifies a literal block into a `Proc` (`Interp/Send.lean`), so the
    -- 15 `send-with-block` bodies are behind this clause and not only behind the
    -- three-channel judgement.
    --
    -- The generalization is the weakest thing `inv_grow_value` (L149) will accept, and
    -- that is why it is this and not something more permissive: `PlainGrow` for the
    -- heap, and `frames`/`stack`/`kont` untouched. Nothing else in `Inv` reads the
    -- machine.
    --
    -- **What it excludes, and the exclusion is the point**: a builtin that *mutates* an
    -- existing object — `Array#push`, `String#<<` — is not a `PlainGrow`, because
    -- `get`-agreement below the old size is exactly what in-place mutation breaks. Such
    -- a builtin still cannot be tabulated, and now for a reason the clause states rather
    -- than for one it merely happened to imply. A mutating row needs its own transport
    -- (`IvarOnly`'s shape at a payload), which is a rung and not a relaxation.
    -- **L228 adds `globals`**, and it is the sentence above ("nothing else in `Inv` reads
    -- the machine") coming due: `GlobalsOk` does. Free at both witnesses, which leave the
    -- machine alone — and a real restriction on the *next* tabulated builtin, which is the
    -- honest place for it: a builtin that wrote `$~` would otherwise silently invalidate a
    -- declared global.
    ∃ w m', Builtins.run bid recv args m = .ok w m' ∧ ValueTy m'.heap w d.ret ∧
      PlainGrow m.heap m'.heap ∧
      m'.frames = m.frames ∧ m'.stack = m.stack ∧ m'.kont = m.kont ∧
      m'.globals = m.globals

/-- One declared method, satisfied: **some** builtin both resolves for every
    receiver of the class and conforms. Existential in `bid` rather than pinning
    it, which is what makes the condition a lower bound — the invariant never says
    *which* implementation answers, only that a conforming one does. -/
def BuiltinEntryOk (h : Heap) (τr : Ty) (mname : String) (d : MethodDecl) : Prop :=
  ∃ bid, (∀ k, TyClass h τr k → ResolvesAt h k mname bid) ∧ ConformsAt τr mname bid d

/-- **The receiver type a user row is keyed at** (L241), and it is a *relation* rather than
    the equation `τr = .cls c` it replaces.

    The equation was the pinning that made `mem_declAtoms_iff`'s certificate reading break
    when `arrayOf` was given dispatch (L240): the enumeration `declTys` is finite, element
    types are not, so `DeclsOk` at an `arrayOf` receiver has to be *derivable* from the
    `.cls "Array"` atom. For a builtin entry it already is — `TyClass` at the two types is
    the same proposition, definitionally — and for a user entry the equation is what
    refused it.

    Two shapes and no more: a class type at its own name, and the parameterised array type
    at `Array`. Deliberately not `tyClassNames τr = [c]`, which would also admit the ground
    arms — a user row on `Integer` is what `hground` exists to forbid, and widening this to
    reach it would make `UserEntryOk` satisfiable at a type whose inhabitants are
    immediates. -/
def UserKey (τr : Ty) (c : String) : Prop :=
  τr = .cls c ∨ (∃ e, τr = .arrayOf e) ∧ c = "Array"


/-- At a class type the key *is* the equation, which is what every consumer reads: a send's
    receiver type is a `.cls` (that is what `plainRecv`/`valueTy?` answer), so the second
    shape is refuted by the constructor. -/
theorem UserKey.cls_inv {n c : String} (h : UserKey (.cls n) c) : n = c := by
  rcases h with h | ⟨⟨e, he⟩, -⟩
  · simpa using h
  · exact absurd he (by simp)

theorem UserKey.cls {c : String} : UserKey (.cls c) c := Or.inl rfl

/-- **The user witness** (L157): resolution to a `MethodDef` with `builtin = none`,
    with conformance discharged by the *checker* rather than by running anything.

    The table is the invariant's own. A witness that carried a *smaller* one,
    related by `SubDecls`, is what the arm will need once a `def` grows the table
    — a body is checked where it is written and called later — and it is
    deliberately not here yet: nothing in this commit grows the table, so the
    clause would be a speculative one with no proof to justify its shape.
    `SubDecls` is defined (`Types/Decls.lean`) and unused, which is the honest
    place to leave it. -/
def UserEntryOk (D : Decls) (h : Heap) (τr : Ty) (mname : String) (d : MethodDecl) :
    Prop :=
  ∃ md c, UserKey τr c ∧ (∀ k, TyClass h τr k → ResolvesUser h k mname md) ∧
    className h md.owner = c ∧ UserConforms D c mname md d

/-- **The name misses on this dispatch class** (L254), and it is the *opposite polarity*
    from `ResolvesAt`/`ResolvesUser`.

    `tryIterator` is reached only from `dispatchMiss`, which `invokeDispatch` reaches only
    when `lookup` answers `none`. So a block row's witness has to say the name is **not**
    there — and a program that reopened `Array` and defined `each` would take a different
    step entirely.

    That reads like an obligation `defineMethod` cannot preserve, and it is not: `infer`'s
    `def` rule requires `declaresName D name = false`, so the *declared* name and the
    *installed* one are disjoint at every `def` the fragment admits, and a miss at one
    name survives an installation at another. The same argument `DeclsOk_defineMethod`
    already makes for the two resolving arms, read in the other direction. -/
def MissesAt (h : Heap) (k : ObjId) (mname : String) : Prop :=
  lookupIn h k mname = none

/-- **A block-taking row, witnessed by a native iterator** (L254) — `EntryOk`'s third
    arm, and the one L242 named as the bill for `MethodDecl.blk`.

    Pinned to `Array#each` and nothing else, which is the same standing `baseDecls`'
    three `Integer` rows had when they were the whole table: `tryIterator`'s `match` on
    the name is a sixteen-way split with a different `IterKind`, element list and seed
    per arm (L244), so there is no shared statement and each row that is ever declared
    pays for its own copy.

    **`bs.params = [.any]` is what keeps `Ty.arrayOf` off the critical path.**
    `KontOk.iterK`'s *every remaining element has the block's parameter types* premise is
    then `ValuesTy h a [.any]`, which holds of **every** value (`ValueTy.any`, L232) — so
    this arm needs no claim about the array's contents at all. A precise element type
    would need `ValueTy h recv (.arrayOf σ)`, which is L239's arm and the dispatch rung
    behind it. -/
def IterEntryOk (h : Heap) (τr : Ty) (mname : String) (d : MethodDecl) : Prop :=
  τr = .cls "Array" ∧ mname = "each" ∧ d.params = [] ∧ d.ret = .cls "Array" ∧
  (∃ br, d.blk = some { params := [.any], ret := br }) ∧
  ∀ k, TyClass h τr k → MissesAt h k mname

/-- A declared method is satisfied by **any** of three kinds of witness. A disjunction
    rather than a generalization because the three produce *different steps*:
    `entry_dispatch` lands a value in one step, `user_dispatch` lands a frame with
    the body still to run, and the iterator lands **two** frames with a block body in
    `ctl`. `HANDOFF.md` §constraint 1 predicted this shape ("a disjunction of witness
    kinds") and predicted the reason. -/
def EntryOk (D : Decls) (h : Heap) (τr : Ty) (mname : String) (d : MethodDecl) : Prop :=
  BuiltinEntryOk h τr mname d ∨ UserEntryOk D h τr mname d ∨ IterEntryOk h τr mname d

/-- **A row `sigOf` handed over is witnessed by one of the *two* resolving arms** (L254).

    `sigOf` refuses a block-taking row (L242) and `sigOf_declFor` therefore concludes at
    `blk := none`, while the iterator arm requires `some` — so the third disjunct is
    refuted by one projection wherever a blockless rule reads the table. Stated once here
    rather than at each of the three send cases, which then keep the two-way `rcases`
    they had. -/
theorem EntryOk.blockless {D : Decls} {h : Heap} {τr : Ty} {mname : String}
    {ps : List Ty} {τret : Ty}
    (he : EntryOk D h τr mname { params := ps, ret := τret, blk := none }) :
    BuiltinEntryOk h τr mname { params := ps, ret := τret, blk := none } ∨
      UserEntryOk D h τr mname { params := ps, ret := τret, blk := none } := by
  rcases he with h1 | h2 | ⟨-, -, -, -, ⟨br, hdb⟩, -⟩
  · exact Or.inl h1
  · exact Or.inr h2
  · exact absurd hdb (by simp)

/-- **And the converse reading** (L255): a row that *does* take a block is witnessed by
    the iterator arm and nothing else, because both resolving arms pin `blk = none`
    (`ConformsAt`'s and `UserConforms`'s L242 conjuncts). This is what the block-send
    rule's consecution case reads its dispatch out of. -/
theorem EntryOk.iter {D : Decls} {h : Heap} {τr : Ty} {mname : String} {d : MethodDecl}
    {bs : BlockSig} (he : EntryOk D h τr mname d) (hb : d.blk = some bs) :
    IterEntryOk h τr mname d := by
  rcases he with ⟨bid, -, -, -, hnb, -, -⟩ | ⟨md, c, -, -, -, -, hnb, -, -⟩ | h3
  · exact absurd hb (by rw [hnb]; simp)
  · exact absurd hb (by rw [hnb]; simp)
  · exact h3

/-- The receiver-shaped form the send cases want, recovered from the class-indexed
    one. This direction is all anything needs, and it is the direction that is
    available: a receiver hands over its dispatch class (`valueTy_tyClass`), while a
    class does not hand over a receiver — which is the asymmetry L147 is about. -/
theorem EntryOk.resolves {h : Heap} {τr : Ty} {mname bid : String} {recv : Value}
    (ha : τr ≠ .any) (hn : ∀ τ', τr ≠ .nilable τ')
    -- L239: `valueTy_tyClass`'s third side condition, threaded.
    (hnar : ∀ σ, τr ≠ .arrayOf σ)
    (hres : ∀ k, TyClass h τr k → ResolvesAt h k mname bid)
    (hrv : ValueTy h recv τr) : ResolvesTo h recv mname bid :=
  resolvesTo_of_resolvesAt (hres (classOf h recv) (valueTy_tyClass ha hn hnar hrv))

/-- **What one constant row obliges** (L195), and it is three conjuncts where
    `ClassOk`'s class-object block carried seven — because `ValueTy h v (.clsOf n)`
    *already* says "a class-object receiver named `n`" (`classRecv` plus the name),
    so `classPayload?`, `className`, `k ≠ regexpId` and `k ≠ mathId` are all inside
    it. Stating it over `ValueTy` rather than over the class-object shape is also what
    makes the *next* population free: a non-class constant is this same clause at a
    different `Ty`.

    The third conjunct is L189's, unchanged and still load-bearing: `evalExpr`'s
    `.const` walks the frame's `cref` **before** the ancestors, and sole ownership is
    what makes any `cref` hit `Object`'s whatever the `cref` is (`constRead_sole`). It
    is why the rule needs no frame clause beyond `Object ∈ cref`. -/
def ConstOk (h : Heap) (n : String) (τ : Ty) : Prop :=
  ∃ v, constOwn h Boot.objectId n = some v ∧ ValueTy h v τ ∧
    (∀ j, (h.classPayload? j).isSome → j ≠ Boot.objectId → constOwn h j n = none)

/-- **`ConstOk` across an allocation.** `PlainGrow` pins `classPayload?` at every
    id, so `constOwn` is unmoved at every id, and `ValueTy` transports by
    `typeAgree_of_plainGrow`. -/
theorem constOk_grow {h h' : Heap} {n : String} {τ : Ty} (hg : PlainGrow h h')
    (hsat : Saturated h) (hc : ConstOk h n τ) : ConstOk h' n τ := by
  obtain ⟨v, hv, hty, hsole⟩ := hc
  refine ⟨v, ?_, ValueTy.congr (typeAgree_of_plainGrow hg hsat) hty, fun j hj hjo => ?_⟩
  · unfold constOwn at hv ⊢; rw [hg.payload]; exact hv
  · unfold constOwn at hsole ⊢
    rw [hg.payload]
    exact hsole j (by rw [← hg.payload]; exact hj) hjo

/-- **And across a `def`.** `consts_defineMethod` (L156) is the constant-table half
    and `typeAgree_defineMethod` (L137) the value half; both were written for other
    consumers, which is the evidence that the clause is stated at the right level. -/
theorem constOk_defineMethod {h : Heap} {cls : ObjId} {name : String} {md : MethodDef}
    {n : String} {τ : Ty} (hc : ConstOk h n τ) :
    ConstOk (defineMethod h cls name md) n τ := by
  obtain ⟨v, hv, hty, hsole⟩ := hc
  refine ⟨v, by rw [constOwn_defineMethod]; exact hv,
    ValueTy.congr (typeAgree_defineMethod h cls name md) hty, fun j hj hjo => ?_⟩
  rw [constOwn_defineMethod]
  exact hsole j (by rw [← classPayload?_isSome_defineMethod]; exact hj) hjo

/-- **What one instance-variable row obliges** (L196), and the quantifier is the
    whole content: **every** object of the class, not one receiver.

    An ivar read has no receiver to constrain — `@x` reads the frame's `self`, and the
    invariant knows only its *class* (`StackCtx`'s `selfCls` clause). So a row on
    `(c, @x)` is a claim about every instance of `c` at once, which is what makes the
    *write* rule owe a conformance check: L191 admitted `@x = e` freely precisely
    because nothing claimed anything about ivars.

    **`none` is admitted, and that is not laxity.** An unset instance variable reads as
    `nil` in Ruby, so the read rule answers `mkNilable τ` rather than `τ` and the
    clause has nothing to say about an absent entry. Tracking definite assignment is
    what would let the read answer `τ`, and it is a different rung (`initialize`, and
    therefore Wall 2). -/
def IvarOk (h : Heap) (c x : String) (τ : Ty) : Prop :=
  ∀ o, o < h.objs.size → className h (h.get o).klass = c →
    ∀ v, ((h.get o).ivars.find? (·.1 == x)).map Prod.snd = some v → ValueTy h v τ

/-- `defineMethod` writes one object's **payload**; `ivars` and `klass` are different
    fields of the same structure, so both are unmoved at every id (L196). -/
theorem get_defineMethod_fields (h : Heap) (cls : ObjId) (name : String)
    (md : MethodDef) (o : ObjId) :
    ((defineMethod h cls name md).get o).ivars = (h.get o).ivars ∧
    ((defineMethod h cls name md).get o).klass = (h.get o).klass := by
  unfold defineMethod
  cases hc : h.classPayload? cls with
  | none => exact ⟨rfl, rfl⟩
  | some c =>
    by_cases ho : o = cls
    · subst ho
      by_cases hb : o < h.objs.size
      · simp only [Heap.setClassPayload, Heap.get, Heap.set]
        rw [objs_getD_set!_self _ _ _ hb]
        exact ⟨rfl, rfl⟩
      · simp only [Heap.setClassPayload, Heap.get, Heap.set]
        rw [objs_getD_set!_oob _ _ _ hb]
        exact ⟨rfl, rfl⟩
    · simp only [Heap.setClassPayload, Heap.get, Heap.set]
      rw [objs_getD_set!_ne _ _ _ _ ho]
      exact ⟨rfl, rfl⟩

/-- **`IvarOk` across an allocation** (L196). Two things to say and they are the two
    halves of `PlainGrow`: at an *old* id nothing moved (`className`, the `ivars`
    list) and `ValueTy` transports; at the **fresh** id the clause is about an object
    the old heap did not have, so the hypothesis cannot supply it — `PlainGrow`'s
    `get`-agreement below the old size is what bounds the quantifier back. -/
theorem ivarOk_grow {h h' : Heap} {c x : String} {τ : Ty} (hg : PlainGrow h h')
    (hsat : Saturated h) (hi : IvarOk h c x τ) : IvarOk h' c x τ := by
  intro o ho hcn v hv
  by_cases hb : o < h.objs.size
  · rw [hg.get o hb] at hcn hv
    exact ValueTy.congr (typeAgree_of_plainGrow hg hsat)
      (hi o hb (by rwa [hg.className_eq] at hcn) v hv)
  · -- Above the old size the object has no ivars at all, so the read is `none` and
    -- the hypothesis `hv` is contradictory.
    rw [hg.freshIvars o (by omega)] at hv
    exact absurd hv (by simp)

/-- **And across a `def`.** `setClassPayload` writes one object's payload; `ivars` is
    a different field of `Object`, so the list is unmoved at every id, and `className`
    is `clsName_defineMethod`'s. -/
theorem ivarOk_defineMethod {h : Heap} {cls : ObjId} {name : String} {md : MethodDef}
    {c x : String} {τ : Ty} (hi : IvarOk h c x τ) :
    IvarOk (defineMethod h cls name md) c x τ := by
  intro o ho hcn v hv
  rw [objs_size_defineMethod] at ho
  obtain ⟨hiv, hkl⟩ := get_defineMethod_fields h cls name md o
  rw [hiv] at hv
  rw [hkl, className_defineMethod] at hcn
  exact ValueTy.congr (typeAgree_defineMethod h cls name md) (hi o ho hcn v hv)

/-- The **method** half, named because the assertion language has atoms for exactly
    it: `declAssn`'s denotation is `RowsOk`, not `DeclsOk`, and since L195 those are
    different propositions. Giving the constant half an atom is the assertion
    language's own next rung. -/
def MethodRowsOk (D : Decls) (h : Heap) : Prop :=
  ∀ τr mname d, declFor D τr mname = some d → EntryOk D h τr mname d

/-- **What one scoped-constant row obliges** (L205), and the two quantifiers are the
    content.

    `∀ o` for `IvarOk`'s reason: the rule is keyed on a **name**, and only `ClassOk`'s
    uniqueness clause ties a name to one id — over the *readable* names, not over every
    name a program can write. So a row on `(C, n)` claims something about every class
    object named `C` at once.

    The second conjunct is the `private_constant` gate (L104), and it has to be here
    rather than at the delivery for `KontOk.asgnIvar`'s reason: it is a fact about the
    heap that the *rule* cannot see, so the declaration is what carries it.

    `constLookupFrom` rather than `constOwn`, because that is what the machine does —
    `.cpathK` walks the container's **ancestors** (`Interp/Kont.lean:130`), so a
    constant inherited from a superclass is visible through `C::n` and the clause has
    to be about the walk, not about one table. -/
def ScopedConstOk (h : Heap) (c n : String) (τ : Ty) : Prop :=
  ∀ o, (h.classPayload? o).isSome → className h o = c →
    ((ancestors h o).all fun a =>
        match h.classPayload? a with
        | some cp => !cp.privateConsts.contains n
        | none => true) = true ∧
    ∃ v, constLookupFrom h o n = some v ∧ ValueTy h v τ

/-- **`ScopedConstOk` across an allocation** (L205). Every clause is pinned by a
    `PlainGrow` field: `classPayload?` at every id (so both the constant tables and the
    `private_constant` lists), `className`, the ancestor walk (with saturation), and
    `ValueTy` by `typeAgree_of_plainGrow`. -/
theorem scopedConstOk_grow {h h' : Heap} {c n : String} {τ : Ty} (hg : PlainGrow h h')
    (hsat : Saturated h) (hs : ScopedConstOk h c n τ) : ScopedConstOk h' c n τ := by
  intro o ho hcn
  rw [hg.payload] at ho
  rw [hg.className_eq] at hcn
  obtain ⟨hpriv, v, hv, hty⟩ := hs o ho hcn
  refine ⟨?_, v, ?_, ValueTy.congr (typeAgree_of_plainGrow hg hsat) hty⟩
  · rw [hg.ancestors_eq hsat]
    simp only [hg.payload]
    exact hpriv
  · rw [constLookupFrom_congr (fun j => by rw [hg.payload]) (hg.ancestors_eq hsat o)]
    exact hv

/-- **And across a `def`** (L205) — `constLookupFrom_defineMethod` and
    `privateConsts_defineMethod` are the two halves, both written for this clause. -/
theorem scopedConstOk_defineMethod {h : Heap} {cls : ObjId} {name : String}
    {md : MethodDef} {c n : String} {τ : Ty} (hs : ScopedConstOk h c n τ) :
    ScopedConstOk (defineMethod h cls name md) c n τ := by
  intro o ho hcn
  rw [classPayload?_isSome_defineMethod] at ho
  rw [className_defineMethod] at hcn
  obtain ⟨hpriv, v, hv, hty⟩ := hs o ho hcn
  refine ⟨?_, v, ?_, ValueTy.congr (typeAgree_defineMethod h cls name md) hty⟩
  · rw [ancestors_defineMethod]
    refine List.all_eq_true.mpr fun a ha => ?_
    have hpa := List.all_eq_true.mp hpriv a ha
    have hc := privateConsts_defineMethod h cls a name md
    cases h1 : (defineMethod h cls name md).classPayload? a with
    | none => simp [h1]
    | some cp' =>
      cases h2 : h.classPayload? a with
      | none => rw [h1, h2] at hc; exact absurd hc (by simp)
      | some cp =>
        rw [h1, h2] at hc
        simp only [Option.map_some, Option.some.injEq] at hc
        rw [h2] at hpa
        simpa [h1, hc] using hpa
  · rw [constLookupFrom_defineMethod]
    exact hv

/-! ### L211: the `super` table's clause

`doSuper` (`Interp/Send.lean:260`) computes its target from three things the frame
carries — the running method's name, the definee, and the receiver — and the only one
of the three the invariant knows *by name* is the definee (`StackCtx` clause 2). So the
clause has to be quantified over every class object of that name and every chain such a
class is on, which is `IvarOk`'s shape at a chain instead of at an object.
-/

/-- **What one `supers` row obliges** (L211). Stated over the **pair** (a class *name*
    and a chain) rather than over one class, which is what avoids needing `ClassOk`'s
    uniqueness clause: uniqueness covers `readableClasses`, and every `super` in the
    slice is in a *program* class, which is exactly the population it does not cover.

    Only the **builtin** arm is here. A user arm is `EntryOk`'s disjunction at a frame
    push (`ResolvesUser` plus `UserConforms`), and it is deliberately not in this
    commit: with the builtin arm alone the table's rows are unsatisfiable for a program
    method, so `preludeDecls` declares none and the rule's front end reports a **needed
    declaration** — §5's reading of an unsatisfiable requirement (`Regexp`, L106)
    applies verbatim. What that buys is the rule and its consecution case landing before
    the harder witness, rather than after. -/
def SuperOk (h : Heap) (c mname : String) (d : MethodDecl) : Prop :=
  ∀ k dm, (h.classPayload? dm).isSome → className h dm = c → dm ∈ ancestors h k →
    ∃ owner md bid, superFound h k dm mname = some (owner, md) ∧
      md.builtin = some bid ∧ ConformsAt (.cls c) mname bid d

/-- `superFound` is a `firstM` over a chain-derived list and a per-class table read,
    so it is congruent under anything that pins `classPayload?` at every id — which is
    both `PlainGrow` and `defineMethod`-of-a-different-name. Stated over the *list*
    rather than over the chain so the two callers can supply their own chain equality. -/
theorem superFound_congr {h h' : Heap} {k dm : ObjId} {mname : String}
    (hp : ∀ j, (h'.classPayload? j).map (fun c => c.methods.find? (·.1 == mname))
              = (h.classPayload? j).map (fun c => c.methods.find? (·.1 == mname)))
    (hanc : ancestors h' k = ancestors h k) :
    superFound h' k dm mname = superFound h k dm mname := by
  unfold superFound
  rw [hanc]
  induction (((ancestors h k).dropWhile (· != dm)).drop 1) with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.firstM, Option.orElse_eq_orElse]
    have := hp a
    cases h1 : h'.classPayload? a with
    | none =>
      cases h2 : h.classPayload? a with
      | none => simp [h1, h2, ih]
      | some cp => rw [h1, h2] at this; exact absurd this (by simp)
    | some cp' =>
      cases h2 : h.classPayload? a with
      | none => rw [h1, h2] at this; exact absurd this (by simp)
      | some cp =>
        rw [h1, h2] at this
        simp only [Option.map_some, Option.some.injEq] at this
        simp only [h1, h2, this]
        cases hf : cp.methods.find? (·.1 == mname) <;> simp [hf, ih]

/-- **`SuperOk` across an allocation.** Every clause is a `PlainGrow` field:
    `classPayload?` at every id, `className`, and the chain (with saturation).
    `ConformsAt` mentions no heap (L146), so the conformance half passes straight
    through. -/
theorem superOk_grow {h h' : Heap} {c n : String} {d : MethodDecl} (hg : PlainGrow h h')
    (hsat : Saturated h) (hs : SuperOk h c n d) : SuperOk h' c n d := by
  intro k dm hdm hcn hmem
  rw [hg.payload] at hdm
  rw [hg.className_eq] at hcn
  rw [hg.ancestors_eq hsat] at hmem
  obtain ⟨owner, md, bid, hf, hb, hconf⟩ := hs k dm hdm hcn hmem
  exact ⟨owner, md, bid,
    by rw [superFound_congr (fun j => by rw [hg.payload]) (hg.ancestors_eq hsat k)]; exact hf,
    hb, hconf⟩

/-- **And across a `def` of a different name.** The side condition is the one
    `ResolvesUser_defineMethod` needs and for the same reason: a write to an existing
    method table can *displace* the target of a `super`, which is why `declaresName`
    now scans the `supers` table's method names as well as `rows`'. -/
theorem superOk_defineMethod {h : Heap} {c n : String} {d : MethodDecl} {cls : ObjId}
    {name : String} {md' : MethodDef} (hs : SuperOk h c n d) (hne : ¬ (n = name)) :
    SuperOk (defineMethod h cls name md') c n d := by
  intro k dm hdm hcn hmem
  rw [classPayload?_isSome_defineMethod] at hdm
  rw [className_defineMethod] at hcn
  rw [ancestors_defineMethod] at hmem
  obtain ⟨owner, md, bid, hf, hb, hconf⟩ := hs k dm hdm hcn hmem
  refine ⟨owner, md, bid, ?_, hb, hconf⟩
  rw [superFound_congr (fun j => methods_find_defineMethod h cls j name n md' hne)
    (ancestors_defineMethod h cls k name md')]
  exact hf

/-- **The refinement invariant.** Note what is *not* here: no clause about names
    the table does not declare, and no upper bound on the heap's method table.
    That absence is the whole content of D10. -/
def DeclsOk (D : Decls) (h : Heap) : Prop :=
  MethodRowsOk D h ∧
  -- L195: the constant table's half. `Inv` already ∃-quantifies `D`, so putting the
  -- obligation here rather than in `ClassOk` is what lets a *prelude-only* name be
  -- declared at all — the boot-safe table and the prelude-aware one are then two
  -- tables, each sound at the heap it describes, rather than one global list that has
  -- to be true everywhere.
  (∀ n τ, constTy? D n = some τ → ConstOk h n τ) ∧
  -- L196's third half. Same reason as the second: `Inv` ∃-quantifies the table, so a
  -- table-indexed heap claim belongs here rather than in a new conjunct.
  (∀ c x τ, ivarTy? D c x = some τ → IvarOk h c x τ) ∧
  -- L205's fourth half, for the third's reason.
  (∀ c n τ, scopedConstTy? D c n = some τ → ScopedConstOk h c n τ) ∧
  -- L211's fifth half, for the fourth's reason.
  (∀ c n d, superDecl? D c n = some d → SuperOk h c n d)

/-! ## 2. The uniform dispatch step

What the `argsK` case of preservation needs, once per declared method instead of
once per tabulated builtin. This is `int_bin_dispatch` with the three
`Integer`-specific hypotheses replaced by `EntryOk`.
-/

theorem entry_dispatch {m : Machine} {τr : Ty} {mname : String} {d : MethodDecl}
    {recv : Value} {args : List Value} {site : SendSite}
    -- L193's two side conditions, and they are the *declaration's* rather than the
    -- receiver's: dispatch has to start somewhere, and neither `.any` nor a nilable
    -- names a class. `sigOf_atomic` supplies them from the row's existence, so no
    -- caller has to argue.
    (ha : τr ≠ .any) (hn : ∀ τ', τr ≠ .nilable τ')
    -- L239: `EntryOk.resolves`' third side condition. Every caller is at a concrete
    -- receiver type, so it is `by simp` at each.
    (hnar : ∀ σ, τr ≠ .arrayOf σ)
    (he : BuiltinEntryOk m.heap τr mname d)
    (hrv : ValueTy m.heap recv τr) (hargs : ValuesTy m.heap args d.params) :
    -- **L215: the conclusion carries the machine the builtin left**, and the four
    -- facts about it are `inv_grow_value`'s hypotheses verbatim. Every caller that used
    -- to end in `inv_value` now ends in `inv_grow_value`; a non-allocating row makes
    -- `m' = m` and the two agree.
    ∃ w m', ValueTy m'.heap w d.ret ∧ PlainGrow m.heap m'.heap ∧
      m'.frames = m.frames ∧ m'.stack = m.stack ∧ m'.kont = m.kont ∧
      m'.globals = m.globals ∧
      startArgs m recv site mname args [] .none
        = .next (withCtl m' (.value w)) := by
  obtain ⟨bid, hres, hns, hraise, -, hnew, hconf⟩ := he
  obtain ⟨owner, md, hlook, hb, hu, hvis, hpre, hbtw⟩ :=
    EntryOk.resolves ha hn hnar hres hrv
  obtain ⟨hdefer, w, m', hrun, hw, hg, hfr, hst, hko, hgv⟩ := hconf m recv args hrv hargs
  refine ⟨w, m', hw, hg, hfr, hst, hko, hgv, ?_⟩
  simp only [startArgs, finishSend]
  rw [invoke.eq_def]
  -- The receiver has to be case-split, and the reason is worth stating: `invoke`
  -- has receiver-shape special cases *before* the resolved-builtin path (a `.proc`
  -- answers `call`, a `.hsh` with a proc default answers `[]`, and a `.cls` reaches
  -- `invokeMaybeNew` or the `Math`/`Regexp` singleton arms), so an abstract
  -- receiver leaves them standing.
  --
  -- **F1a closed them by there being no inhabitant** — every one is a `.ref` and
  -- `valueTy?` had no `.ref` arm. F1b closes them by a hypothesis instead:
  -- `plainRecv` is exactly the negation of the three payload shapes, and it is part
  -- of what the class arm of `valueTy?` *means*, so the inversion hands it over
  -- (`valueTy_shapes`). The special cases are still discharged by the type
  -- judgement; what changed is that the judgement now has to say so out loud.
  -- **Five immediates since L202** — the `.flt` disjunct is `.int`'s twin here too:
  -- `invoke`'s receiver-shape arms are all `.ref`, so it falls through the outer
  -- match exactly as the other four do and costs this proof one more `inr`.
  rcases valueTy_shapes (subTy_any_false ha hn)
    -- L239: the same `subTy_atomic` argument `subTy_any_false` makes, at the array arm.
    (fun σ => by
      by_cases hq : subTy (.arrayOf σ) τr = true
      · exact absurd ((subTy_atomic ha hn).mp hq) (Ne.symm (hnar σ))
      · simpa using hq) hrv with
    ⟨a, rfl⟩ | ⟨b, rfl⟩ | rfl | ⟨sy, rfl⟩ | ⟨fx, rfl⟩ | ⟨o, rfl, hplain⟩
  case' inr.inr.inr.inr.inr =>
    -- The `.ref` case, which is F1b's whole bill. Case on the payload: `plainRecv`
    -- refutes the three special arms and the rest reach `invokeDispatch`, which is
    -- what `ResolvesTo` describes. Note this does **not** need
    -- `crubySingletonShadow`: that gate sits on `invoke`'s `md.builtin = none`
    -- branch (`Interp/Send.lean:246`) and `ResolvesTo` pins `md.builtin = some bid`,
    -- so F1a's measurement survives an abstract object receiver unchanged.
    -- **Two shapes since L185**: a plain receiver, where the three special payload
    -- arms are refuted, and a **class object**, where the payload *is* the arm
    -- `plainRecv` used to refute — so it has to be walked instead. What walks it is
    -- three refusals the judgement carries: `classRecv` excludes `Boot.regexpId`
    -- and `Boot.mathId` (the two singleton families `invoke` dispatches by
    -- receiver id, L106) and `ConformsAt` excludes `mname = "new"` (the
    -- `invokeMaybeNew` interception). With those three, `invoke` falls through to
    -- `invokeDispatch` exactly as a plain receiver does.
    rcases hplain with hplain | hclass
    · cases hpl : (m.heap.get o).payload
      -- The three special shapes, refuted by `plainRecv` rather than reasoned about.
      case proc => exact absurd hplain (by simp [plainRecv, hpl])
      case hsh => exact absurd hplain (by simp [plainRecv, hpl])
      case cls => exact absurd hplain (by simp [plainRecv, hpl])
      -- Everything else is the uniform path, and identical to the immediate cases.
      all_goals
        simp [invoke.invokeDispatch, hpl, hlook, hb, hu, hbtw, hpre, visError?, hvis,
          appendKwHash, hrun, hns, hdefer, hraise]
    · have hc := hclass
      unfold classRecv at hc
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq,
        Option.isSome_iff_exists] at hc
      obtain ⟨⟨⟨-, hrx⟩, hmt⟩, cp, hcp⟩ := hc
      have hpl : (m.heap.get o).payload = .cls cp := by
        unfold Heap.classPayload? at hcp
        cases hp : (m.heap.get o).payload <;> simp_all
      simp [invoke.invokeMaybeNew, invoke.invokeDispatch, hpl, hrx, hmt, hnew,
        hlook, hb, hu, hbtw, hpre, visError?, hvis, appendKwHash, hrun, hns, hdefer,
        hraise]
  all_goals
    simp [invoke.invokeDispatch, hlook, hb, hu, hbtw, hpre, visError?, hvis,
      appendKwHash, hrun, hns, hdefer, hraise]

/-- The activation `enterUserMethod` builds for a zero-parameter, non-closure
    method. Named rather than left to an existential because unification cannot
    find a twelve-field literal from inside a `simp`, and because the two fields
    `FrameConforms` reads are then `rfl`. -/
def userFrame (recv : Value) (md : MethodDef) (mname : String) : Frame :=
  { self := recv, locals := [], defmod := md.owner, cref := md.cref,
    blk := none, callBlk := none, kind := .method,
    meth := md.superName.getD mname, runParams := [], runFromDM := false,
    captured := none }

set_option maxHeartbeats 1000000 in
/-- **The user-method dispatch step** (L157) — `entry_dispatch`'s sibling, and the
    reason the two had to split rather than generalize.

    `entry_dispatch` concludes `.next (withCtl m (.value w))`: one step, a value,
    the machine otherwise unchanged. This concludes a **frame push** with the body
    in `ctl` and nothing in hand. Same hypothesis shape, different `StepResult`
    argument, so no common statement covers both — which is exactly what
    `HANDOFF.md` §constraint 1 predicted ("`entry_dispatch` splits in two, because
    the two branches have different step results"). -/
theorem user_dispatch {m : Machine} {cn : String} {mname : String} {md : MethodDef}
    {recv : Value} {site : SendSite}
    (hres : ResolvesUser m.heap (classOf m.heap recv) mname md)
    -- **The receiver's type is pinned to the class arm** (L185). `UserEntryOk`
    -- requires `τr = .cls c`, so every caller has this shape already — and pinning
    -- it is what keeps the class-*object* receiver out of this lemma, where the
    -- dispatch would go through `invokeMaybeNew` rather than `invokeDispatch`.
    (hrv : ValueTy m.heap recv (.cls cn)) :
    startArgs m recv site mname [] [] .none
      = .next { m with frames := m.frames.push (userFrame recv md mname),
                       stack := m.frames.size :: m.stack,
                       kont := .frameK m.frames.size :: m.kont,
                       ctl := .eval md.body } := by
  obtain ⟨owner, hlook, hb, hu, hvis, hpar, hdec, hcap, hown, hbtw⟩ := hres
  -- **Two stages, and the split is not cosmetic.** Unfolding `invoke` and
  -- `enterUserMethod` in one `simp` exhausts the heartbeat budget: the first is a
  -- nest of receiver-shape and gate `match`es, the second a hundred lines of
  -- parameter binding, and `simp` interleaves them. Reducing the dispatch to a
  -- *named call* first keeps each stage's search space small.
  -- `lookup h v m` *is* `lookupIn h (classOf h v) m` (`lookupIn`'s docstring), so
  -- this is the same equation with the definitional factoring made visible —
  -- `resolvesTo_of_resolvesAt`'s move, at the user arm.
  have hlook' : lookup m.heap recv mname = some (owner, md) := hlook
  have hinv : invoke m recv site mname [] none []
      = enterUserMethod m recv mname md [] none [] := by
    rw [invoke.eq_def]
    -- Exactly `entry_dispatch`'s receiver split, and for the same reason: `invoke`'s
    -- three receiver-shape arms are all `.ref`, and `plainRecv` refutes them. The
    -- `.cls` refutation does double duty on this branch — it is also what makes
    -- `crubySingletonShadow`, the gate `ResolvesTo` never has to mention, answer
    -- `none`.
    rcases valueTy_shapes (by simp [subTy]) (by simp [subTy]) hrv with
      ⟨a, rfl⟩ | ⟨b, rfl⟩ | rfl | ⟨sy, rfl⟩ | ⟨fx, rfl⟩ | ⟨o, rfl, -⟩
    case' inr.inr.inr.inr.inr =>
      -- L185: the receiver's type is `.cls cn`, which only `valueTy?`'s *plain*
      -- branch produces — so the disjunction `valueTy_shapes` now returns is
      -- narrowed back to `plainRecv` here rather than handled.
      have hplain : plainRecv m.heap o = true := valueTy_ref_plain hrv
      cases hpl : (m.heap.get o).payload
      case proc c => exact absurd hplain (by simp [plainRecv, hpl])
      case hsh xs => exact absurd hplain (by simp [plainRecv, hpl])
      case cls c => exact absurd hplain (by simp [plainRecv, hpl])
      all_goals
        simp [invoke.invokeDispatch, hpl, hlook', hb, hu, hbtw, hvis, visError?,
          crubySingletonShadow]
    all_goals
      simp [invoke.invokeDispatch, hlook', hb, hu, hbtw, hvis, visError?,
        crubySingletonShadow]
  simp only [startArgs, finishSend, hinv]
  simp [enterUserMethod, classifyFull, hpar, hdec, hcap, userFrame, withCtl,
    appendKwHash]

/-- **The `super` dispatch step** (L212), and it is *cheaper* than
    `entry_dispatch` for a reason worth knowing: **`doSuper` has no gates.** It goes
    straight from `found` to `md.builtin`, where `invoke` walks receiver shapes,
    `invokeMaybeNew`, visibility and the CRuby shadow table first — so there is no
    `valueTy_shapes` case split here at all, and the receiver stays abstract.

    Everything about the frame is a hypothesis, because everything about the frame is a
    `StackCtx` clause at the call site: the running name (L207/L210), the definee's name
    (L154), that it is a class (L154), and that it is on the receiver's chain (L209).
    The last one is what makes `dropWhile` land rather than empty the list — without it
    `doSuper` raises `NoMethodError`, which is exactly the type-stuck outcome. -/
theorem super_dispatch {m : Machine} {c mname : String} {d : MethodDecl}
    {args : List Value} {blk : Option Value}
    (hne : mname ≠ "")
    (hsup : SuperOk m.heap c mname d)
    (hfm : (m.frames.getD (methodFrameOf m) default).meth = mname)
    (hdp : (m.heap.classPayload? (m.frames.getD (methodFrameOf m) default).defmod).isSome)
    (hdn : className m.heap (m.frames.getD (methodFrameOf m) default).defmod = c)
    (hch : (m.frames.getD (methodFrameOf m) default).defmod ∈
      ancestors m.heap (classOf m.heap (m.frames.getD (methodFrameOf m) default).self))
    (hrv : ValueTy m.heap (m.frames.getD (methodFrameOf m) default).self (.cls c))
    (hargs : ValuesTy m.heap args d.params) :
    -- L215: `doSuper`'s builtin arm may allocate too, and the conclusion says so in
    -- `entry_dispatch`'s shape.
    ∃ w m', ValueTy m'.heap w d.ret ∧ PlainGrow m.heap m'.heap ∧
      m'.frames = m.frames ∧ m'.stack = m.stack ∧ m'.kont = m.kont ∧
      m'.globals = m.globals ∧
      doSuper m args blk = .next (withCtl m' (.value w)) := by
  obtain ⟨owner, md, bid, hf, hb, hconf⟩ := hsup _ _ hdp hdn hch
  obtain ⟨-, -, -, -, hcf⟩ := hconf
  obtain ⟨hdefer, w, m', hrun, hw, hg, hfr, hst, hko, hgv⟩ := hcf m _ args hrv hargs
  refine ⟨w, m', hw, hg, hfr, hst, hko, hgv, ?_⟩
  unfold doSuper
  simp only []
  rw [hfm, hf]
  simp only [hb, appendKwHash, hrun, beq_iff_eq, if_neg hne, List.isEmpty_nil, if_true]

/-! ## 3. Preservation: the additive step is free

The D10 claim, as a lemma. `defineMethod` of a name the declarations do not
mention leaves every declared entry alone: `lookup` is unchanged by
name-disjointness (`Proof/HeapFacts.lean`), and conformance is heap-uniform where
it has to be.
-/

/-- A declared method's name is declared. Needed to turn the *syntactic* side
    condition `declaresName D name = false` — what `infer` checks on a `def` —
    into the name-disjointness `lookup_defineMethod` wants. -/
theorem declOf?_declaresName {D : Decls} {cls name : String} {d : MethodDecl}
    (h : declOf? D cls name = some d) : declaresName D name = true := by
  unfold declOf? declsFor at h
  cases hf : D.rows.find? (·.1 == cls) with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some cd =>
    rw [hf] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨e, he, _⟩ := h
    have hp := List.find?_some he
    exact Bool.or_eq_true_iff.mpr (Or.inl (List.any_eq_true.mpr
      ⟨cd, List.mem_of_find?_eq_some hf,
        List.any_eq_true.mpr ⟨e, List.mem_of_find?_eq_some he, hp⟩⟩))

/-- **The `supers` table's half of the same fact** (L211), and it is why
    `declaresName` grew a disjunct: a `def` of a name a `supers` row is keyed on can
    displace that row's target, so the `def` rule's freshness test has to see it. -/
theorem superDecl?_declaresName {D : Decls} {cls name : String} {d : MethodDecl}
    (h : superDecl? D cls name = some d) : declaresName D name = true := by
  unfold superDecl? at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨e, he, _⟩ := h
  have hp := List.find?_some he
  refine Bool.or_eq_true_iff.mpr (Or.inr (List.any_eq_true.mpr
    ⟨e, List.mem_of_find?_eq_some he, ?_⟩))
  simp only [beq_iff_eq] at hp
  rw [hp]
  simp

/-- **Adding a row for an undeclared name carries every signature the table already
    supported** (F1b.10). The hypothesis is the `def` rule's own side condition, and
    it is doing real work: without it the new row could *displace* an existing one
    for the same name on the same class, and `declFor` would answer differently.

    Lives here rather than beside `addRow` because the *undeclared* half is
    `declOf?_declaresName`, which is a proof-side fact — and it is the only thing
    that rules the displacement out. -/
theorem subDecls_addRow {D : Decls} {cls name : String} {d : MethodDecl}
    (hfresh : declaresName D name = false) : SubDecls D (addRow D cls name d) := by
  have hkey : ∀ (c m : String) (x : MethodDecl), declOf? D c m = some x →
      declOf? (addRow D cls name d) c m = some x := by
    intro c m x hd
    have hne : ¬ (m = name) := by
      intro heq
      subst heq
      exact absurd (declOf?_declaresName hd) (by simp [hfresh])
    by_cases hc : c = cls
    · subst hc
      have hda : declsFor (addRow D c name d) c = (name, d) :: declsFor D c := by
        simp [declsFor, addRow]
      unfold declOf?
      rw [hda, List.find?_cons_of_neg (by simpa using fun hh => hne hh.symm)]
      exact hd
    · have hcne : (cls == c) = false := by simpa using fun hh => hc (Eq.symm hh)
      have hfind :
          (addRow D cls name d).rows.find? (fun x => x.1 == c) = D.rows.find? (fun x => x.1 == c) :=
        List.find?_cons_of_neg (by simp [hcne])
      have hdb : declsFor (addRow D cls name d) c = declsFor D c := by
        unfold declsFor; rw [hfind]
      unfold declOf?
      rw [hdb]
      exact hd
  -- L195/L196/L205/L211/L228: `SubDecls` is a sextuple now, and `addRow` touches `rows`
  -- only — so all five other table halves are `rfl`.
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  intro τ mname dd hdf
  unfold declFor at hdf ⊢
  cases hcs : tyClassNames τ with
  | nil => rw [hcs] at hdf; exact absurd hdf (by simp)
  | cons c cs =>
    rw [hcs] at hdf
    dsimp only at hdf ⊢
    cases hd : declOf? D c mname with
    | none => rw [hd] at hdf; exact absurd hdf (by simp)
    | some d0 =>
      simp only [hd] at hdf
      by_cases hall : (cs.all fun c' => declOf? D c' mname == some d0) = true
      · rw [if_pos hall] at hdf
        have hdd : d0 = dd := by simpa using hdf
        subst hdd
        simp only [hkey c mname _ hd]
        refine if_pos (List.all_eq_true.mpr fun c' hc' => ?_)
        have hc'' := List.all_eq_true.mp hall c' hc'
        simp only [beq_iff_eq] at hc'' ⊢
        cases hd' : declOf? D c' mname with
        | none => rw [hd'] at hc''; exact absurd hc'' (by simp)
        | some d1 => rw [hd'] at hc''; rw [hkey c' mname _ hd']; exact hc''
      · rw [if_neg hall] at hdf; exact absurd hdf (by simp)

theorem declFor_declaresName {D : Decls} {τ : Ty} {mname : String} {d : MethodDecl}
    (h : declFor D τ mname = some d) : declaresName D mname = true := by
  have key : ∀ (c : String) (cs : List String),
      (match declOf? D c mname with
       | none => none
       | some d0 =>
         if cs.all (fun c' => declOf? D c' mname == some d0) then some d0 else none)
        = some d → declaresName D mname = true := by
    intro c cs hh
    cases hd : declOf? D c mname with
    | none => rw [hd] at hh; exact absurd hh (by simp)
    | some d0 => exact declOf?_declaresName hd
  -- The class arm (F1b) is the only one that is not immediate: the key is a
  -- variable, and `tyClassNames` can answer `[]` (for a ground name), which
  -- `declFor` reads as no declaration.
  cases τ <;> (unfold declFor at h; simp only [tyClassNames] at h)
  case cls n =>
    by_cases hg : groundClassNames.contains n = true
    · rw [if_pos hg] at h; exact absurd h (by simp)
    · rw [if_neg hg] at h; exact key n [] h
  all_goals
    first
      | exact key "Integer" [] h
      | exact key "Float" [] h
      | exact key "TrueClass" ["FalseClass"] h
      | exact key "NilClass" [] h
      | exact key "Symbol" [] h
      -- L183/L184: `tyClassNames` is `[]` at the top type and at the class-object
      -- arm, so `declFor` answers `none` and the hypothesis is refuted by
      -- computing it.
      -- L238: and the parameterised arm, which is `[]` at `tyClassNames` for now —
      -- see the note there for what `["Array"]` costs.
      | exact absurd h (by simp [declFor, tyClassNames])

/-! ~~`ResolvesTo_defineMethod`~~ is **withdrawn** (L150): L147 moved its only caller
(`DeclsOk_defineMethod`) to `ResolvesAt_defineMethod`, and a receiver-shaped resolution
transport has had no consumer since. The receiver-shaped *predicate* `ResolvesTo` stays
— `entry_dispatch` reads it, via `EntryOk.resolves` — but nothing transports it. -/

/-! ~~`ResolvesTo_classOf`~~ and ~~`ResolvesTo_grow`~~ (L145) are **superseded by
L147's class indexing** and withdrawn. `ResolvesTo_classOf` said resolution factors
through `classOf`; `ResolvesAt` *is* that factoring, so the lemma became `rfl`.
`ResolvesTo_grow` transported the receiver-shaped form and needed the receiver to be
an id the old heap had — which is exactly the restriction that could not reach a fresh
object, i.e. the reason the indexing changed. `ResolvesAt_grow` below needs no such
hypothesis. -/

/-- **Resolution survives an allocating step, for every class, with no side
    condition** (L147). Every clause of `ResolvesAt` is a fact about the method
    table, the ancestor walk or the shadow gate at a *class id*, and `PlainGrow` pins
    all three at every id — so unlike the receiver-shaped version this says something
    about classes the old heap had no instances of, which is the case a producer
    creates.

    `Saturated` enters once, through `ancestors` (L144). Contrast
    `ResolvesAt_defineMethod`, whose side condition is *name* disjointness: a write to
    an existing table can displace an entry, an allocation cannot. -/
theorem ResolvesAt_grow {h h' : Heap} {k : ObjId} {mname bid : String}
    (hg : PlainGrow h h') (hsat : Saturated h)
    (hr : ResolvesAt h k mname bid) : ResolvesAt h' k mname bid := by
  obtain ⟨owner, md0, hlook, hb, hu, hvis, hpre, hbtw⟩ := hr
  refine ⟨owner, md0, ?_, hb, hu, hvis, hpre, ?_⟩
  · unfold lookupIn at hlook ⊢
    rw [hg.ancestors_eq hsat, lookup_go_grow hg]; exact hlook
  · rw [hg.ancestors_eq hsat, crubyShadow_grow hg]; exact hbtw

/-- **The user arm's growth transport** (L157). Clause for clause the same argument
    as `ResolvesAt_grow`, plus one: `(classPayload? md.owner).isSome`, which
    `PlainGrow` pins at *every* id. That extra clause is the frame's definee, and it
    is the only place the user arm reads the heap somewhere `ResolvesAt` does not. -/
theorem ResolvesUser_grow {h h' : Heap} {k : ObjId} {mname : String} {md : MethodDef}
    (hg : PlainGrow h h') (hsat : Saturated h)
    (hr : ResolvesUser h k mname md) : ResolvesUser h' k mname md := by
  obtain ⟨owner, hlook, hb, hu, hvis, hpar, hdec, hcap, hown, hbtw, hcref, hchain⟩ := hr
  refine ⟨owner, ?_, hb, hu, hvis, hpar, hdec, hcap, by rw [hg.payload]; exact hown, ?_,
    hcref, ?_⟩
  · unfold lookupIn at hlook ⊢
    rw [hg.ancestors_eq hsat, lookup_go_grow hg]; exact hlook
  · rw [hg.ancestors_eq hsat, crubyShadow_grow hg]; exact hbtw
  · -- L209: the chain itself, and `PlainGrow.ancestors_eq` is the same fact the two
    -- clauses above already spend.
    rw [hg.ancestors_eq hsat]; exact hchain

/-- **And across a `def` of a different name** — the same name-disjointness
    `ResolvesAt_defineMethod` needs, since a write to an existing table can displace
    an entry. `classPayload?_isSome_defineMethod` covers the definee clause. -/
theorem ResolvesUser_defineMethod {h : Heap} {k : ObjId} {mname : String}
    {md : MethodDef} {cls : ObjId} {name : String} {md' : MethodDef}
    (hr : ResolvesUser h k mname md) (hne : ¬ (mname = name)) :
    ResolvesUser (defineMethod h cls name md') k mname md := by
  obtain ⟨owner, hlook, hb, hu, hvis, hpar, hdec, hcap, hown, hbtw, hcref, hchain⟩ := hr
  refine ⟨owner, ?_, hb, hu, hvis, hpar, hdec, hcap,
    by rw [classPayload?_isSome_defineMethod]; exact hown, ?_, hcref, ?_⟩
  · unfold lookupIn at hlook ⊢
    rw [ancestors_defineMethod, lookup_go_defineMethod h cls name mname md' hne]
    exact hlook
  · rw [ancestors_defineMethod, crubyShadow_defineMethod]; exact hbtw
  · rw [ancestors_defineMethod]; exact hchain

/-- The `defineMethod` case, class-indexed. Same proof as the receiver-shaped one it
    replaces, with `classOf_defineMethod` no longer needed — a class id is not a
    receiver, so there is nothing to re-derive about dispatch. -/
theorem ResolvesAt_defineMethod {h : Heap} {k : ObjId} {mname bid : String}
    {cls : ObjId} {name : String} {md : MethodDef}
    (hr : ResolvesAt h k mname bid) (hne : ¬ (mname = name)) :
    ResolvesAt (defineMethod h cls name md) k mname bid := by
  obtain ⟨owner, md0, hlook, hb, hu, hvis, hpre, hbtw⟩ := hr
  refine ⟨owner, md0, ?_, hb, hu, hvis, hpre, ?_⟩
  · unfold lookupIn at hlook ⊢
    rw [ancestors_defineMethod, lookup_go_defineMethod h cls name mname md hne]
    exact hlook
  · rw [ancestors_defineMethod, crubyShadow_defineMethod]; exact hbtw

/-! ### `TyClass` transports backwards, which is the point

The clause is `∀ k, TyClass h τr k → ResolvesAt h k mname bid`, so preserving it means
reading `TyClass` in the **new** heap and needing it in the old one. That direction is
available for both steps, and for the same reason in both: `TyClass` reads only
`className` and `classPayload?`-ness, which `defineMethod` preserves exactly and a
`PlainGrow` preserves at every id — including the ids the old heap did not have, where
both answer `"Object"` and `none`.

This is where the inhabitant-indexed clause failed. `ValueTy` does **not** transport
backwards across a growing heap (L143), because a fresh object *is* a new inhabitant;
a fresh object is not a new class.
-/

theorem TyClass_defineMethod {h : Heap} {τr : Ty} {k cls : ObjId} {name : String}
    {md : MethodDef} (ht : TyClass (defineMethod h cls name md) τr k) : TyClass h τr k := by
  cases τr with
  | cls n =>
    exact ⟨by rw [← classPayload?_isSome_defineMethod h cls k name md]; exact ht.1,
      by rw [← className_defineMethod h cls k name md]; exact ht.2⟩
  -- L183: both sides are `False`, and the arm is here because the two are not
  -- *syntactically* the same `False`.
  | any => exact absurd ht (by simp [TyClass])
  -- L193, for L183's reason: `False` on both sides, but not syntactically the same
  -- `False`, so the arm is written.
  | nilable _ => exact absurd ht (by simp [TyClass])
  -- L184: the witness's payload and name transport by the two rewrites the `.cls`
  -- arm uses, and `classOf` by `classOf_defineMethod` — a method-table write moves
  -- neither `eigen` nor `klass`.
  | clsOf n =>
    obtain ⟨o, ho, hn, hk⟩ := ht
    exact ⟨o, by rw [← classPayload?_isSome_defineMethod h cls o name md]; exact ho,
      by rw [← className_defineMethod h cls o name md]; exact hn,
      by rw [hk, classOf_defineMethod]⟩
  -- L238: the same two rewrites the `.cls` arm uses — the arm *is* `.cls "Array"`'s
  -- content, so it transports identically. Stated even though `tyClassNames` is `[]`
  -- at it today, because the arm is what the iterator rung will turn on.
  | arrayOf _ =>
    exact ⟨by rw [← classPayload?_isSome_defineMethod h cls k name md]; exact ht.1,
      by rw [← className_defineMethod h cls k name md]; exact ht.2⟩
  | _ => exact ht

theorem TyClass_grow {h h' : Heap} {τr : Ty} {k : ObjId} (hg : PlainGrow h h')
    (ht : TyClass h' τr k) : TyClass h τr k := by
  cases τr with
  | cls n => exact ⟨by rw [← hg.payload k]; exact ht.1, by rw [← hg.className_eq k]; exact ht.2⟩
  | any => exact absurd ht (by simp [TyClass])
  | nilable _ => exact absurd ht (by simp [TyClass])
  | clsOf n =>
    obtain ⟨o, ho, hn, hk⟩ := ht
    -- `o` is in `h`'s bounds because `PlainGrow` says **nothing became a class**:
    -- the witness is a class in `h'`, so it was one in `h`, so it is in bounds.
    have ho' : (h.classPayload? o).isSome := by rw [← hg.payload o]; exact ho
    have hlt : o < h.objs.size := classPayload?_isSome_lt ho'
    exact ⟨o, ho', by rw [← hg.className_eq o]; exact hn,
      by rw [hk, hg.classOf_eq hlt]⟩
  | arrayOf _ =>
    exact ⟨by rw [← hg.payload k]; exact ht.1, by rw [← hg.className_eq k]; exact ht.2⟩
  | _ => exact ht

/-! ~~`ConformsAt_defineMethod`~~ is **withdrawn** (L146) rather than repaired.
`ConformsAt` no longer mentions a heap, so a heap-writing step has nothing to
re-establish about it and the lemma has no content. It is worth recording what it
*was*: the only consumer of `TypeAgree`'s backward direction — the one L143 had to
supply specially, and the one a growing step cannot supply at all. Deleting the
clause deleted the obligation. -/

/-- **The additive step preserves the invariant, with no condition beyond
    non-displacement.** D10's claim, and the reason `infer`'s `def` rule checks
    `declaresName` rather than a list of names. -/
theorem DeclsOk_defineMethod {D : Decls} {h : Heap} {cls : ObjId} {name : String}
    {md : MethodDef} (hd : DeclsOk D h) (hfresh : declaresName D name = false) :
    DeclsOk D (defineMethod h cls name md) := by
  refine ⟨?_, fun n τ hn => ?_, fun c x τ hn => ?_,
    fun c nn τ hn => scopedConstOk_defineMethod (hd.2.2.2.1 c nn τ hn),
    fun c nn dd hn => superOk_defineMethod (hd.2.2.2.2 c nn dd hn)
      (fun heq => by
        rw [heq] at hn
        exact absurd (superDecl?_declaresName hn) (by simp [hfresh]))⟩
  case refine_2 =>
    -- L195: a method-table write moves neither `constOwn` nor any field `ValueTy`
    -- reads, so the constant half is `consts_defineMethod` plus `ValueTy.congr` at
    -- `typeAgree_defineMethod` — the two lemmas L156 and L137 already wrote.
    exact constOk_defineMethod (hd.2.1 n τ hn)
  case refine_3 => exact ivarOk_defineMethod (hd.2.2.1 c x τ hn)
  intro τr mname decl hdecl
  have hne : ¬ (mname = name) := by
    intro heq
    rw [heq] at hdecl
    exact absurd (declFor_declaresName hdecl) (by simp [hfresh])
  -- `hconf` passes straight through (L146): it is a fact about `bid` and `decl`, not
  -- about this heap. What is left is resolution, and after L147 that is
  -- class-indexed — so the hypothesis read backwards is `TyClass`, not `ValueTy`.
  -- **That is what retired `TypeAgree`'s backward direction**: `TyClass` transports
  -- both ways for any step that preserves `className` and `classPayload?`-ness.
  --
  -- L157: two arms now, and the *same* argument twice. `UserConforms` mentions no
  -- heap either — it is a fact about `infer` and a body — so both conformance halves
  -- pass through and only the resolution halves transport.
  rcases hd.1 τr mname decl hdecl with ⟨bid, hres, hconf⟩ | ⟨mdu, cu, htys, hres, hnm, hconf⟩ |
    ⟨hτ, hmn, hdp, hdr, hdb, hmiss⟩
  · exact Or.inl ⟨bid,
      fun k ht => ResolvesAt_defineMethod (hres k (TyClass_defineMethod ht)) hne, hconf⟩
  · exact Or.inr (Or.inl ⟨mdu, cu, htys,
      fun k ht => ResolvesUser_defineMethod (hres k (TyClass_defineMethod ht)) hne,
      by rw [className_defineMethod]; exact hnm, hconf⟩)
  -- **L254: a miss survives an installation at a *different* name**, and
  -- `declaresName D name = false` is what makes the two names disjoint — the same
  -- argument the two arms above make, read in the other direction.
  · exact Or.inr (Or.inr ⟨hτ, hmn, hdp, hdr, hdb, fun k ht => by
      have := hmiss k (TyClass_defineMethod ht)
      unfold MissesAt lookupIn at this ⊢
      rw [ancestors_defineMethod, lookup_go_defineMethod h cls name mname md hne]
      exact this⟩)

/-- **The `def` step with a row.** F1b.10's central obligation, and the shape says
    what it costs: every row the table already had survives by name-disjointness,
    exactly as in `DeclsOk_defineMethod`, and the *new* row is discharged once.

    `hground` is what keeps the new row off the ground types. `tyClassNames` of a
    ground type is a list of ground class names, so a row on a name outside that
    list cannot change `declFor` at `.int`/`.bool`/`.nilT`/`.sym` — and a row on a
    name *inside* it would owe `EntryOk` at a type whose inhabitants are immediates,
    which is the failure `tyClassNames`' own docstring describes. The `def` rule
    discharges it by requiring the class to be in `reopenableClasses`.

    The user witnesses of the *old* rows need `infer_mono`, which is why
    `UserConforms` carries `defFree`: a body typed at `D` has to still type at
    `addRow D …`, and `infer` is not monotone in the table without it. -/
theorem DeclsOk_addRow {D : Decls} {h : Heap} {cls : ObjId} {name c : String}
    {md : MethodDef} {τb : Ty}
    (hd : DeclsOk D h) (hfresh : declaresName D name = false)
    (hground : groundClassNames.contains c = false)
    (hnew : EntryOk (addRow D c name { params := [], ret := τb })
              (defineMethod h cls name md) (.cls c) name { params := [], ret := τb }) :
    DeclsOk (addRow D c name { params := [], ret := τb }) (defineMethod h cls name md) := by
  have hsub : SubDecls D (addRow D c name { params := [], ret := τb }) :=
    subDecls_addRow hfresh
  refine ⟨?_, fun n τ hn => ?_, fun c x τ hn => ?_,
    fun c nn τ hn => scopedConstOk_defineMethod
      (hd.2.2.2.1 c nn τ (by simpa [scopedConstTy?, addRow] using hn)),
    fun c nn dd hn => by
      have hn' : superDecl? D c nn = some dd := by
        simpa [superDecl?, addRow] using hn
      exact superOk_defineMethod (hd.2.2.2.2 c nn dd hn')
        (fun heq => by
          rw [heq] at hn'
          exact absurd (superDecl?_declaresName hn') (by simp [hfresh]))⟩
  case refine_2 =>
    -- `addRow` leaves `consts` alone, so the row's obligation is the old one at the
    -- new heap — which is `DeclsOk_defineMethod`'s constant half.
    exact constOk_defineMethod (hd.2.1 n τ (by simpa [constTy?, addRow] using hn))
  case refine_3 =>
    exact ivarOk_defineMethod (hd.2.2.1 c x τ (by simpa [ivarTy?, addRow] using hn))
  intro τr mname decl hdecl
  -- Two facts about the new table at the *written* name, and everything about the
  -- new row follows from them: `c` has it, and no other class does.
  have hsome : declOf? (addRow D c name { params := [], ret := τb }) c name
      = some { params := [], ret := τb } := by
    unfold declOf? declsFor; simp [addRow]
  have hnone : ∀ c₀, ¬ (c₀ = c) →
      declOf? (addRow D c name { params := [], ret := τb }) c₀ name = none := by
    intro c₀ hne
    have hfind : (addRow D c name { params := [], ret := τb }).rows.find? (fun x => x.1 == c₀)
        = D.rows.find? (fun x => x.1 == c₀) :=
      List.find?_cons_of_neg (by simpa using fun hh => hne (Eq.symm hh))
    have heq : declOf? (addRow D c name { params := [], ret := τb }) c₀ name
        = declOf? D c₀ name := by unfold declOf? declsFor; rw [hfind]
    rw [heq]
    cases hdd : declOf? D c₀ name with
    | none => rfl
    | some dd => exact absurd (declOf?_declaresName hdd) (by simp [hfresh])
  -- Whatever type it is read at, a table with no row for `name` outside `c` gives
  -- `declFor` nothing — which is what makes the new row's obligation *one* row.
  have hgroundNone : ∀ τ0 : Ty, (∀ g ∈ tyClassNames τ0, ¬ (g = c)) →
      declFor (addRow D c name { params := [], ret := τb }) τ0 name = none := by
    intro τ0 hall
    unfold declFor
    cases hcs : tyClassNames τ0 with
    | nil => rfl
    | cons c₀ cs =>
      dsimp only
      rw [hnone c₀ (hall c₀ (by rw [hcs]; simp))]
  by_cases hmn : mname = name
  · -- The only row the new table has for `name` is the one just added, and the only
    -- type it is read at is `.cls c` — every other class's rows are untouched, and a
    -- ground type's class names cannot include `c`, which is what `hground` says.
    subst hmn
    have hgnd : ∀ g ∈ groundClassNames, ¬ (g = c) := by
      intro g hg hgc
      rw [hgc] at hg
      exact absurd hg (by simpa using hground)
    have hτ : τr = .cls c ∧ decl = { params := [], ret := τb } := by
      cases τr with
      | int =>
        exfalso
        have hn : declFor (addRow D c mname { params := [], ret := τb }) .int mname = none := by
          refine hgroundNone _ ?_
          intro g hg
          simp only [tyClassNames, List.mem_singleton] at hg
          subst hg
          exact hgnd _ (by simp [groundClassNames])
        rw [hn] at hdecl
        exact absurd hdecl (by simp)
      | bool =>
        exfalso
        have hn : declFor (addRow D c mname { params := [], ret := τb }) .bool mname = none := by
          refine hgroundNone _ ?_
          intro g hg
          have hg' : g = "TrueClass" ∨ g = "FalseClass" := by
            simpa [tyClassNames] using hg
          rcases hg' with rfl | rfl
          · exact hgnd _ (by simp [groundClassNames])
          · exact hgnd _ (by simp [groundClassNames])
        rw [hn] at hdecl
        exact absurd hdecl (by simp)
      -- L202: `.int`'s twin, and the copy is verbatim — one ground name, subtracted
      -- from the class arm by `groundClassNames`.
      | float =>
        exfalso
        have hn : declFor (addRow D c mname { params := [], ret := τb }) .float mname
            = none := by
          refine hgroundNone _ ?_
          intro g hg
          simp only [tyClassNames, List.mem_singleton] at hg
          subst hg
          exact hgnd _ (by simp [groundClassNames])
        rw [hn] at hdecl
        exact absurd hdecl (by simp)
      | nilT =>
        exfalso
        have hn : declFor (addRow D c mname { params := [], ret := τb }) .nilT mname = none := by
          refine hgroundNone _ ?_
          intro g hg
          simp only [tyClassNames, List.mem_singleton] at hg
          subst hg
          exact hgnd _ (by simp [groundClassNames])
        rw [hn] at hdecl
        exact absurd hdecl (by simp)
      -- L183: `tyClassNames .any = []`, so `declFor` is `none` outright — no
      -- ground-name argument is needed, which is the arm's whole content.
      | any =>
        exfalso
        rw [show declFor (addRow D c mname { params := [], ret := τb }) .any mname = none from
          by simp [declFor, tyClassNames]] at hdecl
        exact absurd hdecl (by simp)
      -- L193, the same argument at the nilable arm — `tyClassNames` is `[]` there too.
      | nilable τ' =>
        exfalso
        rw [show declFor (addRow D c mname { params := [], ret := τb }) (.nilable τ') mname
              = none from by simp [declFor, tyClassNames]] at hdecl
        exact absurd hdecl (by simp)
      -- L184: the same argument at the class-object arm, and for the same reason —
      -- `tyClassNames` is `[]` there, so no key is read at all.
      | clsOf n =>
        exfalso
        rw [show declFor (addRow D c mname { params := [], ret := τb }) (.clsOf n) mname
            = none from by simp [declFor, tyClassNames]] at hdecl
        exact absurd hdecl (by simp)
      -- **L238, and this arm is where `tyClassNames (.arrayOf _) = []` is spent.** With
      -- `["Array"]` the `exfalso` would be *false* — a program may reopen `class Array`
      -- and `def` into it, and then an `arrayOf` receiver resolves to the new row too, so
      -- this lemma's conclusion (`τr = .cls c`) would have to widen to a disjunction.
      -- That is the iterator rung's first bill, and it is one lemma statement.
      | arrayOf e =>
        exfalso
        rw [show declFor (addRow D c mname { params := [], ret := τb }) (.arrayOf e) mname
            = none from by simp [declFor, tyClassNames]] at hdecl
        exact absurd hdecl (by simp)
      -- L269: the same argument at the union arm — `tyClassNames` is `[]` there too.
      | union a b =>
        exfalso
        rw [show declFor (addRow D c mname { params := [], ret := τb }) (.union a b) mname
            = none from by simp [declFor, tyClassNames]] at hdecl
        exact absurd hdecl (by simp)
      | sym =>
        exfalso
        have hn : declFor (addRow D c mname { params := [], ret := τb }) .sym mname = none := by
          refine hgroundNone _ ?_
          intro g hg
          simp only [tyClassNames, List.mem_singleton] at hg
          subst hg
          exact hgnd _ (by simp [groundClassNames])
        rw [hn] at hdecl
        exact absurd hdecl (by simp)
      | cls n =>
        by_cases hng : groundClassNames.contains n = true
        · exfalso
          have hn : declFor (addRow D c mname { params := [], ret := τb }) (.cls n) mname
              = none := by
            refine hgroundNone _ ?_
            intro g hg
            simp only [tyClassNames, if_pos hng, List.not_mem_nil] at hg
          rw [hn] at hdecl
          exact absurd hdecl (by simp)
        · by_cases hnc : n = c
          · subst hnc
            refine ⟨rfl, ?_⟩
            have hn : declFor (addRow D n mname { params := [], ret := τb }) (.cls n) mname
                = some { params := [], ret := τb } := by
              simp only [declFor, tyClassNames, if_neg hng, hsome, List.all_nil, if_pos]
            rw [hn] at hdecl
            exact (Option.some.inj hdecl).symm
          · exfalso
            have hn : declFor (addRow D c mname { params := [], ret := τb }) (.cls n) mname
                = none := by
              refine hgroundNone _ ?_
              intro g hg
              simp only [tyClassNames, if_neg hng, List.mem_singleton] at hg
              rw [hg]
              exact hnc
            rw [hn] at hdecl
            exact absurd hdecl (by simp)
    obtain ⟨rfl, rfl⟩ := hτ
    exact hnew
  · -- Every other name: `declFor` is unchanged, and both arms of the old witness
    -- transport — the builtin one because it mentions no table, the user one by
    -- `infer_mono` on a `defFree` body.
    have hold : declFor D τr mname = some decl := by
      have hsame : ∀ c', declOf? (addRow D c name { params := [], ret := τb }) c' mname
          = declOf? D c' mname := by
        have _ := hsome
        intro c'
        by_cases hcc : c' = c
        · subst hcc
          have hhead : (name == mname) = false := by simpa using fun hh => hmn hh.symm
          have hda : declsFor (addRow D c' name { params := [], ret := τb }) c'
              = (name, { params := [], ret := τb }) :: declsFor D c' := by
            simp [declsFor, addRow]
          unfold declOf?
          rw [hda, List.find?_cons_of_neg (by simp [hhead])]
        · unfold declOf? declsFor
          rw [show (addRow D c name { params := [], ret := τb }).rows.find?
                  (fun x => x.1 == c') = D.rows.find? (fun x => x.1 == c') from
              List.find?_cons_of_neg (by simpa using fun hh => hcc (Eq.symm hh))]
      unfold declFor at hdecl ⊢
      cases hcs : tyClassNames τr with
      | nil => rw [hcs] at hdecl; exact absurd hdecl (by simp)
      | cons c₀ cs =>
        rw [hcs] at hdecl
        dsimp only at hdecl ⊢
        rw [hsame c₀] at hdecl
        cases hd0 : declOf? D c₀ mname with
        | none => rw [hd0] at hdecl; exact absurd hdecl (by simp)
        | some d0 =>
          rw [hd0] at hdecl
          simpa only [hsame] using hdecl
    rcases hd.1 τr mname decl hold with ⟨bid, hres, hconf⟩ |
      ⟨mdu, cu, htys, hresu, hnmu, hconfu⟩ | ⟨hτ, hmnm, hdp, hdr, hdb, hmiss⟩
    · exact Or.inl ⟨bid,
        fun k ht => ResolvesAt_defineMethod (hres k (TyClass_defineMethod ht)) hmn, hconf⟩
    · refine Or.inr (Or.inl ⟨mdu, cu, htys,
        fun k ht => ResolvesUser_defineMethod (hresu k (TyClass_defineMethod ht)) hmn,
        by rw [className_defineMethod]; exact hnmu, hconfu.1, hconfu.2.1, hconfu.2.2.1, ?_⟩)
      obtain ⟨Γ', r, τb, hb, hsb, hag⟩ := hconfu.2.2.2
      exact ⟨Γ', r, τb, infer_mono hsub hconfu.2.2.1 hb, hsb, hag⟩
    -- L254: the miss survives, by the same name-disjointness the two arms above use.
    · exact Or.inr (Or.inr ⟨hτ, hmnm, hdp, hdr, hdb, fun k ht => by
        have hm0 := hmiss k (TyClass_defineMethod ht)
        unfold MissesAt lookupIn at hm0 ⊢
        rw [ancestors_defineMethod, lookup_go_defineMethod h cls name mname md hmn]
        exact hm0⟩)

/-! ## 3b. L266 — a row added to the table at a **fixed** heap

`DeclsOk_addRow` above is the `def` step's form: the row and the method arrive
together, so its conclusion is at `defineMethod h cls name md` and its new-row
obligation is discharged by the installation. The **certificate** needs the same
fact with nothing about the heap moving — a claimed row is not installed by
anything, its witness is supplied — and that turns out to be *cheaper* rather than
harder in two places, and to need one thing `DeclsOk_addRow` did not.

* Cheaper: the two resolving arms of an old row transport by `rfl` (the heap is the
  same), so `ResolvesAt_defineMethod`/`ResolvesUser_defineMethod` are not needed;
  and `IterEntryOk`'s `MissesAt` clause likewise.
* Needed: `DeclsOk_addRow` assumes `groundClassNames.contains c = false` and
  concludes `τr = .cls c`, which is exactly what a row on `Integer` must *not* be
  refused by — `declFor` reads such a row at `Ty.int`, not at `.cls "Integer"`
  (L189's subtraction). `declFor_addRow_self_inv` below replaces the assumption with
  the true statement: whatever type the new row is read at, its class list is the
  singleton `[c]`. That covers the ground arms, the class arm, and — vacuously —
  `.bool`, whose two names cannot both be `c`.

Kept here rather than in `RubyCore/Cert/` because every one of these is a fact
about `addRow`/`declFor`/`DeclsOk`, i.e. about the existing machinery
(`docs/semantics/certificate-language.md` §7 norm 7). The `nomTy` half of the
bridge — *the singleton is `nomTy c`* — lives in `Types/Assn.lean`, where both
functions are in scope. -/

theorem declOf?_addRow_self {D : Decls} {c name : String} {σ : MethodDecl} :
    declOf? (addRow D c name σ) c name = some σ := by
  unfold declOf? declsFor; simp [addRow]

theorem declOf?_addRow_ne {D : Decls} {c name : String} {σ : MethodDecl}
    (hfresh : declaresName D name = false) :
    ∀ c₀, ¬ (c₀ = c) → declOf? (addRow D c name σ) c₀ name = none := by
  intro c₀ hne
  have hfind : (addRow D c name σ).rows.find? (fun x => x.1 == c₀)
      = D.rows.find? (fun x => x.1 == c₀) :=
    List.find?_cons_of_neg (by simpa using fun hh => hne (Eq.symm hh))
  have heq : declOf? (addRow D c name σ) c₀ name = declOf? D c₀ name := by
    unfold declOf? declsFor; rw [hfind]
  rw [heq]
  cases hdd : declOf? D c₀ name with
  | none => rfl
  | some dd => exact absurd (declOf?_declaresName hdd) (by simp [hfresh])

theorem declOf?_addRow_other {D : Decls} {c name mname : String} {σ : MethodDecl}
    (hmn : ¬ (mname = name)) :
    ∀ c', declOf? (addRow D c name σ) c' mname = declOf? D c' mname := by
  intro c'
  by_cases hcc : c' = c
  · subst hcc
    have hhead : (name == mname) = false := by simpa using fun hh => hmn hh.symm
    have hda : declsFor (addRow D c' name σ) c' = (name, σ) :: declsFor D c' := by
      simp [declsFor, addRow]
    unfold declOf?
    rw [hda, List.find?_cons_of_neg (by simp [hhead])]
  · unfold declOf? declsFor
    rw [show (addRow D c name σ).rows.find? (fun x => x.1 == c')
            = D.rows.find? (fun x => x.1 == c') from
        List.find?_cons_of_neg (by simpa using fun hh => hcc (Eq.symm hh))]

theorem declFor_addRow_other {D : Decls} {c name mname : String} {σ : MethodDecl}
    (hmn : ¬ (mname = name)) (τr : Ty) :
    declFor (addRow D c name σ) τr mname = declFor D τr mname := by
  unfold declFor
  cases hcs : tyClassNames τr with
  | nil => rfl
  | cons c₀ cs =>
    dsimp only
    rw [declOf?_addRow_other hmn c₀]
    cases hd0 : declOf? D c₀ mname with
    | none => rfl
    | some d0 => simp only [declOf?_addRow_other hmn]

/-- **The new row, read at a type whose class list is the singleton `[g]`.** -/
theorem declFor_addRow_at {D : Decls} {c name g : String} {σ : MethodDecl} {τ0 : Ty}
    (hfresh : declaresName D name = false) (h : tyClassNames τ0 = [g]) :
    declFor (addRow D c name σ) τ0 name = if g = c then some σ else none := by
  unfold declFor
  rw [h]
  dsimp only
  by_cases hg : g = c
  · subst hg
    rw [declOf?_addRow_self]
    simp
  · rw [declOf?_addRow_ne hfresh g hg]
    simp [hg]

/-- And at the **two-class** type, where it is unreadable whatever `c` is. -/
theorem declFor_addRow_bool {D : Decls} {c name : String} {σ : MethodDecl}
    (hfresh : declaresName D name = false) :
    declFor (addRow D c name σ) .bool name = none := by
  unfold declFor
  simp only [tyClassNames]
  by_cases h1 : "TrueClass" = c
  · subst h1
    rw [declOf?_addRow_self]
    dsimp only
    rw [show (List.all ["FalseClass"]
        fun c' => declOf? (addRow D "TrueClass" name σ) c' name == some σ) = false from by
      simp [declOf?_addRow_ne (D := D) (c := "TrueClass") (name := name) (σ := σ)
        hfresh "FalseClass" (by decide)]]
    simp
  · rw [declOf?_addRow_ne hfresh "TrueClass" h1]

/-- **The new row is read at exactly one type, and it is `nomTy c`.** -/
theorem declFor_addRow_self_inv {D : Decls} {c name : String} {σ : MethodDecl} {τr : Ty}
    {decl : MethodDecl} (hfresh : declaresName D name = false)
    (hdecl : declFor (addRow D c name σ) τr name = some decl) :
    tyClassNames τr = [c] ∧ decl = σ := by
  have h : ∀ g, tyClassNames τr = [g] → tyClassNames τr = [c] ∧ decl = σ := by
    intro g hg
    rw [declFor_addRow_at hfresh hg] at hdecl
    by_cases hgc : g = c
    · subst hgc
      exact ⟨hg, (Option.some.inj (by simpa using hdecl)).symm⟩
    · simp [hgc] at hdecl
  have hnil : ∀ (τ : Ty), tyClassNames τ = [] →
      declFor (addRow D c name σ) τ name = none := by
    intro τ hτ; unfold declFor; rw [hτ]
  cases τr with
  | int => exact h "Integer" rfl
  | float => exact h "Float" rfl
  | nilT => exact h "NilClass" rfl
  | sym => exact h "Symbol" rfl
  | bool => rw [declFor_addRow_bool hfresh] at hdecl; exact absurd hdecl (by simp)
  | any => rw [hnil _ (by simp [tyClassNames])] at hdecl; exact absurd hdecl (by simp)
  | clsOf _ => rw [hnil _ (by simp [tyClassNames])] at hdecl; exact absurd hdecl (by simp)
  | nilable _ => rw [hnil _ (by simp [tyClassNames])] at hdecl; exact absurd hdecl (by simp)
  | arrayOf _ => rw [hnil _ (by simp [tyClassNames])] at hdecl; exact absurd hdecl (by simp)
  | union _ _ => rw [hnil _ (by simp [tyClassNames])] at hdecl; exact absurd hdecl (by simp)
  | cls n =>
    by_cases hng : groundClassNames.contains n = true
    · rw [hnil _ (by simp only [tyClassNames]; rw [if_pos hng])] at hdecl
      exact absurd hdecl (by simp)
    · exact h n (by simp only [tyClassNames]; rw [if_neg hng])

/-- **A row added to the table at a *fixed* heap.** `DeclsOk_addRow` is this at the
    heap a `def` step produced; this is the certificate's form, where nothing about the
    heap moves and the new row's witness is supplied rather than installed. -/
theorem DeclsOk_addRow_here {D : Decls} {h : Heap} {c name : String} {σ : MethodDecl}
    (hd : DeclsOk D h) (hfresh : declaresName D name = false)
    (hnew : ∀ τ0, tyClassNames τ0 = [c] → EntryOk (addRow D c name σ) h τ0 name σ) :
    DeclsOk (addRow D c name σ) h := by
  have hsub : SubDecls D (addRow D c name σ) := subDecls_addRow hfresh
  refine ⟨?_,
    fun n τ hn => hd.2.1 n τ (by simpa [constTy?, addRow] using hn),
    fun c0 x τ hn => hd.2.2.1 c0 x τ (by simpa [ivarTy?, addRow] using hn),
    fun c0 nn τ hn => hd.2.2.2.1 c0 nn τ (by simpa [scopedConstTy?, addRow] using hn),
    fun c0 nn dd hn => hd.2.2.2.2 c0 nn dd (by simpa [superDecl?, addRow] using hn)⟩
  intro τr mname decl hdecl
  by_cases hmn : mname = name
  · subst hmn
    obtain ⟨hk, rfl⟩ := declFor_addRow_self_inv hfresh hdecl
    exact hnew τr hk
  · have hold : declFor D τr mname = some decl := by
      rw [← declFor_addRow_other (D := D) (c := c) (σ := σ) hmn τr]; exact hdecl
    rcases hd.1 τr mname decl hold with hb | ⟨mdu, cu, htys, hresu, hnmu, hconfu⟩ | hi
    · exact Or.inl hb
    · refine Or.inr (Or.inl ⟨mdu, cu, htys, hresu, hnmu,
        hconfu.1, hconfu.2.1, hconfu.2.2.1, ?_⟩)
      obtain ⟨Γ', r, τb, hbo, hsb, hag⟩ := hconfu.2.2.2
      exact ⟨Γ', r, τb, infer_mono hsub hconfu.2.2.1 hbo, hsb, hag⟩
    · exact Or.inr (Or.inr hi)

/-! ## 3c. L267 — `EntryOk` is monotone in the table, and `DeclsOk` transfers along `SubDecls`

L266 gives *a row added at a fixed heap*, one row at a time. A **certificate** adds
several (`Cert.table` folds `addRow` over its claims), and doing that one row at a
time is the wrong induction: the new row's obligation has to be discharged at the
table the certificate *ends* at, because that is the table the `decl` atom in
`assumes` is denoted against, and `EntryOk` is not antitone — a `UserEntryOk` witness
at a bigger table does not give one at a smaller (`infer_mono` runs the other way).

So the induction is over `declFor` at the final table instead, and these two lemmas
are what it needs. Both are facts about the existing machinery, neither has anything
to do with certificates, and `DeclsOk_of_subDecls` in particular is the general form
of the second half of every `DeclsOk_*` lemma above: *the old rows survive because
`infer` is monotone; only the new ones owe anything.* -/

theorem EntryOk_mono {D D' : Decls} {h : Heap} {τ : Ty} {n : String} {d : MethodDecl}
    (hs : SubDecls D D') (he : EntryOk D h τ n d) : EntryOk D' h τ n d := by
  rcases he with hb | ⟨mdu, cu, htys, hres, hnm, hconf⟩ | hi
  · exact Or.inl hb
  · refine Or.inr (Or.inl ⟨mdu, cu, htys, hres, hnm,
      hconf.1, hconf.2.1, hconf.2.2.1, ?_⟩)
    obtain ⟨Γ', r, τb, hbo, hsb, hag⟩ := hconf.2.2.2
    exact ⟨Γ', r, τb, infer_mono hs hconf.2.2.1 hbo, hsb, hag⟩
  · exact Or.inr (Or.inr hi)

theorem DeclsOk_of_subDecls {D D' : Decls} {h : Heap} (hd : DeclsOk D h)
    (hs : SubDecls D D')
    (hnew : ∀ τ n d, declFor D τ n = none → declFor D' τ n = some d → EntryOk D' h τ n d) :
    DeclsOk D' h := by
  refine ⟨fun τ n d hdf => ?_,
    fun n τ hn => hd.2.1 n τ (by rw [← hs.constTy_eq]; exact hn),
    fun c x τ hn => hd.2.2.1 c x τ (by rw [← hs.ivarTy_eq]; exact hn),
    fun c n τ hn => hd.2.2.2.1 c n τ (by rw [← hs.scopedConstTy_eq]; exact hn),
    fun c n dd hn => hd.2.2.2.2 c n dd (by rw [← hs.superDecl_eq]; exact hn)⟩
  cases hold : declFor D τ n with
  | none => exact hnew τ n d hold hdf
  | some d0 =>
    have heq := hs.1 τ n d0 hold
    rw [hdf] at heq
    have : d0 = d := (Option.some.inj heq).symm
    subst this
    exact EntryOk_mono hs (hd.1 τ n d0 hold)

/-- **The invariant survives an allocating step, unconditionally** (L147).

    L146 proved this with a side condition — *every receiver the new heap types was
    already typed by some receiver of the same dispatch class* — which was the honest
    form of an inhabitant-indexed clause and would have become real work the moment a
    user class had a declared row. L147's class indexing removes it: `TyClass`
    transports backwards (`TyClass_grow`), `ResolvesAt` forwards
    (`ResolvesAt_grow`), and conformance mentions no heap at all (L146). There is
    nothing left to assume.

    ~~`DeclsOk_grow_ground`~~ and ~~`declsOk_baseDecls_grow`~~ (L146) are withdrawn
    with the side condition they discharged. Their content was *"the base table
    declares nothing at a class type, so the fresh object inhabits nothing declared"*
    — true, still true, and no longer load-bearing. That is the good kind of
    withdrawal: the theorem got stronger, so its scaffolding stopped being needed.

    What a producer still owes is not here: it is the **step**, i.e. that the rule
    really does produce a `PlainGrow`-related machine, and `Saturated` for the heap it
    starts from (`saturatedB`, checked by `check-proofs.sh`). -/
theorem DeclsOk_grow {D : Decls} {h h' : Heap} (hg : PlainGrow h h') (hsat : Saturated h)
    (hd : DeclsOk D h) : DeclsOk D h' := by
  refine ⟨?_, fun n τ hn => constOk_grow hg hsat (hd.2.1 n τ hn),
    fun c x τ hn => ivarOk_grow hg hsat (hd.2.2.1 c x τ hn),
    fun c nn τ hn => scopedConstOk_grow hg hsat (hd.2.2.2.1 c nn τ hn),
    fun c nn dd hn => superOk_grow hg hsat (hd.2.2.2.2 c nn dd hn)⟩
  intro τr mname decl hdecl
  rcases hd.1 τr mname decl hdecl with ⟨bid, hres, hconf⟩ | ⟨mdu, cu, htys, hres, hnm, hconf⟩ |
    ⟨hτ, hmn, hdp, hdr, hdb, hmiss⟩
  · exact Or.inl ⟨bid,
      fun k ht => ResolvesAt_grow hg hsat (hres k (TyClass_grow hg ht)), hconf⟩
  · exact Or.inr (Or.inl ⟨mdu, cu, htys,
      fun k ht => ResolvesUser_grow hg hsat (hres k (TyClass_grow hg ht)),
      by rw [hg.className_eq]; exact hnm, hconf⟩)
  -- **L254: an allocation cannot install a method**, so a miss survives with no side
  -- condition at all — the contrast `ResolvesAt_grow`'s docstring already draws, in the
  -- other direction.
  · exact Or.inr (Or.inr ⟨hτ, hmn, hdp, hdr, hdb, fun k ht => by
      have hm0 := hmiss k (TyClass_grow hg ht)
      unfold MissesAt lookupIn at hm0 ⊢
      rw [hg.ancestors_eq hsat, lookup_go_grow hg]
      exact hm0⟩)

/-! ## 4. The bridge from `TableOk`

`TableOk` stays exactly as it was, because F0's two theorems and the runtime
certificate (`heapOkB`, `scripts/heapok_probe.lean`) are stated over it. What
changes is that it is no longer what the invariant carries: it is the *concrete
witness* for `baseDecls`, and this section is the derivation.
-/

/-- Every entry of `baseDecls` still resolves in this heap, spelled out at the
    three concrete names. A *heap* condition, so preservation must re-establish
    it.

    **This is no longer what the invariant carries** (F1a): `DeclsOk` is, and this
    is its concrete witness for `baseDecls` via `tableOk_declsOk`. It is kept
    exactly as it was because it is the *certificate-shaped* form — `HeapCert.lean`
    reflects it into a `Bool`, `scripts/heapok_probe.lean` reports it per clause,
    and `check-proofs.sh` fails if it stops holding at the booted heap. Moved here
    from `Proof/Static/Konts.lean` with the rest of the heap conditions, since the
    file that defines the refinement invariant is where its instances belong. -/
def TableOk (h : Heap) : Prop :=
  IntBuiltinResolves h "+" "Integer#+" ∧
  IntBuiltinResolves h "-" "Integer#-" ∧
  IntBuiltinResolves h "*" "Integer#*" ∧
  -- L152's nullary row. `IntBuiltinResolves` is arity-agnostic — it is a fact about
  -- the method table, not about the call — so the fourth clause is the same shape as
  -- the first three and `intResolvesB` decides it unchanged.
  IntBuiltinResolves h "zero?" "Integer#zero?"

/-- **No `def` hook is installed on any class** (generalized in L153).

    `Interp.lean:2625` fires `Module#method_added` on the defining module right after
    installing a method, and the hook body is arbitrary Ruby we cannot type — so the
    fragment has to exclude it rather than reason about it.

    It is excludable because the prelude installs the hook **lazily**: the
    `Object.define_singleton_method(:method_added)` in `T.__toplevel_sig`
    (`prelude/prelude.rb:1187`) runs only when a toplevel `sig` is evaluated. A
    sig-free program therefore never has one, and `lookup` simply misses [V —
    `rfl` on the boot heap, and measured over all 105 ids at the prelude-booted one].

    **Quantified over class objects as receivers, and the indexing is the content.**
    L149's version fixed the receiver at `Boot.objectId`, which is all a fragment with
    no `class` can ever define into; a class body's `def` installs on the class it is
    inside, so the clause has to hold at *every* possible definee. Two ways to say
    that, and **only one of them is true**:

    * `∀ k, (classPayload? k).isSome → lookup h (.ref k) "method_added" = none` —
      the hook lookup `evalExpr` actually performs, which walks
      `ancestors (classOf h (.ref k))`, i.e. the class object's **eigenclass** chain.
      **True**, at 0 of 105 ids.
    * `∀ k, (classPayload? k).isSome → lookupIn h k "method_added" = none` — the
      class-*indexed* walk, over `k`'s own instance chain. **False**: `T::Sig`
      defines `method_added` as an instance method, because that is how
      `sorbet-runtime` installs a sig (D9/D10, and `T.__wrap`'s comment says so).

    So this is L147's lesson with the answer the other way round — the content depends
    on the *receiver*, not on the class-indexed walk — and `T::Sig` is the witness that
    picking by analogy rather than by measurement would have produced a false clause.

    The first conjunct **replaces** L149's `Boot.objectId < h.objs.size` with a
    strictly stronger fact at the same price: it is what lets the `def` case
    *instantiate* the quantifier at the definee a toplevel `def` uses. Being a class
    implies being in bounds (`classPayload?_isSome_lt`), so the bound is subsumed —
    the same put-the-condition-in-the-judgement trade, measured for the fifth time.

    A pure *heap* fact, with the frame's definee carried by `FrameConforms` instead —
    phrasing it at the current frame's `defmod` makes it unprovable across `frameK`,
    which resumes a different frame. -/
def NoHook (h : Heap) : Prop :=
  (h.classPayload? Boot.objectId).isSome ∧
    ∀ k, (h.classPayload? k).isSome → lookup h (.ref k) "method_added" = none

/-- **`NoHook` survives an allocating step** (L149, restated at L153's indexing).

    Simpler than L149's version, and the reason is the indexing: `PlainGrow` pins
    `classPayload?` at **every** id, so the set of class objects is unchanged and
    there is no fresh-id case to discharge at all. L149 needed an explicit
    `Boot.objectId < h.objs.size` to rule out the pathological case where `Object` is
    the id being allocated; here `classPayload?_isSome_lt` supplies the bound from the
    quantifier's own hypothesis. -/
theorem NoHook_grow {h h' : Heap} (hg : PlainGrow h h') (hsat : Saturated h)
    (hh : NoHook h) : NoHook h' := by
  refine ⟨by rw [hg.payload]; exact hh.1, fun k hk => ?_⟩
  have hk' : (h.classPayload? k).isSome := by rw [← hg.payload k]; exact hk
  rw [lookup_grow hg hsat (fun o hEq => by cases hEq; exact classPayload?_isSome_lt hk')]
  exact hh.2 k hk'

/-- **And a `def`** (L153). The receiver's dispatch class is unchanged
    (`classOf_defineMethod`) and the name differs, so `lookup_defineMethod` applies at
    every class object — the same argument L149's Object-only version made, now made
    once per definee rather than once. -/
theorem NoHook_defineMethod {h : Heap} {cls : ObjId} {name : String} {md : MethodDef}
    (hh : NoHook h) (hne : ¬ ("method_added" = name)) :
    NoHook (defineMethod h cls name md) := by
  refine ⟨by rw [classPayload?_isSome_defineMethod]; exact hh.1, fun k hk => ?_⟩
  have hk' : (h.classPayload? k).isSome := by
    rw [← classPayload?_isSome_defineMethod h cls k name md]; exact hk
  rw [lookup_defineMethod _ _ name "method_added" md _ hne
    (classOf_defineMethod _ _ _ _ _)]
  exact hh.2 k hk'

/-- `noHookB` reflects `NoHook` (L153). The out-of-range ids are the only interesting
    step: `classPayload?` answers `none` there, so the clause holds vacuously and the
    bounded `all` really does decide an unbounded `∀`. -/
theorem noHookB_sound {h : Heap} (hb : noHookB h = true) : NoHook h := by
  unfold noHookB at hb
  simp only [Bool.and_eq_true] at hb
  obtain ⟨hobj, hb⟩ := hb
  refine ⟨hobj, fun k hk => ?_⟩
  by_cases hlt : k < h.objs.size
  · have := List.all_eq_true.mp hb k (List.mem_range.mpr hlt)
    simp only [Bool.or_eq_true, Option.isNone_iff_eq_none] at this
    rcases this with h1 | h2
    · exact absurd hk (by rw [h1]; simp)
    · exact h2
  · exact absurd hk (by rw [classPayload?_oob h k hlt]; simp)

/-- **The boot `String` id is a class named `"String"`** (L151), and it is the
    fourth heap conjunct for the same reason the other three are conjuncts rather
    than theorems: nothing in the `Heap` *type* forbids a heap where it is false,
    and no step a program can take makes it false.

    It exists because `infer` types a string literal `.cls "String"` — a claim about
    a **name** — while the step allocates an object whose class is the **id**
    `Boot.stringId`. Something has to join the two, and the invariant is where it
    is cheapest: the alternative is for the producer's consecution case to re-derive
    it at the use site, which is the trade L142/L143/L147/L149 each priced and each
    resolved the same way.

    Both halves are needed and neither implies the other: `className` answers
    `"Object"` at an id that is not a class, so the name clause alone would be
    satisfied by an *absent* `String`, and `plainRecv` separately requires the
    allocated object's class to *be* a class. -/
def LitClsOk (h : Heap) : Prop :=
  ((h.classPayload? Boot.stringId).isSome ∧ className h Boot.stringId = "String") ∧
    ((h.classPayload? Boot.arrayId).isSome ∧ className h Boot.arrayId = "Array")

/-- **`LitClsOk` survives an allocating step**, and unlike `NoHook_grow` it needs
    neither a bound nor saturation: `PlainGrow` pins `classPayload?` at *every* id
    (that is exactly what the non-class restriction buys, `lookup_go_grow`'s note)
    and `className` is a function of it. -/
theorem LitClsOk_grow {h h' : Heap} (hg : PlainGrow h h') (hs : LitClsOk h) :
    LitClsOk h' :=
  ⟨⟨by rw [hg.payload]; exact hs.1.1, by rw [hg.className_eq]; exact hs.1.2⟩,
   ⟨by rw [hg.payload]; exact hs.2.1, by rw [hg.className_eq]; exact hs.2.2⟩⟩

/-- **And a `def`**, from the same two facts `TyClass_defineMethod` uses. A
    `defineMethod` at `Boot.stringId` itself rewrites the payload, but
    `setClassPayload` changes the method table and nothing else, so the class stays
    a class and keeps its name. -/
theorem LitClsOk_defineMethod {h : Heap} {cls : ObjId} {name : String}
    {md : MethodDef} (hs : LitClsOk h) : LitClsOk (defineMethod h cls name md) :=
  ⟨⟨by rw [classPayload?_isSome_defineMethod h cls Boot.stringId name md]; exact hs.1.1,
    by rw [className_defineMethod h cls Boot.stringId name md]; exact hs.1.2⟩,
   ⟨by rw [classPayload?_isSome_defineMethod h cls Boot.arrayId name md]; exact hs.2.1,
    by rw [className_defineMethod h cls Boot.arrayId name md]; exact hs.2.2⟩⟩

/-! ### The reopen promise

`ClassOk` is `Inv`'s **fifth** heap conjunct (L156) and the first that is indexed
by something the *program* chooses rather than by a boot id. It is the D10-shaped
program-indexed clause `HANDOFF.md` §What is left item 4 asked for, in the only
form that is preserved: not *absent or a class* — "absent" is falsified by the
very step that would need it — but **present and a non-module class**, which every
step in the fragment leaves alone.
-/

/-- **Nothing strictly in front of `Object` on `k`'s ancestor chain owns a
    constant** — and `Object` is on the chain at all (L178).

    This is the clause `scripts/consts_probe.lean` measured (L177), and it is
    stated over the **reach** rather than over the heap because the obvious
    version is *false*: five names are owned by both `Object` and `T` at the
    prelude-booted heap (`Struct`, `Enumerable`, `Range`, `Hash`, `Array`), so
    *no class other than `Object` owns this name* would be unprovable rather
    than merely strong. The population this quantifies over is
    `{String, Comparable}` and it owns **0** constants.

    Why it is what a name-keyed constant table needs: a constant *read* is
    artifact 03 §4's two phases — lexical over the frame's `cref`, then
    inheritance over `ancestors h defmod` — so a table keyed on the name alone
    is sound only if that walk reaches the class the table is about. Both
    clauses here are one half of that: `Object` is reachable, and nothing gets
    there first. -/
def NoShadowBefore (h : Heap) (k : ObjId) : Prop :=
  Boot.objectId ∈ ancestors h k ∧
    ∀ j ∈ (ancestors h k).takeWhile (· != Boot.objectId),
      ∀ cp, h.classPayload? j = some cp → cp.consts = []

theorem noShadowBeforeB_sound {h : Heap} {k : ObjId} (hb : noShadowBeforeB h k = true) :
    NoShadowBefore h k := by
  simp only [noShadowBeforeB, Bool.and_eq_true, List.all_eq_true] at hb
  refine ⟨List.mem_of_elem_eq_true (by simpa using hb.1), fun j hj cp hcp => ?_⟩
  have := hb.2 j (by simpa using hj)
  rw [hcp] at this
  simpa using this

/-- **`NoShadowBefore` survives an allocating step.** `PlainGrow` pins
    `classPayload?` at every id and `ancestors_congr_grow` pins the walk, so both
    conjuncts transport by the same two rewrites `ClassOk`'s other clauses use. -/
theorem NoShadowBefore_grow {h h' : Heap} (hg : PlainGrow h h') (hsat : Saturated h)
    {k : ObjId} (hn : NoShadowBefore h k) : NoShadowBefore h' k := by
  obtain ⟨hmem, hno⟩ := hn
  refine ⟨by rw [ancestors_congr_grow hg.shapeAgree hg.size hsat]; exact hmem,
    fun j hj cp hcp => ?_⟩
  rw [ancestors_congr_grow hg.shapeAgree hg.size hsat] at hj
  rw [hg.payload] at hcp
  exact hno j hj cp hcp

/-- **And a `def`.** `defineMethod` writes `methods`; the walk reads `clsShape`
    and this clause reads `consts`, and `consts_defineMethod` (L156) is exactly the
    lemma that says the second is untouched — including at the definee itself,
    which is the case that makes it worth having. -/
theorem NoShadowBefore_defineMethod {h : Heap} {cls k : ObjId} {name : String}
    {md : MethodDef} (hn : NoShadowBefore h k) :
    NoShadowBefore (defineMethod h cls name md) k := by
  obtain ⟨hmem, hno⟩ := hn
  refine ⟨by rw [ancestors_defineMethod]; exact hmem, fun j hj cp hcp => ?_⟩
  rw [ancestors_defineMethod] at hj
  have hcs := consts_defineMethod h cls j name md
  rw [hcp] at hcs
  cases hp : h.classPayload? j with
  | none => rw [hp] at hcs; simp at hcs
  | some cp' =>
    rw [hp] at hcs
    simp only [Option.map_some, Option.some.injEq] at hcs
    rw [hcs]
    exact hno j hj cp' hp

/-- A class with an empty own-constant table owns nothing at any name. -/
theorem constOwn_of_no_consts {h : Heap} {k : ObjId} {n : String}
    (hn : ∀ cp, h.classPayload? k = some cp → cp.consts = []) :
    constOwn h k n = none := by
  unfold constOwn
  cases hp : h.classPayload? k with
  | none => simp [hp]
  | some cp => simp [hp, hn cp hp]

/-- **The inheritance phase reaches `Object`** (L189, on L178's clause): a `firstM`
    down a chain whose members in front of `Object` own nothing gets to `Object`, and
    `Object` answers. Stated over the raw list and at `constLookupFrom`'s own function
    body, so the ancestor walk can be handed to it without an eta rewrite. -/
theorem firstM_lookupOwn {h : Heap} {n : String} {v : Value}
    (hobj : constOwn h Boot.objectId n = some v) :
    ∀ (l : List ObjId), Boot.objectId ∈ l →
      (∀ j ∈ l.takeWhile (· != Boot.objectId), ∀ cp,
        h.classPayload? j = some cp → cp.consts = []) →
      l.firstM (fun k => match h.classPayload? k with
        | some c => (c.consts.find? (·.1 == n)).map (·.2)
        | Option.none => Option.none) = some v := by
  intro l
  induction l with
  | nil => intro hmem _; exact absurd hmem (by simp)
  | cons a rest ih =>
    intro hmem hno
    by_cases ha : a = Boot.objectId
    · subst ha
      unfold constOwn at hobj
      cases hp : h.classPayload? Boot.objectId with
      | none => rw [hp] at hobj; simp at hobj
      | some cp =>
        rw [hp] at hobj
        simp only [Option.bind_some] at hobj
        simp [List.firstM, hp, hobj]
    · have hane : (a != Boot.objectId) = true := by simpa using ha
      have hnone : (match h.classPayload? a with
          | some c => (c.consts.find? (·.1 == n)).map (·.2)
          | Option.none => Option.none) = none := by
        cases hp : h.classPayload? a with
        | none => simp [hp]
        | some cp => simp [hp, hno a (by simp [List.takeWhile, hane]) cp hp]
      have hrest : Boot.objectId ∈ rest := by
        rcases List.mem_cons.mp hmem with h' | h'
        · exact absurd h'.symm ha
        · exact h'
      have hno' : ∀ j ∈ rest.takeWhile (· != Boot.objectId), ∀ cp,
          h.classPayload? j = some cp → cp.consts = [] := by
        intro j hj cp hcp
        have hmm : j ∈ (a :: rest).takeWhile (· != Boot.objectId) := by
          simp only [List.takeWhile, hane, if_true]
          exact List.mem_cons_of_mem _ hj
        exact hno j hmm cp hcp
      simp [List.firstM, hnone, ih hrest hno']

/-- **The lexical phase can only hit `Object`** (L189). Whatever the `cref` is, either
    it misses the name or the hit is `Object`'s value — which is what makes the read
    safe over a `cref` the invariant says nothing about, and what a frame clause would
    otherwise have had to buy. -/
theorem firstM_sole_owner {h : Heap} {n : String} {v : Value}
    (hown : constOwn h Boot.objectId n = some v)
    (hsole : ∀ j, (h.classPayload? j).isSome → j ≠ Boot.objectId → constOwn h j n = none) :
    ∀ (l : List ObjId), l.firstM (fun c => constOwn h c n) = none ∨
      l.firstM (fun c => constOwn h c n) = some v := by
  intro l
  induction l with
  | nil => exact Or.inl rfl
  | cons a rest ih =>
    by_cases ha : a = Boot.objectId
    · subst ha; exact Or.inr (by simp [List.firstM, hown])
    · have hnone : constOwn h a n = none := by
        by_cases hp : (h.classPayload? a).isSome
        · exact hsole a hp ha
        · unfold constOwn
          cases hq : h.classPayload? a with
          | none => simp [hq]
          | some _ => rw [hq] at hp; exact absurd hp (by simp)
      rcases ih with h1 | h1
      · exact Or.inl (by simp [List.firstM, hnone, h1])
      · exact Or.inr (by simp [List.firstM, hnone, h1])

/-- **The whole constant read, in one equation** (L189) — and the *inheritance*
    phase is never consulted.

    `evalExpr`'s `.const` arm is the lexical phase over the frame's `cref` and then
    the ancestor walk, and two facts collapse it to `Object`'s own table: `Object` is
    **on** the cref (`StackCtx`, L189) so the lexical phase cannot miss, and `Object`
    is the **sole owner** of the name (`ClassOk`, L189) so whatever it hits is
    `Object`'s. The `orElse` is therefore dead code under the invariant, which is why
    the rule needs nothing about `ancestors` — the `NoShadowBefore` an earlier draft
    reached for is not required at all.

    **This is what a `CrefOk` clause would have bought, bought by a membership.** -/
theorem constRead_sole {h : Heap} {n : String} {v : Value} {cref : List ObjId}
    {rest : Option Value}
    (hmem : Boot.objectId ∈ cref)
    (hown : constOwn h Boot.objectId n = some v)
    (hsole : ∀ j, (h.classPayload? j).isSome → j ≠ Boot.objectId → constOwn h j n = none) :
    (cref.firstM (fun c => constOwn h c n)).orElse (fun _ => rest) = some v := by
  have hlex : cref.firstM (fun c => constOwn h c n) = some v := by
    induction cref with
    | nil => exact absurd hmem (by simp)
    | cons a tail ih =>
      by_cases ha : a = Boot.objectId
      · subst ha; simp [List.firstM, hown]
      · have hnone : constOwn h a n = none := by
          by_cases hp : (h.classPayload? a).isSome
          · exact hsole a hp ha
          · unfold constOwn
            cases hq : h.classPayload? a with
            | none => simp [hq]
            | some _ => rw [hq] at hp; exact absurd hp (by simp)
        have htail : Boot.objectId ∈ tail := by
          rcases List.mem_cons.mp hmem with h' | h'
          · exact absurd h'.symm ha
          · exact h'
        simp [List.firstM, hnone, ih htail]
  rw [hlex]; rfl

/-- **Every reopenable class name really names a reopenable class**: `Object`'s own
    constant table binds it to a class object that is not a module.

    Those are exactly the three tests `enterClassBody` applies before `pushFrame`
    (`Interp/Dispatch.lean:236–246`), and stating them as one clause is what lets
    the `class'` consecution case be a rewrite rather than a case analysis over
    branches it must then refute one at a time.

    The `isModule = false` conjunct is not redundant with being a class: a
    `ClassPayload` describes modules too, and `enterClassBody` compares the flag
    against the head keyword. A `module M` reopened as `class M` is a `TypeError`,
    which is a `.jump`, which `CtlOk` refuses — so the flag has to be pinned here
    rather than derived. -/
def ClassOk (h : Heap) : Prop :=
  -- **`Object` is named `"Object"`** (F1b.9). `BottomObj` says the outermost
  -- activation's definee is the `Object` *id*; `StackCtx` needs its *name*, because
  -- a declaration row is keyed on one. Folded in here rather than made a seventh
  -- conjunct of `Inv` because it is the same kind of fact as the rows below and
  -- `classOkB` decides it in the same pass.
  className h Boot.objectId = "Object" ∧
  -- **L178, at `Object` itself** — the other frame a constant read can happen in
  -- is the toplevel one, whose definee is `Object` (`BottomObj`). Not automatic:
  -- `ancestors` puts `prepends` first, so a module prepended to `Object` and
  -- owning a constant would shadow the toplevel table.
  NoShadowBefore h Boot.objectId ∧
  -- **Quantified over `readableClasses`, not `reopenableClasses`** (L194), and the
  -- three clauses only the *reopen* rule needs are behind an implication. The
  -- `.const` read (L189) and the `class C … end` reopen (L156) are different rules
  -- with different obligations, and until L194 they shared a table because the read
  -- was built on top of the reopen's. Splitting them is worth 7 method bodies of the
  -- slice, and it is measured rather than argued
  -- (`scripts/reopen_probe.lean` decides both clause sets per name): the read admits
  -- `T` — a *module*, so unreopenable, and the single most-read constant in the slice
  -- at 259 occurrences — and `Float`, which owns `NAN`/`INFINITY` and therefore fails
  -- `NoShadowBefore`, a clause about reading constants *from inside* the class that
  -- the read of its own name does not touch.
  --
  -- One quantified block rather than two, with the difference as an implication: two
  -- blocks would double every `ClassOk` transport (`_grow`, `_defineMethod`,
  -- `IvarOnly.classOk`), and the transports are the whole cost of this predicate.
  ∀ n ∈ readableClasses, ∃ k cp,
    constOwn h Boot.objectId n = some (.ref k) ∧
    h.classPayload? k = some cp ∧
    -- **The constant's object is a class *named* `n`** (F1b.9). Without this the
    -- class-body frame has a definee the invariant cannot name, and a declaration
    -- row — which is keyed on a name, because `infer` cannot name an `ObjId` — has
    -- nothing to attach to.
    className h k = n ∧
    -- **and it is the only one.** `TyClass h (.cls n) j` quantifies over *every*
    -- class object named `n`, so a row on `n` obliges all of them while a `def`
    -- installs on exactly one. Measured before it was assumed
    -- (`scripts/names_probe.lean`): at the prelude-booted heap no two of the 87
    -- class objects share a name at all, so the general clause is true and this
    -- restriction of it to the table's own names is what a row costs — the same
    -- shape, and the same argument, as the row above it.
    (∀ j, (h.classPayload? j).isSome → className h j = n → j = k) ∧
    -- **L189, and these two are what the `.const` *read* rule needs.**
    --
    -- First: the class object is a **legal receiver** — `classRecv` excludes the two
    -- ids `invoke` dispatches singleton families from (L185), so a name whose class
    -- object were `Regexp` or `Math` could be read but not sent to. Decidable, and it
    -- is the price of a `reopenableClasses` row exactly as the clauses above are.
    k ≠ Boot.regexpId ∧ k ≠ Boot.mathId ∧
    -- Second: **`Object` is the only class object owning a constant of this name.**
    -- That single clause replaces a `cref` clause on frames entirely, which is the
    -- rung's whole economy: `evalExpr`'s `.const` walks the frame's cref *before* the
    -- ancestors, so a name-keyed read is only sound if no cref entry can shadow — and
    -- if `Object` is the sole owner then any cref hit *is* `Object`'s, whatever the
    -- cref is. Measured before it was assumed (`scripts/consts_probe.lean`: `String`
    -- has exactly one owner, `Object`), and preserved because nothing in the fragment
    -- writes a constant anywhere else.
    (∀ j, (h.classPayload? j).isSome → j ≠ Boot.objectId → constOwn h j n = none) ∧
    -- **And the three the *reopen* rule needs on top** (L194), behind the membership
    -- that distinguishes the two tables.
    (n ∈ reopenableClasses →
      -- Not redundant with being a class: a `ClassPayload` describes modules too, and
      -- `enterClassBody` compares the flag against the head keyword. A `module M`
      -- reopened as `class M` is a `TypeError`, which is a `.jump`, which `CtlOk`
      -- refuses — so the flag has to be pinned rather than derived.
      cp.isModule = false ∧
      -- **Its ancestor chain starts at itself** (F1b.10). Not automatic: `ancestors`
      -- puts `prepends` *before* the class (`Heap.lean:506`), so a prepended module
      -- defining the same name would shadow a method the `def` step just installed —
      -- and the row's `ResolvesUser` would be false. Measured at the booted heap by
      -- `scripts/names_probe.lean` (`ancestors String = [9, 40, 1, …]`).
      (ancestors h k).head? = some k ∧
      -- **L178: the constant-table clause, at this class.** A method body of a
      -- reopenable class is one of the two frames a constant read can happen in, and
      -- `NoShadowBefore` is what makes *that* read reach `Object`'s table. This is
      -- the clause `Float` fails, and L194's split is what makes the failure cost
      -- nothing: the read of `Float`'s own name never enters a `Float` frame.
      NoShadowBefore h k)

/-- The `Bool` decides the `Prop`. Same shape as `noHookB_sound`: the certificate
    computes, the invariant quantifies, and this is the one place they meet. -/
theorem classOkB_sound {h : Heap} (hb : classOkB h = true) : ClassOk h := by
  simp only [classOkB, Bool.and_eq_true, beq_iff_eq] at hb
  refine ⟨hb.1.1, noShadowBeforeB_sound hb.1.2, ?_⟩
  intro n hn
  have := List.all_eq_true.mp hb.2 n hn
  revert this
  cases hc : constOwn h Boot.objectId n with
  | none => simp
  | some v =>
    cases v with
    | ref k =>
      cases hp : h.classPayload? k with
      | none => simp [hc, hp]
      | some cp =>
        intro hm
        simp only [hc, hp, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
          List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hm
        -- L194: the read clauses, then the sole-owner scan, then the guarded reopen
        -- triple — `classOkB`'s conjunction order, read left to right.
        obtain ⟨⟨⟨⟨hnm, huniq⟩, hrx⟩, hmt⟩, hsole⟩ := hm.1
        have hreop := hm.2
        refine ⟨k, cp, rfl, hp, hnm, fun j hj hjn => ?_,
          by simpa using hrx, by simpa using hmt, fun j hj hjo => ?_, fun hmem => ?_⟩
        -- The bound comes from the payload, exactly as `StackCtx`'s does
        -- (`classPayload?_isSome_lt`), so the `List.range` scan really is a scan
        -- over every id that can satisfy the hypothesis.
        · have hlt : j < h.objs.size := classPayload?_isSome_lt hj
          rcases huniq j (List.mem_range.mpr hlt) with hno | heq
          · have : ¬ ((h.classPayload? j).isSome = true ∧ className h j = n) := by
              simpa using hno
            exact absurd ⟨hj, hjn⟩ this
          · exact heq
        · -- L189's sole-owner clause, read out of the `List.range` scan.
          have hlt : j < h.objs.size := classPayload?_isSome_lt hj
          have hh := hsole j (List.mem_range.mpr hlt)
          rcases hh with hno | hnone
          · exact absurd (by simp [hj, hjo] : ((h.classPayload? j).isSome && j != Boot.objectId) = true)
              (by rw [hno]; simp)
          · simpa using hnone
        · -- L194's guarded triple. `hreop` is a disjunction because `classOkB` writes
          -- the guard as `!contains || …`; the membership kills the left arm.
          rcases hreop with hno | ⟨⟨hmod, hhead⟩, hns⟩
          · exact absurd (List.elem_eq_true_of_mem hmem) (by simpa using hno)
          · exact ⟨hmod, by simpa using hhead, noShadowBeforeB_sound hns⟩
    | _ => simp [hc]

/-- **`ClassOk` survives an allocating step**, and it needs nothing but
    `PlainGrow`'s third clause: `constOwn` is `classPayload?` composed with a
    lookup in `consts`, and `PlainGrow` pins `classPayload?` at *every* id. That is
    the same one-line argument `LitClsOk_grow` makes, for the same reason. -/
theorem ClassOk_grow {h h' : Heap} (hg : PlainGrow h h') (hsat : Saturated h)
    (hc : ClassOk h) : ClassOk h' := by
  refine ⟨by rw [hg.className_eq]; exact hc.1,
    NoShadowBefore_grow hg hsat hc.2.1, ?_⟩
  intro n hn
  obtain ⟨k, cp, h1, h2, h4, h5, hrx, hmt, hsole, hreop⟩ := hc.2.2 n hn
  refine ⟨k, cp, by unfold constOwn at h1 ⊢; rw [hg.payload]; exact h1,
    by rw [hg.payload]; exact h2, ?_, fun j hj hjn => ?_,
    hrx, hmt, fun j hj hjo => ?_, fun hmem => ?_⟩
  -- `PlainGrow` pins `classPayload?` at every id and `className` with it, so both
  -- new clauses transport by the same rewrite the old ones do.
  · rw [hg.className_eq]; exact h4
  · exact h5 j (by rw [← hg.payload]; exact hj) (by rw [← hg.className_eq]; exact hjn)
  · -- L189's sole-owner clause: `constOwn` reads `classPayload?`, which `PlainGrow`
    -- pins at every id, so the clause transports by the same rewrite the first one does.
    unfold constOwn at *
    rw [hg.payload]
    exact hsole j (by rw [← hg.payload]; exact hj) hjo
  · -- L194's guarded triple, transported by the two rewrites the read clauses use
    -- plus `ancestors_congr_grow` — which is why `Saturated` is a hypothesis here.
    obtain ⟨hmod, hhd, hns⟩ := hreop hmem
    exact ⟨hmod, by rw [ancestors_congr_grow hg.shapeAgree hg.size hsat]; exact hhd,
      NoShadowBefore_grow hg hsat hns⟩

/-- **And a `def`** — including a `def` in the body of the very class being
    reopened, which is the case that makes the clause worth carrying rather than
    re-deriving. `defineMethod` writes `methods`; `constOwn` and `isModule` read
    neither. -/
theorem ClassOk_defineMethod {h : Heap} {cls : ObjId} {name : String}
    {md : MethodDef} (hc : ClassOk h) : ClassOk (defineMethod h cls name md) := by
  refine ⟨by rw [className_defineMethod]; exact hc.1,
    NoShadowBefore_defineMethod hc.2.1, ?_⟩
  intro n hn
  obtain ⟨k, cp, h1, h2, h4, h5, hrx, hmt, hsole, hreop⟩ := hc.2.2 n hn
  refine ⟨k, ?_⟩
  rw [constOwn_defineMethod h cls Boot.objectId name n md]
  -- The payload at `k` may genuinely differ — this is the in-body `def` case — so
  -- the witness is the *new* payload, and what carries over is its `isModule`.
  have hsh := shape_defineMethod h cls k name md
  cases hk : (defineMethod h cls name md).classPayload? k with
  | none => rw [hk, h2] at hsh; exact absurd hsh (by simp)
  | some cp' =>
    refine ⟨cp', h1, rfl, ?_, fun j hj hjn => ?_,
      hrx, hmt, fun j hj hjo => ?_, fun hmem => ?_⟩
    -- The two F1b.9 clauses need `className` unmoved by a method-table write, which
    -- is `clsName_defineMethod` at *every* id rather than at the definee only.
    · rw [className_defineMethod]; exact h4
    · exact h5 j (by rw [← classPayload?_isSome_defineMethod]; exact hj)
        (by rw [← className_defineMethod]; exact hjn)
    · -- L189: `defineMethod` writes `methods`, and `consts_defineMethod` (L156) is
      -- the lemma that says the constant table is untouched — including at the
      -- definee, which is why it was written.
      have hcs := consts_defineMethod h cls j name md
      unfold constOwn at *
      cases hp : h.classPayload? j with
      | none =>
        rw [hp] at hcs
        cases hp' : (defineMethod h cls name md).classPayload? j with
        | none => simp [hp']
        | some cp'' => rw [hp'] at hcs; simp at hcs
      | some cpj =>
        have hj' : (h.classPayload? j).isSome := by rw [hp]; simp
        have := hsole j hj' hjo
        rw [hp] at this hcs
        cases hp' : (defineMethod h cls name md).classPayload? j with
        | none => simp [hp']
        | some cp'' =>
          rw [hp'] at hcs
          simp only [Option.map_some, Option.some.injEq] at hcs
          simp only [hp', Option.bind_some, hcs]
          simpa using this
    · -- L194's guarded triple. `isModule` is not in `clsShape`, but it *is* in
      -- `clsName_defineMethod` — L124 put it there because the anonymous-class
      -- fallback renders by it. Reused rather than reproved.
      obtain ⟨hmod, hhd, hns⟩ := hreop hmem
      refine ⟨?_, by rw [ancestors_defineMethod]; exact hhd,
        NoShadowBefore_defineMethod hns⟩
      have hnm := clsName_defineMethod h cls k name md
      rw [hk, h2] at hnm
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hnm
      rw [hnm.2]; exact hmod

/-- **`TableOk` survives a user `def`.** Still needed, because `HeapOk` — F0's
    heap half — is stated over `TableOk`, and `PreludeInv.heapOk_defineMethod` is
    its `defineMethod` case. `DeclsOk_defineMethod` is the general version of the
    same claim; this one stays because the certificate does.

    The side condition is what the fragment checks syntactically — a `def` may not
    shadow a tabulated builtin name. It holds for *any* target class `cls`, so
    reopening `Integer` itself is fine as long as the name differs. -/
theorem TableOk_defineMethod {h : Heap} {cls : ObjId} {name : String}
    {md : MethodDef} (ht : TableOk h)
    (h1 : ¬ (name = "+")) (h2 : ¬ (name = "-")) (h3 : ¬ (name = "*"))
    (h4 : ¬ (name = "zero?")) :
    TableOk (defineMethod h cls name md) :=
  ⟨IntBuiltinResolves_defineMethod ht.1 (fun hh => h1 hh.symm),
   IntBuiltinResolves_defineMethod ht.2.1 (fun hh => h2 hh.symm),
   IntBuiltinResolves_defineMethod ht.2.2.1 (fun hh => h3 hh.symm),
   IntBuiltinResolves_defineMethod ht.2.2.2 (fun hh => h4 hh.symm)⟩

/-- The `Integer` entries of `baseDecls`, from the corresponding
    `IntBuiltinResolves`. The `hrun`/`hdefer` hypotheses are the ones
    `Proof/BuiltinConformance.lean` already discharges by `rfl` and `simp`. -/
theorem entryOk_int {h : Heap} {mname bid : String} {op : Int → Int → Int}
    (hres : IntBuiltinResolves h mname bid)
    (hns : (mname == "send" || mname == "public_send" || mname == "__send__") = false)
    (hraise : bid ≠ "Object#raise") (hnew : mname ≠ "new")
    (hrun : ∀ (x y : Int) (m' : Machine),
      Builtins.run bid (.int x) [.int y] m' = .ok (.int (op x y)) m')
    (hdefer : ∀ (h' : Heap) (x y : Int),
      Builtins.deferTwin? h' bid (.int x) [.int y] = none) :
    BuiltinEntryOk h .int mname { params := [.int], ret := .int } := by
  -- L185's `mname ≠ "new"` is `hnew`, a hypothesis rather than a `decide`, because
  -- the lemma is stated at an abstract `mname`.
  refine ⟨bid, ?_, hns, hraise, rfl, hnew, ?_⟩
  · -- L147: the clause is now indexed by the dispatch class, and `TyClass h .int k`
    -- *is* `k = Boot.integerId` — so the `valueTy_int` inversion and the
    -- `lookup_int_const`/`classOf_int` rewrites all go away. `IntBuiltinResolves` is
    -- already a statement about `lookup h (.int 0)`, which is `lookupIn` at that
    -- class definitionally.
    intro k hk
    subst hk
    exact hres
  · -- L146: the conformance half is now quantified over the machine, and the proof
    -- did not move — every hypothesis it used was a `valueTy_int` inversion, which
    -- is heap-independent. That is the evidence the heap index was carrying nothing.
    intro m recv args hrv hargs
    obtain ⟨a, rfl⟩ := valueTy_int hrv
    -- `d.params = [.int]`, so `ValuesTy` pins the argument list to one integer.
    match args, hargs with
    | [b], ⟨hb, _⟩ =>
      -- L183: `ValuesTy` matches by `subTy`, and `Ty.int` is concrete, so
      -- `subTy_concrete` puts the argument back at exactly `.int` — which is the
      -- lemma that makes the weakening inert for every `baseDecls` row.
      obtain ⟨σ, hσ, hsub⟩ := hb
      obtain ⟨y, rfl⟩ := valueTy_int ((subTy_concrete (by simp) (by simp)).mp hsub ▸ hσ)
      -- L215: the witness leaves the machine alone, so it supplies `PlainGrow.rfl'`
      -- and three `rfl`s. That the generalization is *inert* for every row that does
      -- not allocate is the whole reason it can land before the rows that do.
      exact ⟨fun h' => hdefer h' a y, .int (op a y), m, hrun a y m, ValueTy.exact rfl,
        PlainGrow.rfl' _, rfl, rfl, rfl, rfl⟩

/-- **The nullary sibling of `entryOk_int`** (L152). The same three-clause shape with
    `ValuesTy` pinning the argument list to `[]` instead of to one integer — which is
    the whole difference an arity makes to the *invariant*, as against the difference
    it makes to the machine (a whole `KontOk` constructor and consecution case, because
    a zero-argument send dispatches in the `recvK` step rather than a step later).

    The return type is a parameter because a nullary builtin need not answer its own
    receiver type; `zero?` answers `.bool`. -/
theorem entryOk_int_nullary {h : Heap} {mname bid : String} {τret : Ty}
    {f : Int → Value}
    (hres : IntBuiltinResolves h mname bid)
    (hns : (mname == "send" || mname == "public_send" || mname == "__send__") = false)
    (hraise : bid ≠ "Object#raise") (hnew : mname ≠ "new")
    (hty : ∀ (hp : Heap) (x : Int), ValueTy hp (f x) τret)
    (hrun : ∀ (x : Int) (m' : Machine),
      Builtins.run bid (.int x) [] m' = .ok (f x) m')
    (hdefer : ∀ (h' : Heap) (x : Int),
      Builtins.deferTwin? h' bid (.int x) [] = none) :
    BuiltinEntryOk h .int mname { params := [], ret := τret } := by
  -- L185's `mname ≠ "new"` is `hnew`, a hypothesis rather than a `decide`, because
  -- the lemma is stated at an abstract `mname`.
  refine ⟨bid, ?_, hns, hraise, rfl, hnew, ?_⟩
  · intro k hk
    subst hk
    exact hres
  · intro m recv args hrv hargs
    obtain ⟨a, rfl⟩ := valueTy_int hrv
    match args, hargs with
    | [], _ => exact ⟨fun h' => hdefer h' a, f a, m, hrun a m, hty m.heap a,
        PlainGrow.rfl' _, rfl, rfl, rfl, rfl⟩

/-- **The base table declares nothing at a class type.** `baseDecls`'s only key is
    `"Integer"`, and `tyClassNames` subtracts the ground names from the class arm's
    range (L141) precisely so that `.cls "Integer"` — whose inhabitants are objects
    of *some* class merely named `Integer` — cannot read `Integer`'s row.

    Pulled out of `tableOk_declsOk`'s class arm in L146, where it discharged the
    side condition `DeclsOk_grow` then had. L147 removed that side condition, so this
    is back to being one refutation used once — kept split out because the class arm
    of a `declFor` computation is worth a name. -/
theorem declFor_baseDecls_cls (n mname : String) :
    declFor baseDecls (.cls n) mname = none := by
  unfold declFor
  simp only [tyClassNames]
  by_cases hg : groundClassNames.contains n = true
  · rw [if_pos hg]
  · rw [if_neg hg]
    have hne : ("Integer" == n) = false := by
      by_cases he : "Integer" = n
      · exact absurd (by subst he; simp [groundClassNames]) hg
      · simpa using he
    simp [declOf?, declsFor, baseDecls, hne]

/-- The class-object constant table, read backwards. A list induction, isolated
    because the table is a `map` and the lookup is a `find?` — the two do not compose
    by `simp` alone. -/
theorem constTy?_clsOf_inv : ∀ {ns : List String} {n : String} {τ : Ty},
    ((ns.map (fun m => (m, Ty.clsOf m))).find? (·.1 == n)).map (·.2) = some τ →
      n ∈ ns ∧ τ = .clsOf n
  | [], _, _, h => by simp at h
  | a :: as, n, τ, h => by
    simp only [List.map_cons, List.find?_cons] at h
    by_cases hae : a = n
    · subst hae
      simp only [beq_self_eq_true, if_true, Option.map_some, Option.some.injEq] at h
      exact ⟨List.mem_cons_self, h.symm⟩
    · rw [show ((a, Ty.clsOf a).1 == n) = false from by simpa using hae] at h
      simp only [Bool.false_eq_true, if_false] at h
      obtain ⟨h1, h2⟩ := constTy?_clsOf_inv h
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩

/-- **`ClassOk` read out at one `baseConsts` entry** (L195). The entry's type is
    `.clsOf n` by construction, and `ValueTy h (.ref k) (.clsOf n)` is `classRecv` plus
    the name — which is what `ClassOk`'s payload clause, its two id clauses and its
    `className` clause say between them. So this lemma is the L194 clause set,
    repackaged as a value judgement, and it is the reason the new `DeclsOk` half is
    three conjuncts rather than seven. -/
theorem constOk_of_classOk {h : Heap} {n : String} {τ : Ty} (hcls : ClassOk h)
    (hn : constTy? baseDecls n = some τ) :
    ConstOk h n τ := by
  -- The lookup pins both the membership and the type, because `baseConsts` is
  -- `readableClasses.map (fun n => (n, .clsOf n))`.
  have hmem : n ∈ readableClasses ∧ τ = .clsOf n :=
    constTy?_clsOf_inv (by
      unfold constTy? at hn
      rw [show baseDecls.consts = baseConsts from rfl, baseConsts] at hn
      exact hn)
  obtain ⟨hmem, rfl⟩ := hmem
  obtain ⟨k, cp, hco, hpay, hnm, -, hrx, hmt, hsole, -⟩ := hcls.2.2 n hmem
  have hlt : k < h.objs.size := classPayload?_isSome_lt (by rw [hpay]; simp)
  refine ⟨.ref k, hco, ValueTy.exact ?_, hsole⟩
  have hcr : classRecv h k = true := by
    unfold classRecv
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    exact ⟨⟨⟨hlt, hrx⟩, hmt⟩, by rw [hpay]; simp⟩
  have hnp : plainRecv h k = false := by
    unfold plainRecv
    unfold Heap.classPayload? at hpay
    cases hp : (h.get k).payload <;> simp_all
  simp [valueTy?, hnp, hcr, hnm]

/-- **The constant table's obligation, decided** (L195). Lives in `Proof/` rather
    than in `HeapCert.lean` — where `heapOkB` and `classOkB` live — for one reason:
    it has to call `valueTy?`, and that is `Proof/Static/Locals.lean`'s. The
    one-definition-two-readers rule then says the probe must import *this* rather
    than re-implement it, which `scripts/consts_probe.lean` does.

    Why a certificate at all, when nothing consumes it yet: `preludeDecls` is the
    table `--assn` reports against, and its `T` row is a claim about the
    prelude-booted heap that the kernel cannot check (`Lean.Json.parse` does not
    reduce, L135). A row asserted and not decided is exactly what `reopen_probe`
    exists to prevent. -/
def constsOkB (h : Heap) (cs : List (String × Ty)) : Bool :=
  cs.all fun e =>
    match constOwn h Boot.objectId e.1 with
    | none => false
    | some v =>
      (match valueTy? h v with
       | none => false
       | some σ => subTy σ e.2) &&
      (List.range h.objs.size).all fun j =>
        !((h.classPayload? j).isSome && j != Boot.objectId) || (constOwn h j e.1).isNone

theorem constsOkB_sound {h : Heap} {cs : List (String × Ty)}
    (hb : constsOkB h cs = true) : ∀ n τ, (n, τ) ∈ cs → ConstOk h n τ := by
  intro n τ hmem
  have he := List.all_eq_true.mp hb (n, τ) hmem
  revert he
  cases hc : constOwn h Boot.objectId n with
  | none => simp [hc]
  | some v =>
    intro he
    simp only [hc, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true'] at he
    refine ⟨v, hc, ?_, fun j hj hjo => ?_⟩
    · cases hv : valueTy? h v with
      | none => rw [hv] at he; exact absurd he.1 (by simp)
      | some σ =>
        rw [hv] at he
        exact Or.inr (Or.inr ⟨σ, hv, by simpa using he.1⟩)
    · -- The bound comes from the payload, so the `List.range` scan really does cover
      -- every id the hypothesis can name (`classPayload?_isSome_lt`).
      have hlt : j < h.objs.size := classPayload?_isSome_lt hj
      rcases he.2 j (List.mem_range.mpr hlt) with hno | hnone
      · exact absurd (by simp [hj, hjo] :
          ((h.classPayload? j).isSome && j != Boot.objectId) = true) (by rw [hno]; simp)
      · simpa using hnone

/-- The form the invariant reads: `constTy?` rather than membership. -/
theorem constsOk_of_constsOkB {h : Heap} {D : Decls} (hb : constsOkB h D.consts = true)
    {n : String} {τ : Ty} (hn : constTy? D n = some τ) : ConstOk h n τ := by
  refine constsOkB_sound hb n τ ?_
  unfold constTy? at hn
  cases hf : D.consts.find? (·.1 == n) with
  | none => rw [hf] at hn; exact absurd hn (by simp)
  | some e =>
    rw [hf] at hn
    simp only [Option.map_some, Option.some.injEq] at hn
    have hmem := List.mem_of_find?_eq_some hf
    have hname : e.1 = n := by
      have := List.find?_some hf
      simpa using this
    rw [show (n, τ) = e from by rw [← hname, ← hn]]
    exact hmem

/-- **The bridge, with one new hypothesis** (L195). `baseDecls.consts` is
    `readableClasses` mapped to class-object types, and `ClassOk` is exactly the
    predicate that says those names are there, at legal receivers, solely owned — so
    the constant half is `ClassOk` read out rather than anything new. The hypothesis
    is not a widening of the trust base: `ClassOk` was already a conjunct of `HeapOk`,
    which every caller of this lemma has in hand. -/
theorem tableOk_declsOk {h : Heap} (ht : TableOk h) (hcls : ClassOk h) :
    DeclsOk baseDecls h := by
  refine ⟨?_, fun n τ hn => ?_, fun c x τ hn => ?_,
    -- L205: and the fourth, empty for the third's reason and stated the same way.
    fun c nn τ hn => absurd hn (by simp [scopedConstTy?, baseDecls]),
    -- L211: and the fifth, empty for the same reason.
    fun c nn dd hn => absurd hn (by simp [superDecl?, baseDecls])⟩
  case refine_2 => exact constOk_of_classOk hcls hn
  -- `baseDecls.ivars` is empty, so the third half is vacuous — and stating it as a
  -- refutation of the lookup rather than as `trivial` is what will break here the
  -- moment a row lands, which is the point.
  case refine_3 => exact absurd hn (by simp [ivarTy?, baseDecls])
  intro τr mname d hd
  -- Only `Integer` has declarations, and only three names on it, so the table
  -- lookup either pins `mname` or refutes `hd`.
  cases τr with
  | int =>
    by_cases h1 : mname = "+"
    · subst h1
      have : d = { params := [Ty.int], ret := Ty.int } := by
        simpa [declFor, tyClassNames, declOf?, declsFor, baseDecls] using hd.symm
      subst this
      exact Or.inl <| entryOk_int ht.1 (by decide) (by decide) (by decide) run_int_add
        (fun _ _ _ => by simp [Builtins.deferTwin?, Builtins.reprDefer?,
          Builtins.coerceDefer?, Builtins.toAryDefer?, Builtins.num?])
    · by_cases h2 : mname = "-"
      · subst h2
        have : d = { params := [Ty.int], ret := Ty.int } := by
          simpa [declFor, tyClassNames, declOf?, declsFor, baseDecls] using hd.symm
        subst this
        exact Or.inl <| entryOk_int ht.2.1 (by decide) (by decide) (by decide) run_int_sub
          (fun _ _ _ => by simp [Builtins.deferTwin?, Builtins.reprDefer?,
            Builtins.coerceDefer?, Builtins.toAryDefer?, Builtins.num?])
      · by_cases h3 : mname = "*"
        · subst h3
          have : d = { params := [Ty.int], ret := Ty.int } := by
            simpa [declFor, tyClassNames, declOf?, declsFor, baseDecls] using hd.symm
          subst this
          exact Or.inl <| entryOk_int ht.2.2.1 (by decide) (by decide) (by decide) run_int_mul
            (fun _ _ _ => by simp [Builtins.deferTwin?, Builtins.reprDefer?,
              Builtins.coerceDefer?, Builtins.toAryDefer?, Builtins.num?])
        -- L152's nullary row, and the only line of this proof that differs in shape:
        -- the return type is `.bool` rather than the receiver's, so the witness has
        -- to say what a `.bool` value *is* (`hty`).
        · by_cases h4 : mname = "zero?"
          · subst h4
            have : d = { params := [], ret := Ty.bool } := by
              simpa [declFor, tyClassNames, declOf?, declsFor, baseDecls] using hd.symm
            subst this
            -- `f` is given explicitly: elaborating `hty` first would leave it an
            -- undetermined metavariable, since nothing in `ValueTy _ (f x) .bool`
            -- pins the function.
            exact Or.inl <| entryOk_int_nullary (f := fun x => .bool (x == 0))
              ht.2.2.2 (by decide) (by decide) (by decide)
              (fun _ _ => ValueTy.exact rfl) run_int_zero
              (fun _ _ => by simp [Builtins.deferTwin?, Builtins.reprDefer?,
                Builtins.coerceDefer?, Builtins.toAryDefer?])
          · exact absurd hd (by
              simp [declFor, tyClassNames, declOf?, declsFor, baseDecls,
                show ("+" == mname) = false from by simp [Ne.symm h1],
                show ("-" == mname) = false from by simp [Ne.symm h2],
                show ("*" == mname) = false from by simp [Ne.symm h3],
                show ("zero?" == mname) = false from by simp [Ne.symm h4]])
  -- L202: `baseDecls` declares nothing on `Float`, so the new ground arm is refuted
  -- by the same table computation the other three are. That it is *refutable* is the
  -- rung's whole cost in this file: a float literal types, and no send to it does.
  | float =>
    exact absurd hd (by simp [declFor, tyClassNames, declOf?, declsFor, baseDecls])
  | bool =>
    exact absurd hd (by simp [declFor, tyClassNames, declOf?, declsFor, baseDecls])
  | nilT =>
    exact absurd hd (by simp [declFor, tyClassNames, declOf?, declsFor, baseDecls])
  | sym =>
    exact absurd hd (by simp [declFor, tyClassNames, declOf?, declsFor, baseDecls])
  -- The class arm (F1b): refuted by `declFor_baseDecls_cls` below — `baseDecls` has
  -- one key, `"Integer"`, and `tyClassNames` subtracts it from the class arm's
  -- range, so a class type has no declarations in the base table by construction.
  | cls n => exact absurd hd (by rw [declFor_baseDecls_cls]; simp)
  -- L183's top type and L184's class-object arm: no class names, so no
  -- declarations, in any table.
  | any => exact absurd hd (by simp [declFor, tyClassNames])
  | clsOf n => exact absurd hd (by simp [declFor, tyClassNames])
  | nilable _ => exact absurd hd (by simp [declFor, tyClassNames])
  -- L238, and it is `.any`'s arm for `.any`'s reason today.
  | arrayOf _ => exact absurd hd (by simp [declFor, tyClassNames])
  | union _ _ => exact absurd hd (by simp [declFor, tyClassNames])

end Static

/-! ## 8. L191: transporting the invariant across an `ivars`-only write

`@x = e` is the first admitted rule whose step **writes the heap without allocating**.
`PlainGrow` is the wrong shape for it — nothing grows — and `TypeAgree` alone is not
enough, because `DeclsOk` reads the method table and `ClassOk` reads the constant
tables, neither of which `TypeAgree` mentions.

`IvarOnly` (`Proof/HeapFacts.lean`) is the right shape, and every transport below is
the same two-line proof: rewrite the heap function by its congruence and hand back
the hypothesis. That there is nothing harder here is the point of the rule — an
instance-variable table is invisible to the invariant, which is why the ivar
*write* is admissible while the ivar *read* (which needs a type for what comes
back) is not.
-/

open Static Interp Types

namespace IvarOnly

variable {h h' : Heap}

theorem crubyShadow_eq (hi : IvarOnly h h') (chain : List ObjId) (mname : String) :
    crubyShadow h' chain mname = crubyShadow h chain mname := by
  simp only [crubyShadow, hi.className_eq]

theorem lookupIn_eq (hi : IvarOnly h h') (k : ObjId) (mname : String) :
    lookupIn h' k mname = lookupIn h k mname := by
  simp only [lookupIn, hi.ancestors_eq, hi.lookup_go_eq]

theorem resolvesAt (hi : IvarOnly h h') {k : ObjId} {mname bid : String}
    (hr : ResolvesAt h k mname bid) : ResolvesAt h' k mname bid := by
  obtain ⟨owner, md, hl, hb, hu, hv, hp, hsh⟩ := hr
  exact ⟨owner, md, by rw [hi.lookupIn_eq]; exact hl, hb, hu, hv, hp,
    by rw [hi.crubyShadow_eq, hi.ancestors_eq]; exact hsh⟩

theorem resolvesUser (hi : IvarOnly h h') {k : ObjId} {mname : String} {md : MethodDef}
    (hr : ResolvesUser h k mname md) : ResolvesUser h' k mname md := by
  obtain ⟨owner, hl, hb, hu, hv, hps, hdc, hcf, hown, hsh, hcref, hchain⟩ := hr
  refine ⟨owner, by rw [hi.lookupIn_eq]; exact hl, hb, hu, hv, hps, hdc, hcf,
    by rw [hi.classPayload]; exact hown, ?_, hcref, by rw [hi.ancestors_eq]; exact hchain⟩
  rw [hi.crubyShadow_eq, hi.ancestors_eq]
  exact hsh

/-- Backwards, because `EntryOk`'s resolution clause is a hypothesis about the
    *new* heap's dispatch classes discharged from the old heap's. -/
theorem tyClass (hi : IvarOnly h h') {τ : Ty} {k : ObjId} (ht : TyClass h' τ k) :
    TyClass h τ k := by
  cases τ with
  | cls n => exact ⟨by rw [← hi.classPayload]; exact ht.1, by rw [← hi.className_eq]; exact ht.2⟩
  | clsOf n =>
    obtain ⟨o, hcp, hnm, hk⟩ := ht
    exact ⟨o, by rw [← hi.classPayload]; exact hcp, by rw [← hi.className_eq]; exact hnm,
      by rw [← hi.classOf_eq]; exact hk⟩
  | any => exact ht.elim
  | nilable _ => exact ht.elim
  -- L238: `.cls "Array"`'s content, so `.cls`'s two rewrites verbatim.
  | arrayOf _ =>
    exact ⟨by rw [← hi.classPayload]; exact ht.1, by rw [← hi.className_eq]; exact ht.2⟩
  | _ => exact ht

theorem entryOk (hi : IvarOnly h h') {D : Decls} {τr : Ty} {mname : String}
    {d : MethodDecl} (he : EntryOk D h τr mname d) : EntryOk D h' τr mname d := by
  rcases he with ⟨bid, hres, hconf⟩ | ⟨md, c, hkey, hres, hown, hconf⟩ |
    ⟨hτ, hmn, hdp, hdr, hdb, hmiss⟩
  · exact Or.inl ⟨bid, fun k hk => hi.resolvesAt (hres k (hi.tyClass hk)), hconf⟩
  · exact Or.inr (Or.inl ⟨md, c, hkey, fun k hk => hi.resolvesUser (hres k (hi.tyClass hk)),
      by rw [hi.className_eq]; exact hown, hconf⟩)
  -- L254: an ivar write moves no method table, so the miss is unmoved.
  · exact Or.inr (Or.inr ⟨hτ, hmn, hdp, hdr, hdb, fun k hk => by
      have hm0 := hmiss k (hi.tyClass hk)
      unfold MissesAt at hm0 ⊢
      rw [hi.lookupIn_eq]; exact hm0⟩)

theorem constOk (hi : IvarOnly h h') {n : String} {τ : Ty} (hc : ConstOk h n τ) :
    ConstOk h' n τ := by
  obtain ⟨v, hv, hty, hsole⟩ := hc
  refine ⟨v, by rw [hi.constOwn_eq]; exact hv,
    ValueTy.congr (typeAgree_of_fields hi.size.symm hi.klass hi.eigen hi.payload hi.frozen)
      hty, fun j hj hjo => ?_⟩
  rw [hi.constOwn_eq]
  exact hsole j (by rw [hi.classPayload] at hj; exact hj) hjo

/-- **And the scoped-constant clause** (L205), which `IvarOnly` carries for `constOk`'s
    reason: `consts` and `privateConsts` are fields of a *class payload*, and an ivar
    write moves no payload anywhere. -/
theorem scopedConstOk (hi : IvarOnly h h') {c n : String} {τ : Ty}
    (hs : ScopedConstOk h c n τ) : ScopedConstOk h' c n τ := by
  intro o ho hcn
  rw [hi.classPayload] at ho
  rw [hi.className_eq] at hcn
  obtain ⟨hpriv, v, hv, hty⟩ := hs o ho hcn
  refine ⟨?_, v, ?_, ValueTy.congr
    (typeAgree_of_fields hi.size.symm hi.klass hi.eigen hi.payload hi.frozen) hty⟩
  · rw [hi.ancestors_eq]
    simp only [hi.classPayload]
    exact hpriv
  · rw [constLookupFrom_congr (fun j => by rw [hi.classPayload]) (hi.ancestors_eq o)]
    exact hv

/-- **`SuperOk` across an ivar write** (L211). `IvarOnly` pins every `classPayload?`,
    so both the chain and the per-class method table are unmoved, and `ConformsAt`
    mentions no heap. -/
theorem superOk (hi : IvarOnly h h') {c n : String} {d : MethodDecl}
    (hs : SuperOk h c n d) : SuperOk h' c n d := by
  intro k dm hdm hcn hmem
  rw [hi.classPayload] at hdm
  rw [hi.className_eq] at hcn
  rw [hi.ancestors_eq] at hmem
  obtain ⟨owner, md, bid, hf, hb, hconf⟩ := hs k dm hdm hcn hmem
  exact ⟨owner, md, bid,
    by rw [superFound_congr (fun j => by rw [hi.classPayload]) (hi.ancestors_eq k)];
       exact hf,
    hb, hconf⟩

/-- **Only three of the four halves** (L196, L205), and the omission is the rung:
    `IvarOnly` says an ivar write is invisible, and `DeclsOk`'s *ivar* half is the one
    that is *about* ivars. The `@x = e` consecution case has to re-establish that half
    from the rule's own conformance check, which is why the rule has one. -/
theorem rowsAndConsts (hi : IvarOnly h h') {D : Decls} (hd : DeclsOk D h) :
    MethodRowsOk D h' ∧ (∀ n τ, constTy? D n = some τ → ConstOk h' n τ) ∧
      (∀ c n τ, scopedConstTy? D c n = some τ → ScopedConstOk h' c n τ) ∧
      ∀ c n d, superDecl? D c n = some d → SuperOk h' c n d :=
  ⟨fun τr mname d hf => hi.entryOk (hd.1 τr mname d hf),
   fun n τ hn => hi.constOk (hd.2.1 n τ hn),
   fun c n τ hn => hi.scopedConstOk (hd.2.2.2.1 c n τ hn),
   fun c n dd hn => hi.superOk (hd.2.2.2.2 c n dd hn)⟩

theorem noHook (hi : IvarOnly h h') (hn : NoHook h) : NoHook h' :=
  ⟨by rw [hi.classPayload]; exact hn.1,
   fun k hk => by rw [hi.lookup_eq]; exact hn.2 k (by rw [← hi.classPayload]; exact hk)⟩

theorem litClsOk (hi : IvarOnly h h') (hs : LitClsOk h) : LitClsOk h' :=
  ⟨⟨by rw [hi.classPayload]; exact hs.1.1, by rw [hi.className_eq]; exact hs.1.2⟩,
   ⟨by rw [hi.classPayload]; exact hs.2.1, by rw [hi.className_eq]; exact hs.2.2⟩⟩

theorem saturated (hi : IvarOnly h h') (hs : Saturated h) : Saturated h' := by
  refine ⟨fun mo => ?_, fun k => ?_⟩
  · rw [hi.size, modAncestors_go_congr hi.shape, modAncestors_go_congr hi.shape]
    exact hs.1 mo
  · rw [hi.size, ancestors_go_congr hi.shape hi.size, ancestors_go_congr hi.shape hi.size]
    exact hs.2 k

theorem noShadowBefore (hi : IvarOnly h h') {k : ObjId} (hn : NoShadowBefore h k) :
    NoShadowBefore h' k := by
  refine ⟨by rw [hi.ancestors_eq]; exact hn.1, fun j hj cp hcp => ?_⟩
  rw [hi.ancestors_eq] at hj
  exact hn.2 j hj cp (by rw [← hi.classPayload]; exact hcp)

theorem classOk (hi : IvarOnly h h') (hc : ClassOk h) : ClassOk h' := by
  refine ⟨by rw [hi.className_eq]; exact hc.1, hi.noShadowBefore hc.2.1, fun n hn => ?_⟩
  obtain ⟨k, cp, hco, hcp, hnm, huniq, hre, hma, hsole, hreop⟩ := hc.2.2 n hn
  refine ⟨k, cp, by rw [hi.constOwn_eq]; exact hco, by rw [hi.classPayload]; exact hcp,
    by rw [hi.className_eq]; exact hnm, ?_, hre, hma, ?_, fun hmem => ?_⟩
  · intro j hj hjn
    exact huniq j (by rw [← hi.classPayload]; exact hj) (by rw [← hi.className_eq]; exact hjn)
  · intro j hj
    rw [hi.constOwn_eq]
    exact hsole j (by rw [hi.classPayload] at hj; exact hj)
  · obtain ⟨hmod, hhd, hns⟩ := hreop hmem
    exact ⟨hmod, by rw [hi.ancestors_eq]; exact hhd, hi.noShadowBefore hns⟩

/-- And the value judgement's own transport, which is `typeAgree_of_fields` at this
    bundle. Stated here rather than beside that lemma so `hi.typeAgree` resolves. -/
theorem typeAgree (hi : IvarOnly h h') : TypeAgree h h' :=
  typeAgree_of_fields hi.size.symm hi.klass hi.eigen hi.payload hi.frozen

end IvarOnly

end Proof
end RubyCore
