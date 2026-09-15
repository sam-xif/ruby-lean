# RubyCore Semantics — Type Judgments (implementation catalog)

> **Status:** design artifact, expected to grow rule-by-rule alongside the Lean model. This
> is the **reference spec** for the typing layer whose *rationale, discipline decision, and
> survey* live in `[types-and-preservation.md](types-and-preservation.md)` (read §C.5 there
> first). It catalogs every judgment form we intend to implement, the rules for the
> in-scope fragment, and the staging that maps them onto the existing untyped machine
> (`../../ruby-lean/RubyCore/`) and its metatheory PoC (`../../ruby-lean/RubyCore/Proof/`).
>
> **Discipline (from §C.5):** *extrinsic* — the judgments below are defined *over the
> existing untyped syntax/values*; nothing here changes the interpreter or `Step`. Types are
> heap-relative through a **store typing `Δ`** (≙ `Σ`); `Δ` only grows. Preservation is a
> theorem over machine *configurations*, so we also type the continuation stack and heap.
>
> Notation follows artifact 00 §3 (named turnstiles; inference rules as premises over a
> ruled conclusion with a `(RULE-NAME)` label). Evidence tags: **[V]** verified against
> CRuby, **[D]** from Sorbet docs / the Part-B literature, **[?]** open, to pin during
> mechanization (typically against `srb`/`T.reveal_type`).

---

## 0. Judgment inventory


| Judgment                   | Reads as                                             | Lean name           | Status |
| -------------------------- | ---------------------------------------------------- | ------------------- | ------ |
| `Δ ⊢ τ`                    | `τ` is a well-formed type                            | `TyWf`              | T1     |
| `Δ ⊢ τ₁ <: τ₂`             | `τ₁` is a (static) subtype of `τ₂`                   | `Sub`               | T1     |
| `Δ ⊢ τ₁ ~ τ₂`              | `τ₁` and `τ₂` are consistent (gradual boundary)      | `Consistent`        | T3     |
| `Δ ⊢ τ₁ ≲ τ₂`              | consistent subtyping (`~` then `<:`)                 | `csub`              | T3     |
| `Δ ⊢ τ₁ ⊔ τ₂ = τ`          | `τ` is the join (least upper bound)                  | `Join`              | T2     |
| `Δ ⊢ ancestors(c) = c̄`    | static ancestry of class object `c`                  | `StoreTy.ancestors` | T1     |
| `Δ ⊢ mtype(τ, m) = σ`      | method `m` on receiver-type `τ` has sig `σ`          | `StoreTy.mtype`     | T2     |
| `Δ; Γ ⊢ narrow(e, b) = Γ'` | flow-sensitive refinement of `Γ` on guard `e` = `b`  | `narrow`            | T4     |
| `Δ ⊢ v : τ`                | heap value `v` has type `τ`                          | `HasTypeV`          | T1     |
| `Δ; Γ ⊢ e : τ`             | expression `e` has type `τ` (the engine)             | `HasType`           | T1→    |
| `Δ ⊢ K : τ_h ⇒ τ_a`        | kont stack maps a hole of type `τ_h` to answer `τ_a` | `KontOk`            | T1     |
| `Δ ⊢ ctl : τ`              | control state has type `τ`                           | `CtlOk`             | T1     |
| `Δ ⊢ m : τ`                | machine config `m` has answer type `τ`               | `ConfigTy`          | T1     |
| `Δ ⊨ H`                    | heap `H` realizes store typing `Δ`                   | `StoreOk`           | T1     |
| `Δ ⊑ Δ'`                   | `Δ'` extends `Δ` (store growth)                      | `StoreTy.extends`   | T1     |


The **engine** is `Δ; Γ ⊢ e : τ` (§6); every other judgment is either an ingredient it
calls or the machinery to lift it to configurations for preservation. Staging tiers (T1–T4)
are defined in §10.

---

## 1. Types and well-formedness

The grammar (mirrors `types-and-preservation.md` §A.1; nominal types reference a **class
object by ObjId**, reusing classes-as-heap-objects):

```
τ ::= cls c            -- an instance of class object c : ObjId   (Boot.integerId, …)
    | untyped          -- T.untyped, the gradual boundary
    | uni [τ, …]       -- T.any  (union)
    | inter [τ, …]     -- T.all  (intersection)
    | proc [τ, …] τ    -- T.proc / block type: params → ret
    | selfTy           -- T.self_type (resolved against the current frame's self class)
```

Derived (not constructors): `nilable τ ≙ uni [cls NilClass, τ]`; `Boolean ≙ uni [cls TrueClass, cls FalseClass]` [D: /docs/union-types]. `tuple`/`shape` types (§A.1) are **T5+**,
deferred.

Well-formedness `Δ ⊢ τ` checks referenced classes exist in `Δ` and (once generics land, T5)
that type-argument arity/bounds are respected:

```
  Δ.classOf c = some _                    ∀ τ ∈ ts. Δ ⊢ τ
  ─────────────────── (WF-Cls)            ──────────────── (WF-Uni)   [+ WF-Inter, WF-Proc]
  Δ ⊢ cls c                               Δ ⊢ uni ts
```

---

## 2. Subtyping `Δ ⊢ τ₁ <: τ₂`

A genuine **preorder** (reflexive + transitive) over the *static* fragment. The nominal case
is literally the `Heap.ancestors` walk lifted to `Δ` — **subtyping is a view of the class
heap, not new machinery** (§C.5).

```
                          c₂ ∈ Δ.ancestors c₁
  ───────── (S-Refl)      ─────────────────── (S-Cls)      ── (S-Trans) ──
  Δ ⊢ τ <: τ              Δ ⊢ cls c₁ <: cls c₂             Δ⊢a<:b  Δ⊢b<:c ⟹ Δ⊢a<:c

  ∀ t ∈ ts. Δ ⊢ t <: τ          t ∈ ts   Δ ⊢ τ <: t
  ──────────────────── (S-UniL)  ──────────────────── (S-UniR)     -- union is the LUB
  Δ ⊢ uni ts <: τ                Δ ⊢ τ <: uni ts

  t ∈ ts   Δ ⊢ t <: τ           ∀ t ∈ ts. Δ ⊢ τ <: t
  ──────────────────── (S-InterL) ─────────────────── (S-InterR)   -- intersection is the GLB
  Δ ⊢ inter ts <: τ             Δ ⊢ τ <: inter ts

  Δ ⊢ p' <: p     Δ ⊢ r <: r'
  ─────────────────────────── (S-Proc)      -- contravariant params, covariant return
  Δ ⊢ proc [p] r <: proc [p'] r'
```

**Mechanization note (J18, 2026-08-26).** The built relation (`Judgment/Sub.lean`'s
`SubJ`) renders `nilable τ` as a first-class arm rather than `uni [NilClass, τ]`, so
`(S-UniR)`'s nilable instance is its own rule — and the first cut **omitted it**,
which made the relation non-transitive (`int ≤ int ∪ bool ≤ nilable (int ∪ bool)`
composes to an underivable judgment; `(S-Trans)` above is a *rule* here, but the
mechanization proves transitivity as a theorem instead, precisely so a derivation
checker never has to search for a middle type). `SubJ.nilableR` is the repair —
this table's `(S-UniR)` at the nilable spelling — and `SubJ.trans` is proved by
strong induction on summed type sizes.

`**untyped` deliberately does NOT appear here** — its compatibility is *consistency* (§3),
which would break transitivity. This is the artifact's running "it is not just subtyping"
point, enforced structurally. Generic variance (`:out`/`:in`/invariant, §A.6) extends
`(S-Cls)` at **T5**; deferred while generics are out of scope (runtime-erased, §A.6). **[?]**
exact Sorbet subtype rules for `proc` arity and shape/tuple width.

---

## 3. Consistency `Δ ⊢ τ₁ ~ τ₂` and consistent subtyping `Δ ⊢ τ₁ ≲ τ₂`

The gradual boundary (Sorbet §A.5; Siek–Taha §B.5). **Reflexive and `untyped`-absorbing on
both sides, but NOT transitive** (`cls String ~ untyped ~ cls Integer`, yet `cls String ≁ cls Integer`) — the reason it cannot be a `Sub` rule.

```
  ───────── (C-Refl)   ───────────────── (C-DynL)   ───────────────── (C-DynR)
  Δ ⊢ τ ~ τ            Δ ⊢ untyped ~ τ              Δ ⊢ τ ~ untyped

  (congruence: C-Uni / C-Inter / C-Proc lift `~` structurally through composites)
```

What call sites actually check is **consistent subtyping** — factor through a middle type:

```
  Δ ⊢ τ₁ ~ τ_m    Δ ⊢ τ_m <: τ₂
  ────────────────────────────── (CS)          -- `csub`; used by (T-Send) arg checks (§6)
  Δ ⊢ τ₁ ≲ τ₂
```

On the fully-static fragment (`# typed: strong`, no `untyped`), `≲` collapses to `<:`, so T1
metatheory can ignore this section entirely. **[?]** whether Sorbet's `T.untyped`
compatibility matches textbook consistency exactly, or is looser (accepts *any* send on an
`untyped` receiver — modeled directly in (T-SendDyn), §6).

---

## 4. Auxiliary definitions

### 4.1 Store typing `Δ` (≙ `Σ`)

```
MethSig  ::= { params : List Ty, ret : Ty }               -- a Sorbet `sig`
ClassTy  ::= { super : Option ObjId, methods : List (String × MethSig) }
Δ : StoreTy ::= { typeOf : ObjId → Option Ty,             -- instance objects → their type
                  classOf : ObjId → Option ClassTy }      -- class objects → static payload + sigs
```

`Δ ⊢ ancestors(c) = c̄` and `Δ ⊢ mtype(τ, m) = σ` mirror `Heap.ancestors` / `Heap.lookup`
exactly — walk `super` links, first defining class wins:

```
  Δ ⊢ ancestors(c) = c̄     firstDefining(c̄, m) = some (c', σ)
  ─────────────────────────────────────────────────────────── (MTYPE)
  Δ ⊢ mtype(cls c, m) = σ
```

Keeping `mtype` a *structural mirror* of `Heap.lookup` is load-bearing: static and dynamic
method resolution walk the same ancestry, which is what makes the `send` preservation case
go through (§C.5). `mtype` on a `uni` requires the method on **all** members (§A.1); on
`untyped` it is `none` (handled by (T-SendDyn), not `mtype`).

### 4.2 Join `Δ ⊢ τ₁ ⊔ τ₂ = τ`

Least upper bound — the ingredient that types an `if` whose branches differ. First cut:
normalized union (`Sorbet` infers `T.any` at merge points), with nominal LUB when both are
`cls`. Not derivable from `<:` alone; a separate definition.

### 4.3 Narrowing `Δ; Γ ⊢ narrow(e, b) = Γ'`  (flow-sensitivity, T4)

Occurrence typing (§A.2; Typed Racket §B.4). Refines `Γ` given that guard expression `e`
evaluated to boolean `b`. Guards are themselves sends (`is_a?`, `nil?`, `kind_of?`,
`instance_of?`, `===`), so this judgment arrives with T4, after `send`. Restricted to
**locals** (§A.2) — `narrow` only rewrites `Γ` entries, never method-call results.

```
  -- representative: is_a? on a local narrows it in the true branch
  ──────────────────────────────────────────────────── (N-IsA-T)
  Δ; Γ ⊢ narrow( send(var x, "is_a?", [const C]), true ) = Γ[x ↦ inter [Γ(x), cls C]]
```

**[?]** the full guard catalog and the "guard-not-overridden" soundness assumption (§A.2).

---

## 5. Value typing `Δ ⊢ v : τ`

Immediates get their bootstrap class; refs consult `Δ`; subsumption via `<:`.

```
  ─────────────────────── (V-Int)     ────────────────────────── (V-Nil)
  Δ ⊢ int n : cls Integer             Δ ⊢ nil : cls NilClass

  ─────────────────────────── (V-Bool)   Δ.typeOf o = some τ
  Δ ⊢ bool b : Boolean                    ───────────────── (V-Ref)     [+ V-Flt, V-Sym]
                                          Δ ⊢ ref o : τ

  Δ ⊢ v : τ     Δ ⊢ τ <: τ'
  ───────────────────────── (V-Sub)
  Δ ⊢ v : τ'
```

---

## 6. Expression typing `Δ; Γ ⊢ e : τ` — the engine

`Γ : TyEnv = List (String × Ty)` is the static types of in-scope locals. Rules organized by
staging tier. **The `send` rule is the whole game** (everything is a send); the rest are
short.

### 6.1 T1 — the static control core (matches the fragment already proven in `Proof/Step.lean`)

```
  ─────────────────────────── (T-Int)   [+ T-Flt/Str/Sym/True/False/Nil/Self analogously]
  Δ; Γ ⊢ int n : cls Integer

  Γ.find? x = some τ                     Δ; Γ ⊢ e : τ
  ────────────────────── (T-Var)         ─────────────────────────── (T-Vasgn-L)
  Δ; Γ ⊢ var lvar x : τ                  Δ; Γ ⊢ vasgn lvar x e : τ     (binds x:τ downstream)

  Δ; Γ ⊢ e : τ    ivarType(Δ, self, x) = τ_d    Δ ⊢ τ ≲ τ_d
  ───────────────────────────────────────────────────────── (T-Vasgn-Ivar)
  Δ; Γ ⊢ vasgn ivar x e : τ

  Δ; Γ ⊢ eₙ : τ         (earlier stmts well-typed, values discarded)
  ────────────────────── (T-Seq)     -- type of a seq is its last statement's type
  Δ; Γ ⊢ seq [e₁ … eₙ] : τ

  Δ; Γ ⊢ c : _   Δ; Γ' ⊢ t : τ₁   Δ; Γ'' ⊢ e : τ₂   Δ ⊢ τ₁ ⊔ τ₂ = τ
  ───────────────────────────────────────────────────────────────── (T-If)
  Δ; Γ ⊢ if c t (some e) : τ
      where Γ' = narrow(c,true) Γ,  Γ'' = narrow(c,false) Γ   (narrow = id until T4)

  Δ; Γ ⊢ c : _    Δ; Γ ⊢ b : _
  ──────────────────────────── (T-While)     -- while yields nil (or a break value; §6.4)
  Δ; Γ ⊢ while c b : cls NilClass

  Δ; Γ ⊢ e : τ                            Δ; Γ ⊢ e : τ
  ──────────────────── (T-Break)          ──────────────────── (T-Next)
  Δ; Γ ⊢ brk (some e) : ⊥ₜ                Δ; Γ ⊢ nxt (some e) : ⊥ₜ
```

Jumps (`brk`/`nxt`/`ret`) have a **bottom-ish** answer type `⊥ₜ` (they never yield to their
context) whose value flows to the loop/frame marker kont, not the local continuation — the
kont-typing (§7) is where the break value's type is actually consumed. **[?]** exact
treatment of `⊥ₜ` (either a real `Ty.bottom`, or thread break-types through `KontOk`).

### 6.2 T2 — the send rule (+ `def`, method table)

```
  Δ; Γ ⊢ recv : τ_r    Δ ⊢ mtype(τ_r, m) = {params := σ̄, ret := ρ}
  Δ; Γ ⊢ aᵢ : τᵢ    Δ ⊢ τᵢ ≲ σᵢ   (each arg consistent-subtypes its param)
  ──────────────────────────────────────────────────────────────────── (T-Send)
  Δ; Γ ⊢ send (some recv) m ā none : ρ
```

`def` typechecks the body against the declared sig and is what *populates* `Δ.classOf`'s
method list (its well-formedness is checked in `Δ ⊨ H`, §8):

```
  Δ; (params:σ̄, self:cls C) ⊢ body : ρ'    Δ ⊢ ρ' <: ρ    sig(C,m) = (σ̄ → ρ)
  ─────────────────────────────────────────────────────────────────────────── (T-Def)
  Δ; Γ ⊢ def m params body : cls Symbol
```

Implicit-self sends (`recv = none`) resolve `τ_r = self`'s type from the frame (§7). Blocks
(`blk`/`yield`), `super`, splat/kwargs args: **T2.5+**, following the desugar M2 shape.

### 6.3 T3 — the gradual boundary

```
  Δ; Γ ⊢ recv : untyped                    ────────────────────────── (T-Unsafe)
  ──────────────────────────── (T-SendDyn) Δ; Γ ⊢ send _ "T.unsafe" [e] _ : untyped
  Δ; Γ ⊢ send (some recv) m ā _ : untyped

  -- a method with no sig has all-untyped params + untyped return (§A.5)
  -- T.let(e, τ): checked; T.cast(e, τ): trusted statically, runtime-checked (§A.3)
  Δ; Γ ⊢ e : τ'    Δ ⊢ τ' ≲ τ                            (no static premise on the operand)
  ──────────────────────────── (T-Let)     ──────────────────────────── (T-Cast)
  Δ; Γ ⊢ T.let e τ : τ                     Δ; Γ ⊢ T.cast e τ : τ
```

`T.cast`/`T.let`/`T.must`/`T.bind` desugar to sends (or are recognized heads); their
**runtime** halves are modeled as boundary casts installed by heap mutation (the RTTI axis,
§C.5) — a `TypeError` on failure, which is `obs`-visible and is the "blame" outcome of the
gradual-safety theorem (§9). **[?]** whether to give `T.cast` a distinct RubyCore head or
recognize the send.

### 6.4 Deferred heads (T5+)

`class`/`module`/`sclass`/`defs` (type the body under an updated `Δ`; the mutation is a
`Δ`-extension), `begin`/`rescue`/`ensure` (handler binds the exception type; join over
normal + rescue exits), `array`/`hash` (→ `T::Array`/`T::Hash` generics), `blockpass`,
`const`/`casgn`. Each lands with its operational counterpart in artifacts 07–10.

---

## 7. Continuation & configuration typing

`Step` is an abstract machine, so preservation is over **configurations** — we type the kont
stack as a transformer *hole-type ⇒ answer-type* (standard CEK-machine typing; the piece
beyond textbook expression typing, §C.5).

```
  ───────────── (K-Nil)          Δ; Γ ⊢ seq rest : σ    Δ ⊢ ks : σ ⇒ ans
  Δ ⊢ [] : τ ⇒ τ                 ─────────────────────────────────────── (K-SeqK)
                                 Δ ⊢ (seqK rest :: ks) : hole ⇒ ans      (hole discarded)

  Δ; Γ ⊢ t : τ₁   Δ; Γ ⊢ e : τ₂   Δ ⊢ τ₁⊔τ₂ = σ   Δ ⊢ ks : σ ⇒ ans
  ──────────────────────────────────────────────────────────────── (K-IfK)
  Δ ⊢ (ifK t (some e) :: ks) : _ ⇒ ans

  -- one rule per Kont: asgnK, casgnK, whileCondK/whileBodyK (loop markers carry break-type),
  -- recvK/argsK/argsSplatK/blkCoerceK (send in flight), frameK/blkFrameK (activation
  -- boundaries; the hole is the method/block return type), begin*/rescue*/else*/ensure konts.
```

Control and whole-config typing:

```
  Δ; Γ_self ⊢ e : τ                Δ ⊢ v : τ
  ───────────────── (Ctl-Eval)     ──────────────────── (Ctl-Value)
  Δ ⊢ eval e : τ                   Δ ⊢ value v : τ

  Δ ⊢ m.ctl : τ_h     Δ ⊢ m.kont : τ_h ⇒ ans     (frames well-typed vs Δ; jumps in-flight ok)
  ────────────────────────────────────────────────────────────────────────────── (CFG)
  Δ ⊢ m : ans
```

`Ctl-Eval` draws `Γ_self` from the current frame (its `self` class + bound locals). A
`jump` control state is typed by matching its target marker kont — the auxiliary rules that
make *every intermediate state* typeable, i.e. the FJ "stupid cast" / Typed-Racket
"proof-theoretic rule" tax (§B.2, §B.4). **[?]** the exact frame/`Γ` reconstruction from the
frame store.

---

## 8. Heap well-formedness `Δ ⊨ H` and store growth `Δ ⊑ Δ'`

`Δ ⊨ H` (the `Σ ⊨ H` recipe, §B.3) — the heap *realizes* the store typing:

1. **Class agreement:** for every allocated `o`, `H`'s object class matches `Δ.typeOf o` and
  `Δ.classOf` mirrors `H`'s superclass links.
2. **Method-body fidelity (the content clause):** for every `(m ↦ σ) ∈ Δ.classOf c`, the
  method body in `H` typechecks against `σ` — `(T-Def)`'s premise, but as a heap invariant.
3. **Frame/representation:** bootstrap classes intact (the clause metaprogramming can break —
  the *type* `escape` of §C.2, caught at runtime by sig checks).

```
  ∀ o ∈ dom(Δ). (class agreement)   ∀ (c,m,σ). (method-body fidelity)   (frame clauses)
  ──────────────────────────────────────────────────────────────────────────────────── (STORE-OK)
  Δ ⊨ H
```

`Δ ⊑ Δ'` ("`Δ'` extends `Δ`") holds when `Δ'` agrees with `Δ` on all of `Δ`'s domain. It is
discharged directly by the already-proven `**Step.heap_monotone**` (the heap only grows,
ObjIds never reused) — the one preservation ingredient the metatheory PoC *already has*.

---

## 9. Metatheorems (statements)

```
-- Preservation (subject reduction), up-to-subtyping, growing store  (FJ §B.2 + UT §B.3)
theorem preservation :
  Δ ⊨ m.heap → Δ ⊢ m : τ → Step m m' →
  ∃ Δ', Δ ⊑ Δ' ∧ Δ' ⊨ m'.heap ∧ Δ' ⊢ m' : τ'  ∧ Δ' ⊢ τ' <: τ

-- Progress, fully-static fragment (# typed: strong, no `untyped`)
theorem progress_static :
  Δ ⊨ m.heap → Δ ⊢ m : τ → m.isFinalValue ∨ ∃ m', Step m m'

-- Gradual safety, the real Sorbet target (§C.1 option 2): three outcomes
theorem gradual_safety :
  Δ ⊨ m.heap → Δ ⊢ m : τ →
  m.isFinalValue ∨ m.raisedTypeError ∨ ∃ m', Step m m'
```

Proof-shape notes: preservation is one `cases`/induction over `Step`, one case per rule; the
only hard case is `send`, and it goes through because `mtype` mirrors `Heap.lookup` (§4.1).
`up-to-subtyping` (τ' <: τ) is mandatory in any language with subsumption (FJ §B.2). The
`raisedTypeError` disjunct of `gradual_safety` corresponds to blame landing on untyped code
(the blame theorem, §B.5) and is `obs`-observable, hence differential-testable.

---

## 10. Implementation staging

Each tier keeps the ratchet discipline of the rest of the project (0 disagree; the new
theorems only accrete). Tiers map onto the existing untyped fragments.


| Tier    | Adds                                                                                                            | Meets                                                                                         | Milestone theorem                                      |
| ------- | --------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------- | ------------------------------------------------------ |
| **T1**  | `Ty`, `TyWf`, `Sub` (nominal+uni+inter), `Δ`/`StoreOk`, `HasTypeV`, `HasType` §6.1, `KontOk`/`ConfigTy`, `Δ⊑Δ'` | the **exact fragment in `Proof/Step.lean`** (literals, var/vasgn, seq, if, while, break/next) | `preservation` + `progress_static` on the control core |
| **T2**  | `mtype`, `Join`, `(T-Send)`, `(T-Def)`, method-body fidelity clause                                             | `send`/`def` in the L1/L2 stepper                                                             | preservation extends to dispatch                       |
| **T3**  | `untyped`, `Consistent`/`csub`, `(T-SendDyn)`, `T.let`/`T.cast`/`T.unsafe`, runtime cast model                  | the gradual boundary                                                                          | `gradual_safety`                                       |
| **T4**  | `narrow` + guard catalog (occurrence typing)                                                                    | `is_a?`/`nil?` narrowing                                                                      | narrowing sound (Preservation-of-predicate, §B.4)      |
| **T5+** | generics + variance, tuple/shape, `class`/`begin`/collections                                                   | artifacts 07–10                                                                               | full-fragment soundness                                |


**Where it lives:** a new `../../ruby-lean/RubyCore/Types/` (grammar, `Sub`, `Δ`, `mtype`)
imported by a `../../ruby-lean/RubyCore/Proof/Typing.lean` that adds `HasType`/`ConfigTy` beside
the existing `Step` and proves T1 preservation, reusing `Step.heap_monotone`.

**No-Lean de-risking first** (mirrors the desugar-first discipline, §C.3): use
`srb`/`T.reveal_type` as an oracle for `HasType`, and an `obs⁺` gradual-guarantee probe
(run with/without sigs), before committing the rules to Lean.

---

## 11. Open questions

- **[?]** `⊥ₜ` for jumps (§6.1): real `Ty.bottom` vs. threading break/return types through
`KontOk`.
- **[?]** The exact `narrow` guard catalog and how to encode the "guards not overridden"
assumption (§4.3, §A.2).
- **[?]** Whether `T.cast`/`T.let`/`T.must` get distinct RubyCore heads or are recognized
sends (§6.3), and how their runtime halves normalize in `obs` (distinguishing a cast
`TypeError` from a genuine `NoMethodError`).
- **[?]** `Δ` for user-defined constants/reopened classes: how much of `Δ` is fixed by
bootstrap vs. accreted by `(T-Def)`/`class` as `Δ`-extensions.
- **[?]** Do generics enter the model at all given runtime erasure (§A.6)? (Lean toward:
defer past T5, since they contribute nothing to a *runtime* preservation statement.)

