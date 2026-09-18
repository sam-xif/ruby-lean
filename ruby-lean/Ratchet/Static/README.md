# `Ratchet/Static/` — the static vocabulary

The tables, predicates and contexts that **both** sides of the ladder are stated over:
`Ratchet/Judgment/`'s rules cite them in their premises, `Ratchet/Guards/` decides them, and
`Denote/Sem/`'s `StateOk` says what it means for a real machine to conform to one. Nothing
here is a judgment and nothing here is executable checking.

Until this commit it was a single 3,591-line file called `Ratchet/Judge.lean` — a name that
had stopped being true. The judgment it was named for (`inductive Judge`, 83 rules) was
deleted in clink 68; what stayed behind was all of this. The split below is at that file's
own section boundaries, in its own reading order, so each file still imports its predecessor:

| file | contents |
|---|---|
| `Predicates.lean` | `EqSafe`, `NilQSafe`, `ObjectMethod`, `BuiltinCls`, `ExcCls`, `PrimSig`, `BareNameError` |
| `DefTable.lean` | `Defn`/`DefTable` — a top-level `def` as the checker remembers it |
| `Purity.lean` | `declFree`, `nxtFree`, `asgnFree`, `nxtPrefixOk` — the freedom predicates §F3 and §F23 forced |
| `Lookup.lean` | `defDeclared?`/`defGet?`, the assumption table, constant literals, `paramBind`/`paramEnv` |
| `Classes.lean` | `Cls`/`CTable`, class-body members and constants, method lookup up the chain, the MRO |
| `Ancestors.lean` | `ancestors?`, the builtin chains, `isAAnswer`, the dispatch guards, `mergeCls` |
| `Nested.lean` | `nestedClasses`/`extendClasses`, and `Frame` (the activation `super` reads) |
| `ExprEq.lean` | a structural `Expr` comparator that kernel-reduces |
| `Closures.lean` | `Clos`/`ClosTable`/`collectBlocks` — what `Ty.clos` refers to |
| `Ctx.lean` | `Pos`/`Neg`/`Scope`/`Ctx`, the accessors, the `Neg` seed, the constant tables |
| `Iterators.lean` | `IterSig` — a builtin whose signature mentions a block |
| `Capture.lean` | `Ctx.inClosure`, `capIntact`, `ivarAgree*`, `ivarAsgnOk`, `bodyResult`, `procRetOk` |
| `Narrow.lean` | tier 12's refinements and the conditions that license them |
| `Kept.lean` | `ctxKept` and `ctx0` |
| `All.lean` | the chain's tail, for consumers that want the whole vocabulary |

`CtxEq.lean` (proof-producing branch compatibility) and `NativeInstanceNames.lean` (the
generated per-class name tables) also live here: both are comparisons over this vocabulary
rather than rules about it.

## The judgment this file was named for, and its scope

Historical, kept because it records what the deleted judgment covered and why — the
limitations below are the ones `Ratchet/Judgment/DJudge.lean` was authored to replace one
rule at a time, each with a semantic proof.

## Scope: tiers 1–7's object model, and no more

Deliberately authored for the rungs reached so far (tier 1's eight literals, tier 2's
`send`-shaped rungs, tier 3's `var`/`vasgn`/`seq`/bare-`vcall`, tier 4's conditionals,
tier 5's array and hash literals and their `#[]`, tier 6's top-level `def` and
implicit-self calls, and tier 7's classes, `new`, instance variables, instance-method
dispatch and `self`), and nothing else. Consequences, each a real limitation to lift later,
not an oversight:

- **Two things thread, and both are flat.** `Judge κ Γ I e τ Γ' I'` reads: *in context `κ`,
  with locals `Γ` and instance variables `I`, `e` synthesizes `τ` and leaves `Γ'` and `I'`
  behind*. The output states are what make `x = 1; x = true; x` typeable — an assignment is
  an expression whose effect the next expression sees. Locals are a *flat*
  `List (String × Ty)` with `envSet` overwriting in place: real Ruby locals are not
  single-typed, so re-binding a name at a different type is correct behaviour, not a gap
  (rung `reassign-different-type`). Instance variables are a `Ty` spine rather than an
  `Env`, because they also have to sit inside `Ty.inst` — see there.
- **Locals and `@ivar`s only.** Rules mention `VarKind.lvar`/`.ivar` explicitly;
  `@@cvar`/`$gvar` have no rule, so a program touching one is simply not typed.
- **No `subTy` anywhere.** Every rule below matches types by construction. `subTy`
  exists in `Ratchet/Lang/Ty.lean` and is unused here on purpose: nothing yet has a subtype
  worth exploiting, and a subsumption rule admitted "for later" is a rule whose soundness
  nobody has had to justify against a rung. Tier 7's second clink — inheritance — is where
  that stops being true.
- **No inheritance, no `super`, no singleton methods.** `Cls.super?` is *recorded* by
  `extendClasses` and read by nothing: method lookup is `defGet? c.methods`, one class deep.
  So `class Dog < Animal` declares fine and `Dog.new` finds no `initialize`.
- **Callable values, but not blocks-to-builtins.** Tier 9's `lambda`/`proc` and `#call`
  are typed; a block *passed to* a method (`[1,2].map { … }`), `yield`, `&`-block parameters
  and block-locals are not. Tier 10's metaprogramming is untouched. Modules are typed (tier
  8), but only their
  singleton methods are reachable: `include`, `extend` and `module_function` have no rule, so
  a module's *instance* methods are recorded and unusable.
- **`self` is typed only inside an instance-method body**, and only as `.inst n Iself`.
  At top level `κ.selfTy` is `none`, which two rules depend on: `bareName` (which requires
  it) and `prim`'s "explicit receiver only" restriction (an implicit-self send at top level
  goes to the `defs` table). Inside `initialize` it is deliberately *also* `none` — see
  `newInst` for why that is a soundness requirement and not an omission.

## Every rule is a synthesis rule

There is exactly one kind of rule here: a **synthesis rule justified by the real
semantics** — a literal's type, or a primitive's signature (`PrimSig`). §Justification
in `AGENTS.md`'s tier-1/2 notes plus `Check13.lean`'s semantic cross-check are what back
them.

There used to be a second kind: a `claim` leaf admitting whatever a certificate asserted
about a subterm. It was the certificate architecture's trusted edge, and it was *unsound
in general* — a cert could claim anything, so a `Judge` derivation using it asserted
nothing. **It is gone** (2026-08-31), along with `Cert` itself: `Judge` now relates an
`Expr` to a `Ty` with nothing trusted in between, so *every* derivation in this package
is built only from rules that say something checkable about the real semantics, and a
rung is climbed only when the checker really can synthesize it. See `AGENTS.md`
§Claim-free.
