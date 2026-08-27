# `Judgment/` — implementation notes (J-numbers)

Decision record for the declarative judgment layer (`judgment-layer.md` J0), per the
§7 working norms. Format follows `Cert/implementation-notes.md` (V-numbers).

## J1 — a `Prop` needs no fuel and no kernel reduction

`Judge` is an inductive relation, so none of `chk`'s load-bearing constraints apply:
no fuel, no L73 reducibility discipline on this path, no `.induct` derivability
concerns (inversion is `cases`). The library is off the default build target for
Metatheory's reason (`lake build Judgment`).

## J2 — `JCtx extends FrameCtx`, adding the two channels `chk` lacked

`FrameCtx`'s six channels are reused by structure extension (no copy; their
docstrings stay the reference). Two new channels, each converting a claim-gated `chk`
arm into a **sound rule**:

* `blk : Option BlockSig` — the enclosing method's declared block signature, set by
  `defDecl`/`defs` from the chosen declaration, read only by `yield'`, cleared by
  `jBlockCtx` (a `yield` in a block targets the *home* method's block — a pairing
  this context cannot see).
* `inRescue : Bool` — set by `JudgeRescues` on handler bodies, read only by
  `retry'`, cleared on entering method/block/class bodies.

Two arms remain **assumption rules**, marked `[ASSM]` in the file: `var .cvar` /
`vasgn .cvar` — class variables are the one namespace `Decls` has no channel for.
The chosen type is discharged by nothing here; the future fix is a `cvars` field on
`Decls` (a `Types/` change with its own L-number), after which these become
declared rules like ivars.

## J3 — claims become derivation choices; assumed rows live in `D`

Everywhere `chk` consults the certificate, `Judge` quantifies over the choice and the
derivation records it (D1's stackmaps as proof-theory). Consequences:

* `joinTy` disappears from the rules: the `if`/`begin` joins are one rule each with
  a chosen upper bound (`joinTy`'s answer is an instance, by `joinTy_sub`).
* The chosen continuation environment is **checked** (`SubEnv Γc` into each branch
  exit) where `chk`'s `claimEnv` was unchecked — the sound form of the same arm.
* There are **no claim-fallback rules** on `send`/`vcall`/`const`/`yield`: an
  asserted signature or constant is a row in the certificate's table `D`
  (deltaRows → residue), consumed by the ordinary rule. This is §9.1's "a
  certificate names the declaration table" carried to its conclusion.

## J4 — subsumption

One non-syntax-directed rule: weaken the type up (`subTy`), weaken the exit
environment by **dropping bindings** (`SubEnv`). See J13 for what "dropping, not
coarsening" costs.

## J5 — narrowing, first rung

`ifNarrowElse`/`ifNarrowNone`: a condition that is a bare local read of a
`.nilable σ` narrows the local to `σ` in the then-branch (truthy ⇒ not nil ⇒ a σ).
Sound for every σ including `.bool`. The **else**-branch is *not* narrowed to
`.nilT`: when `σ = .bool` the falsy value may be `false : bool`, so else-narrowing
needs a `σ ≠ .bool` side condition — deferred. The `x.nil?`-condition family (the
`&.` desugar shape) is the next rung.

## J6 — loop rules deviate from `chk`, in the sound direction

* Stability is **containment** (`SubEnv Γl ·` at each subcomputation exit), not
  `chk`'s environment equality — the back edge re-enters at `Γl`, which is all it
  needs.
* The loop's exit environment is **`Γl`** (the stackmap), not the entry `Γ`. `chk`
  answers the entry environment, which is unsound when a claimed `Γl` widens a
  binding the body then retypes — coverage-tier only there (`claimFree` excludes
  it from the sound tier), but the spec states the right thing.
* `brk (some e')` requires the value below the loop's type, which is `.nilT` for
  every loop this judgment types (a valued `break` makes the loop evaluate to the
  value; `while` is typed `nil`). `chk` claim-gates this; the spec restricts it.

## J7 — `redo'` carries the premise `chk`'s arm lacks

`redo` re-enters the loop **body** (typed at `Γl`) from the current environment, so
it owes `SubEnv Γl Γ` exactly as `nxt` does. `chk`'s `redo'` arm checks only
`ctx.inLoop.isSome` — flagged as a possible gap in `chk`'s coverage tier (mid-body
*retyping* of a local, then `redo`, re-enters the body with a wrong assumption).
`redo` is not in `inferFrag`, so no sound-tier claim is affected; verify before
filing against `chk`.

## J8 — [SOUNDNESS-OPEN] `begin'` handlers at the entry environment

Transcribed from `chk`: handlers judged at the region's entry `Γ`. Counterexample
shape: the body retypes a local (`x = "s"` after `x : Int` at entry), then raises —
the handler runs at the mid-body environment, where the entry-env assumption about
`x` is false. Neither `chk` nor `Judge` is in the sound fragment here, so nothing
proved is wrong; the question must be **resolved at J1 preservation**, not patched
silently. Candidate fixes: (a) judge handlers at `Γ` masked of every local the body
assigns (needs an assigned-names predicate), (b) per-raise-point environments
(heavier). Decided to transcribe-and-flag rather than guess.

## J9 — the `def` rules

* `defDecl` generalizes `chk`'s claimed arm to a full chosen `MethodDecl`
  (params, return, **block signature**) — the block signature is what opens the
  `blk` channel for `yield` (J2). It adds `declaresName D name = false`, which
  `chk`'s claimed arm lacks: redefining a name whose row is in force silently
  retargets the row at the new body. (For `chk` this is coverage-tier; noted.)
* `defPromote` is `chk`'s deterministic nullary arm guard-for-guard, including
  `ret := none` on the body (a `return` inside a promoted body refuses) and the
  eight-clause promotion guard, threading `addRow`.
* `defs` chooses a declaration, judges the body at `selfCls := none`, threads no
  row. No `singleton_method_added` guard (`chk` has none either) — noted as an open
  question for the oracle.

## J10 — private binding helpers, and the norm-7 debt

`bindParamsJ`/`bindTargetsJ`/`paramNames` are non-fuel spellings of
`Cert.bindParams`/`Cert.bindTargets` (a `Prop` needs no fuel; the spec states the
recursion directly). This is the `defFree`/`defFreeF` precedent, and the debt is
paid the same way: an equivalence lemma (`Cert.bindParams n ps τs Γ = bindParamsJ
ps τs Γ` for sufficient `n`) lands with the adequacy work. `destr` sub-names bind at
`.any` via `paramNames` (transitive collection) rather than nested recursion —
extensionally what `Cert.bindParams` does.

`defFree` (the promotion guard) is used **by import from `Types/Core.lean`** — no
copy. This couples the module graph to the file that defines `infer`; acceptable
because the concern retired at V12 was the checked *path* calling `infer`, which a
`Prop` cannot. If module hygiene ever matters, move `defFree` down to `Syntax.lean`
(own L-number) as `isMatchView` was.

## J11 — deliberate refusals (arms with no rule), the complete list

* `.block` / `.blockpass` outside a send's `blk` slot — not values the machine
  evaluates; the send rules consume them in place (`chk` refuses too).
* `.undef` — row removal; no sound rule against a table with no notion of removal.
  (`chk` covers it claim-gated; the spec refuses. If a rule is ever wanted, its
  premise is "no claimed row mentions the name", which needs a row-mention
  predicate.)
* `.alias'` with the old name's row **in force** — same invalidation problem;
  admissible only when `declaresName D old = false` (that rule exists).
* Block-bearing `super`/`zsuper` — a `blk`-carrying row is deliberately unreadable
  (L242).
* `self` in a class body / at toplevel — `selfCls = none` refuses; a `.clsOf
  ctx.cls` answer is sound in a class body but wrong at toplevel (`main` is an
  Object *instance*), and `top`'s threading does not pin the two apart. Candidate
  widening once it does.
* Implicit-receiver literal-block sends other than `lambda` — `chk` reaches them
  only via a claim; here the assumed row lives in `D` and `sendIterA`/`sendIter0`
  need the receiver's type, which an implicit receiver supplies via `JudgeRecv`
  only in the args-bearing rule (`sendIterA`). The no-args implicit case is the
  gap; add when a corpus shape wants it.

## J12 — `JudgeElems` recurses through `Judge`'s own splat rules

`chkElems` special-cases `.splat (some o)` inline and accepts only `.cls "Array"`;
the relation just recurses, so an `.arrayOf` splat element is admissible here and
refused by `chkElems`. Sound (an `arrayOf` is an Array — `spreadA` accepts it);
recorded because it is a place a future `chk → Judge` adequacy lemma will notice.

## J13 — environment weakening is exact-type; the precision ceiling is real

`SubEnv` (reused from `Types/Ty.lean`) can **drop** a binding but never **coarsen**
one. Consequence, measured in `Examples.lean`: after `if x then … else …` narrows
`x : Int?` to `.int` in one branch, no continuation environment can retain `x` at
all (`.int` at one exit, `.nilable .int` at the other, and no common exact type), so
the join forgets the variable. The upgrade is a subtype-aware weakening
(`envGet? Γ' x = some σ ∧ subTy σ τ`) or a per-binding `joinTy` env-join — a
`Types/` widening with its own L-number, wanted before real narrowing-heavy corpora.
`chk` has the same ceiling (`subEnvB` is exact), so this loses nothing today.

## J14 — unions: the `Ty` arm is inert; `SubJ` carries the meaning; joins widen and conditionals re-narrow

`Ty.union` (L269, `Types/Ty.lean`) is deliberately **inert on the checker path** —
the alternative (a union-decomposing `subTy`) cannot stay structurally recursive on
`τ` and a well-founded `subTy` stops kernel-reducing under `chk` (norm 5 / L73),
hit at design time. The semantics live here:

* **`SubJ`** (`Sub.lean`) — declarative subtyping: `subTy` embedded whole by `base`,
  union decomposition on both sides, `nilableL` for the left decomposition `subTy`
  cannot state. Every `subTy`/`subTys` premise in `Judge` became `SubJ`/`SubJs`, so
  the relation is a strict widening and every J0 derivation still stands.
* **Widened joins for free**: the join rules already take a chosen bound, so
  `τj := mkUnion τt τe` is always eligible (`mkUnion_sub`) — no rule changed.
  `mkUnion` collapses equal sides and normalizes a `nilT` side to `.nilable`, so
  optionals keep one spelling.
* **Re-narrowing**: J5's rules generalized — premise is now any `envGet?` type;
  then-branch at `dropNil τ₀` (strips the nil half of a nilable *or union*; sound
  for every type, `false : bool` included), else-branch at `elseNarrow τ₀` (`nilT`
  when `boolFree τ₀`, unchanged otherwise) — which **retires J5's deferred
  else-branch narrowing**, with the `σ = bool` unsoundness handled by the
  `boolFree` gate instead of a side condition.
* **The named bill** (unchanged from L269): `ValueTy` has no union disjunction arm,
  so machine typing cannot yet witness a union-typed value — the J1 obligation
  before preservation can cover the union join rules. Union *receivers* also do not
  dispatch (`tyClassNames = []`); narrowing-then-dispatch is the intended pattern,
  and an all-members-agree `sigOf` arm (the L260 nilable shape) is the future
  widening if direct union dispatch is ever wanted.

Demonstrated in `Examples.lean`: `if true then 1 else "s"` at `.union .int
(.cls "String")` (a join `chk` refuses without a claim), and `x : nilT ∪ Int`
re-narrowed to `.int` by `if x` — `dropNil` reduces definitionally, so the
derivations are `rfl`-driven.

## J15 — why narrowing keys on truthiness only (no `nil?`/`is_a?` condition rules)

Answering the design question "is full-language narrowing easy?" — **no**, for two
specific, checkable reasons; truthiness over the full type language *was* easy and
is done (J14):

1. **Predicate methods are user-shadowable.** `if x.nil?` narrows soundly only if
   `nil?` resolves to `Object#nil?`/`NilClass#nil?` — but `def nil?; true; end` on
   any class makes the test lie, `defDecl` accepts such a body (no row is threaded,
   so `declaresName` does not see it), and the invariant carries no "predicate
   methods unshadowed" conjunct. Truthiness is the one test the machine performs
   **without a dispatch**, so it is unforgeable. A `nil?` rule needs either a
   no-shadow heap conjunct (machine typing, J1+) or a syntactic no-`def nil?`
   fragment condition.
2. **`is_a?`-narrowing needs `Sub`.** `subTy` has no subclass relation (`Sub` is
   equality below `any`), so "keep the union members below `.cls C`" misclassifies
   a subclass instance: `x.is_a?(C)` answers true for `D < C`, but the member
   `.cls D` is not below `.cls C` and would be dropped — narrowing would then be
   *unsound*, not just imprecise. Blocked on the ancestors-walk `Sub` rung
   (`PLAN.md` W5 T2), which is where the DRuby-style occurrence typing bill
   actually lands.

## J16 — arrows: lambdas typed, `call` eliminates, subtyping gains variance

The rung the L270 spine exists for. Three pieces:

* **`SubJ.arrow0`/`SubJ.arrowCons`** — contravariant parameters, covariant return,
  cell by cell over the spine (which is why no mutual `SubJs`-in-`SubJ` was
  needed — the spine linearizes the parameter list into the relation's own
  recursion). Arity mismatch refuses by shape: an `arrowCons` is never below an
  `arrow0`. Since every send-rule premise is already `SubJ`/`SubJs` (J14),
  **receivers accept subtype arguments — higher-order ones included — with no
  rule changes**: passing a `(Int?) → Int` lambda where a `(Int) → Int?` is
  declared is admissible by exactly the variance rule.
* **`sendLambdaArrow`** — the intro. The J0 opaque rule (`.any`, body unjudged)
  is kept beside it: still sound (an `.any` value is uninvokable from typed
  code), and it is what a derivation falls back to when the body is out of
  fragment. The arrow rule judges the body in a **block context except `ret`**:
  a `return` in a *lambda* returns from the lambda [V], so `ret := some σa` — the
  one channel where lambda and block genuinely differ, and the reason this rule
  is **lambda-only**: `proc {}`/`Proc.new {}` have method-targeting `return` and
  lenient arity, so minting them arrows with these semantics would be unsound.
  They stay `.any` until a proc-flavored arrow (or a leniency-aware `call` rule)
  is priced.
* **`sendCall`** — the elim, reading the spine via `arrowParts?` (so only
  well-formed spines eliminate), args below params by `SubJs`, arity exact by
  shape — which is lambda arity semantics, matching the only mint.

**The named bill, extending L269's**: `ValueTy` has no arrow arm, so machine
typing cannot yet witness a lambda at an arrow — the J1 obligation is "a
`Value.proc`-shaped closure inhabits `arrowOf τs σ` when its body preserves the
binding discipline," i.e. arrows join unions in the preservation queue. Until
then arrow rules are spec + coverage, same status as everything else here.

Demonstrated in `Examples.lean`: `l = lambda { |a| a }; l.call(1)` end to end at
`.int`, the variance example `(Int?) → Int ≤ (Int) → Int?`, and the `decide`d
refusal of the flipped direction at the `subTy` base.

## J17 — method bodies are not arrows, decided

Considered and declined while adding L270: converting `MethodDecl` to an arrow
(or typing `def` bodies at one). A method is not a value in Ruby — nothing
first-class carries it — and `MethodDecl` already *is* the method-arrow
(params/ret/blk) keyed in the table, consumed by `sigOf`/`superDecl?`/`DeclsOk`
and every preservation lemma; re-representing it buys no expressiveness and
re-opens every proof that cases on rows. The future consumer that *does* want an
arrow from a row is `method(:f)`/`&method(:f)` reification — that is one Judge
rule minting `arrowOf d.params d.ret` from the resolved row when the corpus
demands it, not a representation change.

## J18 — `SubJ` was not transitive; `nilableR` repairs it

Found while pricing the machine-typing layer (`judgment-layer.md` J1), where
`SubJ.trans` is load-bearing (the invariant's subsumption slack composes at every
delivery): `int ≤ int ∪ bool` (unionR1) and `int ∪ bool ≤ nilable (int ∪ bool)`
(base, `subTy`'s reflexive third disjunct) compose to a judgment with **no
derivation** — `base` computes to a false equality, `unionR` needs a union on the
right, `nilableL` a nilable on the left. The missing rule is the nilable-**right**
lift `SubJ σ τ → SubJ σ (nilable τ)`: semantically free (`nilable τ` ⊇ `τ`) and a
strict widening, so every existing derivation and example stands.

With it, `SubJ.trans` closes by strong induction on the summed sizes of the three
types (`Sub.lean`): structural rules recurse on smaller types; a `base` step
against a structural one is decided by `subTy_cases`; the previously-underivable
compositions all land in exactly the `nilableR` constructor. Also added:
`SubJs.trans`/`SubJs.length`, and the **fuel-based** algorithmic form
`subJb`/`subJsb` with soundness only — fuel rather than well-founded recursion by
the L73 discipline (the J2 `Deriv.check` will run it under `decide`), and no
completeness theorem because the checker only ever consumes the sound direction.

## J19 — `VTy`: the value judgment, `SubJ`-closed over an untouched `ValueTy`

J14's named bill ("`ValueTy` has no union disjunction arm") is paid without
touching `ValueTy`: `VTy h v τ := ∃ σ, ValueTy h v σ ∧ SubJ σ τ`
(`Proof/Judgment/Values.lean`). Weakening is `SubJ.trans`, heap transport is
`ValueTy.congr`, and the machine-typing layer will state every value obligation
over `VTy`. The load-bearing bridge is **`VTy.toValueTy`** at a `groundTy`
(union- and arrow-free) type — `valueTy_subJ`, by induction on the `SubJ`
derivation, with `ValueTy`-at-union proved uninhabited (`valueTy?_ground`: the
exact-type function's whole range is ground) and nilables decomposed by a
side-condition-free `valueTy_nilable_cases`. Since `sigOf` answers only at ground
receiver types and every declared row is ground, the dispatch lemmas of
`Proof/Static/` will be consumed **unchanged** — the send cases convert `VTy` →
`ValueTy` at the boundary and proceed as the old proof does. Arrows deliberately
have no value witness yet (J16's bill, position unchanged): the J1 fragment
excludes the lambda-arrow mint, so no reachable value needs one.

## J20 — `MFrag`, the machine-typed fragment gate, and the J-spine's definitions

The invariant's eval arm quantifies existentially over derivations, so inversion at
a head surfaces every rule whose conclusion matches — admitting a head into machine
typing drags in all its rules' preservation cases at once. The boundary is
therefore **syntactic**: `MFrag` (`Judgment/Frag.lean`, an inductive for `cases` +
a fuel `mfragB` for the J2 checker), conjoined into `CtlOkJ`'s eval arm — the role
`infer`'s partiality played for the old spine. Two shape conditions inside admitted
heads are deliberate: an `if` on a bare local read is out until the narrowing rung
(its delivery needs the value↔store correlation; the push-time case-split design is
in `Proof/Judgment/DESIGN-NOTES.md`), and `call`-named sends stay out because no
machine-typed value witnesses an arrow (J19).

The spine itself (`Proof/Judgment/{Frames,Decls,Konts}.lean`) transliterates
`FrameConforms`/`FramesOk`, `UserConforms`/`EntryOk`/`DeclsOk`, and
`KontOk`/`CtlOk`/`Inv` with three systematic changes: `infer*` premises become
`Judge*` derivations plus the stored program's `MFrag` facts; `subTy`/`ValueTy`
become `SubJ`/`VTy`; the context is `JCtx`, read by the untouched `StackCtx`
through `.toFrameCtx`. Heap conjuncts, `GlobalsOk`, the frames/array layer, and all
dispatch lemmas are consumed by import. One correction surfaced by the delivery
cases: `ifNoneK` must pin the branch's exit table to its own (as `Judge.ifNone`
does) — the elseless `if`'s falsy path delivers `nil` at the *registration* table.

## J21 — rung-1 preservation, and the induction pattern that makes `sub` free

`step_okJ` (`Proof/Judgment/Preservation.lean`) over the T1 control core: literals,
locals, `seq`, `if`, `while`. The eval branch is **one induction over the
derivation** — `Judge.rec` applied by `refine` with the ten auxiliary motives
trivial and named holes per constructor (`induction … using Judge.rec` fails on
mutual inductives; the `refine`-with-92-holes form works). Each constructor case is
that head's preservation argument; the `sub` case composes the invariant's slack by
`SubJ.trans`/`SubEnv.trans` **once, for every head** — three lines, where the old
spine's twenty Mono laws and motive maps lived. Out-of-fragment constructors are
refuted by a single `all_goals … cases hmf` sweep.

`Proof/Judgment/Sound.lean` composes: `initiationJ` (boot facts of
`initiation_ctl`, control clause from a derivation), `consecutionJ`/`safetyJ`, and
the headline

    judge_sound : DeclsOkJ F Boot.initHeap → MFrag p →
      Judge F [] p true topJCtx τ Γ' D' →
      ∀ r, ReachableResult (Machine.init p) r → ¬ typeStuck r

axiom-clean, **no checker in the statement**. `tableOk_declsOkJ` converts the boot
table's witness (its user arm refuted by walking `baseDecls`), and `egIf` is
re-certified end-to-end from a seven-line hand derivation — the first program whose
safety theorem goes through the judgment layer.

## J22 — sends machine-typed: dispatch through the `VTy`→`ValueTy` boundary

The fragment (J20) grows `self'`, `vcall`, and block-less sends (explicit and
implicit receiver, any arity) — with two shape gates: no `call`-named explicit send
(the arrow eliminator, J19's bill) and no `splat`/`kwargs`/`fwd` argument (their
own kont path; the shape facts are read *off `MFrag`* where the old proof read them
off `infer`'s refusal). `KontOkJ` gains `recvK`/`recvK0`/`argsK`/`frameK`;
`argsK` stores `VTy`/`VTys` facts, so `heap_congr'` gains its first real content.

The dispatch boundary is one lemma: **`sigOf` answers only at ground receiver
types** (`sigOf_ground` — `tyClassNames` is `[]` at unions and arrows, and a
nilable's payload is pinned by its own row), so `sigOf_vty_atomic` collapses the
widened receiver judgment back to `ValueTy` and `entry_dispatch`/`user_dispatch`
are consumed **unchanged**. Argument lists convert by `VTys.toValuesTy` under a new
sixth `DeclsOkJ` conjunct — declared parameters are ground — which is heap-free
(rides every transport untouched) and honest: a union-parameter row is
unwitnessable by a `ValueTy`-based conformance anyway. The user arm's dispatch
pushes the activation with the body's `Judge` derivation and `MFrag` fact carried
by `UserConformsJ`, and `frameK`'s return agreement is `SubJ`-shaped.

`egZero` (`(1 + 2).zero?`) is certified end to end — the first builtin dispatch
through the judgment layer, axiom-clean.

## J23 — `def`/`class` machine-typed: table growth through `judge_mono`

The fragment gains `def'` (any params — the step is uniform; the *body* gate is
what `defPromote`'s installed row needs) and toplevel `class'` reopens. The new
proof content is **table monotonicity** (`Proof/Judgment/Mono.lean`): `Judge`'s
own rule set is *not* monotone in the table (`alias'`/`defDecl`/`defPromote` carry
negative `declaresName` premises; the definition heads thread tables), but every
rule reachable at an `MFrag ∧ defFree` expression reads the table only through
`sigOf`, which `SubDecls` preserves — so `judge_mono` holds exactly over the gated
fragment, by the same `Judge.rec` pattern, with the definition heads refuted by the
`defFree` gate and everything else by `MFrag`. That is `infer_mono`'s role
(§10.5a's port tax) re-priced at one induction with two gate hypotheses the
conformance predicate already carries.

Transports mirror cleanly: `EntryOkJ_mono` (user arm re-judges by `judge_mono`),
`DeclsOkJ_of_subDecls`, `DeclsOkJ_defineMethod`, `DeclsOkJ_addRow_here` — the last
via `declFor_addRow_self_inv`, with the new row's key pinned to `.cls ctx.cls` by
the promotion rule's own ground-name guard. The `defPromote` preservation case
composes them: heap write first (`DeclsOkJ_defineMethod`), then the row
(`DeclsOkJ_addRow_here`) with a `UserEntryOkJ` witness whose body derivation is
the rule's own premise transported by `judge_mono`.

End-to-end: `egUserCall` (reopen + promote + user-method dispatch — the T5
`class_hierarchy` shape) and `egVcall` (receiverless user call through two threaded
rows) are certified through the judgment layer, axiom-clean.

## J24 — the composed certificate theorem: J1's exit, delivered

`Proof/Judgment/Cert.lean`:

    judge_sound_cert : rowsGuarded (declsOf p) c.deltaRows →
      (∀ r ∈ c.deltaRows, EntryOkJ (c.table p) Boot.initHeap (nomTy r.cls) r.name r.sig) →
      (claimed params ground) → MFrag p →
      Judge (c.table p) [] p true topJCtx τ Γ' D' →
      ∀ r, ReachableResult (Machine.init p) r → ¬ typeStuck r

— `validate_sound_of_ctl` with the open `hctl` premise's *supplier replaced*: the
control clause is a derivation, and the statement mentions no checker at all
(judgment-layer.md §5's re-scoping, cashed). The certificate's table half
(`declsOkJ_table`) consumes `Bridge.lean`'s fold/guard lemmas unchanged through
`DeclsOkJ_of_subDecls`; the residue is one `EntryOkJ` per claimed row, and a
discharged old-style residue is a J-residue verbatim (the builtin arm is shared).

`egEven` — `1.even?` under a claimed `Integer#even? : () → Boolean` row — is
certified **unconditionally**, axiom-clean: the `egEven_certified` corollary C-1
was parked on, delivered through the judgment instead of through a `chk` port.
`check-proofs.sh` audits `judge_sound`, `judge_sound_cert`, `step_okJ`,
`judge_mono`, and the two worked ends.

## J25 — `Deriv`: the certificate is a derivation, checked by one kernel `Bool`

J2, built (`Judgment/Check.lean`, `Judgment/Json.lean`,
`Proof/Judgment/Adequacy.lean`). Design points against §4(3) of the design
artifact:

* **Nodes mirror rules; only choices are fields.** A `Deriv` node records what a
  checker cannot recompute (join bounds, continuation environments, loop-head
  stackmaps, declared signatures); the deterministic data (environments, tables)
  is threaded by `check`, which is fuel-recursive (the L73 discipline — the whole
  point is that certificate checking is a `decide`) with side conditions as
  `subJb`/`subEnvB`/`mfragB` reads. `defFree` needed a fuel twin (`defFreeB`) for
  the same reason — the well-founded original does not kernel-reduce.
* **Adequacy is one induction** (`check_sound_all`): fuel-induct, case per node,
  each "split the side conditions, apply the constructor". Two tactic potholes,
  both now recorded: the C-1 handoff's `absurd h (by simp)` trap re-bitten inside
  `try` (use `simp at h; done`), and `split at h` walking *into* an inline
  shape-`match` in an `if` condition — 47 cases instead of 2 — fixed by naming the
  gate (`notBareLvar`) so the scrutinee is opaque.
* **The composed pipeline**: `validateJ` (row guards + ground params + fragment
  gate + checked derivation) and `validateJ_certifies`, with the claimed rows'
  residue as the one honest hypothesis. `egEven` (claimed row) and `egUserCall`
  (class body, promoted row, user dispatch — the T5 shape) are certified from
  **literal certificate data under `decide`**, axiom-clean.
* **The wire format** (`Judgment/Json.lean`): node kinds mirror constructors;
  `Ty`/`RowClaim` reuse the C-ladder codecs, so a J-certificate's rows section is
  byte-compatible with `delta_rows`. Binary `--certify` wiring deliberately waits
  for an emitter to feed it (the initiative's stated exclusion).
