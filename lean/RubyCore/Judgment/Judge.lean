import RubyCore.Judgment.Sub

/-!
# `Judge` — the declarative typing judgment (the definition of record)

`docs/semantics/judgment-layer.md` **J0**: the flow-sensitive expression typing as an
**inductive `Prop`**, mirroring how `Step m m'` renders `stepFn`. This is the layer the
metatheory is meant to be stated over — `chk`/`infer` become decision procedures to be
related to it by one-directional lemmas, never the other way around (§0 of the design
artifact: metatheory stated over a *function* is re-incurred at every checker rewrite).

## Reading the judgment

`Judge A D Γ e top ctx τ Γ' D'` — under declaration table `D`, local environment `Γ`,
toplevel-position flag `top` and activation context `ctx`, expression `e` has type `τ`
and leaves `Γ'` and `D'` in force. The argument order is `chk`'s
(`chk c n D Γ e top ctx = some (τ, Γ', D')`) so the eventual adequacy lemma is a
statement about two things with the same shape.

**Claims become derivation content.** Everywhere `chk` consults the certificate
(`claimTy`/`claimEnv`/`claimTys`), the corresponding rule here simply *quantifies over
the choice* — a join bound `τj`, a continuation environment `Γc`, a declared signature
`(τs, σ, bs)`. The derivation records the choice; there is no claim table and no
deterministic-vs-claimed split (`joinTy` disappears: one rule with an upper-bound
premise subsumes both of `chk`'s paths). Assumed *rows* do not appear as rules at all:
an asserted signature is a row in `D`, carried by the certificate's table half and
visible in the residue — which is why this file has no analogue of `chk`'s
claim-fallback arms on `send`/`vcall`/`const`.

## Coverage

Every one of the 47 `Expr` constructors is accounted for: 44 have rules; **3 are
deliberate refusals** (no constructor), each for a stated reason:

* `.block` / `.blockpass` outside a send's `blk` slot — not values the machine ever
  evaluates; the send rules consume them in place (`chk` refuses them too).
* `.undef` — removes a row from the definee, and a table with no notion of removal
  cannot state a sound rule. (`chk` covers it claim-gated, i.e. trust-carrying; the
  spec refuses instead. See `implementation-notes.md` J11.)

Two rules are **assumption rules** (marked `[ASSM]` below): their chosen type is
checked against nothing in this file and must be discharged by a machine-typing
conjunct at the preservation milestone (J1), exactly as `ivarTy?` rows are discharged
by heap conformance. Both are class variables — the one namespace `Decls` has no
channel for.

One rule family carries a **[SOUNDNESS-OPEN]** flag (`begin'`): handlers are typed at
the region's entry environment, which is not guaranteed at a mid-body raise point if
the body has *retyped* a local before raising. Transcribed from `chk` deliberately so
the question surfaces at J1 preservation rather than being silently patched here; the
candidate fixes are listed at the rule.

Deviations from `chk`, each recorded in `implementation-notes.md`:
* loop stability is *containment* (`SubEnv Γl ·`), not environment equality, and a
  loop's exit environment is the loop invariant `Γl`, not the entry `Γ` (J6);
* `redo'` carries the `SubEnv Γl Γ` premise `nxt` has and `chk`'s `redo'` arm lacks
  (J7 — flagged as a possible gap in `chk`'s coverage tier);
* `def` with a chosen declaration checks `declaresName D name = false`, which `chk`'s
  claimed arm does not (J9);
* the `if` join is one rule with a chosen upper bound and a chosen continuation
  environment below *both* branch exits — strictly the sound form of `chk`'s
  unchecked `claimEnv` (J3).
-/

namespace RubyCore.Judgment

open RubyCore.Types

/-! ## 1. `JCtx` — the activation context, with the two channels `chk` lacked

`FrameCtx`'s six channels are reused by extension (no copy — their docstrings in
`Types/Ty.lean` remain the reference). The judgment adds exactly two, each unlocking
an arm `chk` could only cover claim-gated:

* **`blk`** — the enclosing method's declared block signature, or `none` where there
  is no enclosing method or its row declares no block. Set by the `def`/`defs` rules
  from the chosen declaration; read by exactly one rule, `yield'`, which becomes
  sound instead of claimed. Cleared on entering a block body (a `yield` inside a
  block forwards to the *home* method's block, a pairing this context cannot see —
  same refusal as `blockCtx`'s other channels).
* **`inRescue`** — are we lexically inside a `rescue` handler? Read by exactly one
  rule, `retry'`, whose target is the handler's region. Set by `JudgeRescues` on the
  handler body; cleared on entering a method, block, or class body. -/
structure JCtx extends FrameCtx where
  blk : Option BlockSig := none
  inRescue : Bool := false
deriving DecidableEq, Repr, Inhabited

/-- The context a block body is judged in: `blockCtx`'s closures (see its docstring
    in `Types/Decls.lean`), plus the two new channels closed — no `yield`, no `retry`
    from inside a block, for the pairing reason above. -/
def jBlockCtx (ctx : JCtx) : JCtx :=
  { toFrameCtx := blockCtx ctx.toFrameCtx, blk := none, inRescue := false }

/-- The context a method body is judged in (the `def` rules' channel settings,
    `chk`'s to the letter, plus the chosen block signature opened and `inRescue`
    closed). `ret` is an `Option` because the promoted-nullary rule types the body
    with **no** return target, as `chk`'s deterministic arm does. -/
def methodCtx (ctx : JCtx) (name : String) (τs : List Ty) (ret : Option Ty)
    (bs : Option BlockSig) : JCtx :=
  { ctx with selfCls := some ctx.cls, ret := ret, meth := some name,
             params := some τs, inLoop := none, inBlock := false,
             inClassBody := false, inModuleBody := false, blk := bs, inRescue := false }

/-- The context a singleton-method (`defs`) body is judged in: `methodCtx` with
    `selfCls := none` — `self` is the receiver object, which the type language
    cannot name (`chk`'s `defs` arm, unchanged). -/
def singletonCtx (ctx : JCtx) (name : String) (τs : List Ty) (ret : Option Ty)
    (bs : Option BlockSig) : JCtx :=
  { methodCtx ctx name τs ret bs with selfCls := none }

/-- Inside a loop whose head environment (stackmap) is `Γl`. -/
def loopCtx (ctx : JCtx) (Γl : Env) : JCtx := { ctx with inLoop := some Γl }

/-- Inside a `rescue` handler body. -/
def rescueCtx (ctx : JCtx) : JCtx := { ctx with inRescue := true }

/-! ## 2. Binding forms

Non-fuel spellings (a `Prop` needs no kernel reduction, so the judgment states the
recursion directly). `Cert/CheckAux.lean` carries the fuel spellings for `chk`; the
two are to be related by an equivalence lemma when the adequacy work lands (J10 —
the `defFree`/`defFreeF` precedent, paid the same way). -/

mutual
/-- Every name a parameter binds, transitively through destructuring. -/
def paramNames : Param → List String
  | .req x => [x]
  | .opt x _ => [x]
  | .rest xo => xo.toList
  | .key x _ => [x]
  | .kwrest xo => xo.toList
  | .block xo => xo.toList
  | .fwd => []
  | .destr subs => paramNamesList subs
termination_by p => sizeOf p

def paramNamesList : List Param → List String
  | [] => []
  | p :: ps => paramNames p ++ paramNamesList ps
termination_by ps => sizeOf ps
end

/-- Bind a list of names at `.any`. -/
def bindAllAny (xs : List String) (Γ : Env) : Env :=
  xs.foldl (fun Γ x => envSet Γ x .any) Γ

/-- Bind a parameter list at the chosen declared types, in order —
    `Cert.bindParams` without the fuel. A parameter kind with no declared type
    (rest, keyword-rest, block capture, forward) binds at `.any`; a destructuring
    parameter binds its transitive names at `.any` (the type language has no tuple). -/
def bindParamsJ : List Param → List Ty → Env → Env
  | [], _, Γ => Γ
  | p :: ps, τs, Γ =>
    match p, τs with
    | .req x, τ :: τs' => bindParamsJ ps τs' (envSet Γ x τ)
    | .req x, [] => bindParamsJ ps [] (envSet Γ x .any)
    | .opt x _, τ :: τs' => bindParamsJ ps τs' (envSet Γ x τ)
    | .opt x _, [] => bindParamsJ ps [] (envSet Γ x .any)
    | .key x _, τ :: τs' => bindParamsJ ps τs' (envSet Γ x τ)
    | .key x _, [] => bindParamsJ ps [] (envSet Γ x .any)
    | .rest (some x), _ => bindParamsJ ps τs (envSet Γ x .any)
    | .rest none, _ => bindParamsJ ps τs Γ
    | .kwrest (some x), _ => bindParamsJ ps τs (envSet Γ x .any)
    | .kwrest none, _ => bindParamsJ ps τs Γ
    | .block (some x), _ => bindParamsJ ps τs (envSet Γ x .any)
    | .block none, _ => bindParamsJ ps τs Γ
    | .fwd, _ => bindParamsJ ps τs Γ
    | .destr subs, _ => bindParamsJ ps τs (bindAllAny (paramNamesList subs) Γ)

/-- The names a `for` loop's targets bind — in the **enclosing** scope (a `for`
    pushes no frame; the loop variable leaks [V]). `Cert.bindTargets`, no fuel. -/
def bindTargetsJ : List (TargetKind × String) → Ty → Env → Env
  | [], _, Γ => Γ
  | (_, x) :: rest, τ, Γ => bindTargetsJ rest τ (envSet Γ x τ)

/-! ## 3. Semantic axioms (J31)

A **semantic axiom set** `A` is a list of expressions the certificate *claims*
semantically: each claimed `e` is admitted by `Judge.semantic` at the canonical
judgment — type `.any`, environment- and table-preserving — with the claim's
*meaning* (running `e` from any conformant state is type-safe and delivers a
value, at any environment, leaving it intact) discharged in the proof layer
(`Proof/Judgment/Preservation.lean`'s `SemAxiomsOk`, one `EvalOkAt` obligation
per claim). The canonical indices are what make a claim *compositional*: they
are the one judgment shape whose embedding needs no coordination with the
surrounding derivation (see the `JudgeSeq` coupling premises below).

Claims are gated to **out-of-fragment heads** (`fragHead e = false`): an
in-fragment head already has syntactic rules and machine-typing cases, and
admitting a second, semantic route for the same expression is what creates the
mixed states preservation cannot discharge (J31's design note). -/

/-- Does `e`'s **head** (one level, no recursion) belong to the machine-typed
    fragment's shape universe? Mirrors `mfragB`'s top-level patterns exactly —
    each syntactic `MFrag` constructor concludes at a `fragHead`-true shape, which
    is the disjointness the semantic arm's gate rests on. -/
def fragHead : Expr → Bool
  | .int _ | .flt _ | .str _ | .sym _ | .tru | .fls | .nil => true
  | .var .lvar _ | .var .ivar _ | .var .gvar _ => true
  | .vasgn .lvar _ _ | .vasgn .ivar _ _ | .vasgn .gvar _ _ => true
  | .seq _ => true
  | .if' _ _ _ => true
  | .while' _ _ => true
  | .self' => true
  | .vcall _ => true
  | .send _ _ _ none => true
  | .def' _ _ _ => true
  | .class' _ none _ => true
  | .const _ => true
  | .cpath _ _ => true
  | .ret _ => true
  | .hash _ => true
  | .casgn _ _ => true
  | .array _ => true
  -- The four *marker* shapes are not evaluable expressions (they occur only as
  -- argument/element/block slots of other heads), so a semantic claim on one has
  -- no eval-position meaning — `fragHead` counts them in the syntactic universe,
  -- which makes them unclaimable (and they stay out of `MFrag` by having no
  -- constructor, as before).
  | .splat _ => true
  | .kwargs _ => true
  | .block _ _ _ => true
  | .blockpass _ => true
  | .fwd => true
  | _ => false

/-- **One semantic claim (J32)**: an out-of-fragment expression judged at a
    *claimed type* `τ`, environment-preserving, whose evaluation may install the
    *claimed rows* into the table — the channel by which runtime-generated methods
    (`define_method`, the Rails shape) become dispatchable, mirroring
    `defPromote`'s row threading. `rows := []`, `τ := .any` recovers the J31
    canonical claim. -/
structure SemClaim where
  e : Expr
  τ : Ty := .any
  rows : List (String × String × MethodDecl) := []
  /-- **The claim's context condition (J35)**: `some cn` restricts the claim to
      class-body position in a reopen of `cn` (the `inClassBody`/`inBlock`
      channels + the class name), which is what pins the implicit receiver to
      *the class object named `cn`* — the fact the `define_method` obligation
      reads through `StackCtx`'s J34 clause. `none` = position-free. -/
  reqCls : Option String := none
deriving Repr

/-- The semantic axiom set. -/
abbrev SemAxioms := List SemClaim

/-- A claim's table effect. -/
def addRows (D : Decls) (rows : List (String × String × MethodDecl)) : Decls :=
  rows.foldl (fun D r => addRow D r.1 r.2.1 r.2.2) D

/-! ## 4. The judgment -/

mutual

/-- An optional subterm: judged if present; `nil` and the incoming environment and
    table if absent. -/
inductive JudgeOpt (A : SemAxioms) : Decls → Env → Option Expr → Bool → JCtx → Ty → Env → Decls → Prop where
  | none {D Γ top ctx} : JudgeOpt A D Γ none top ctx .nilT Γ D
  | some {D Γ e top ctx τ Γ' D'} :
      Judge A D Γ e top ctx τ Γ' D' → JudgeOpt A D Γ (some e) top ctx τ Γ' D'

/-- The receiver of a send: explicit receivers are judged; an implicit receiver is
    `self`, which has a type only where it is an *instance* (`chkRecv`). -/
inductive JudgeRecv (A : SemAxioms) : Decls → Env → Option Expr → Bool → JCtx → Ty → Env → Decls → Prop where
  | self {D Γ top ctx cc} :
      ctx.selfCls = some cc → JudgeRecv A D Γ none top ctx (.cls cc) Γ D
  | expl {D Γ r top ctx τ Γ' D'} :
      Judge A D Γ r top ctx τ Γ' D' → JudgeRecv A D Γ (some r) top ctx τ Γ' D'

/-- A statement sequence: thread the environment and the table, take the last type.
    Empty is `nil`; `[e]` is `e` (the three-way split `evalExpr` makes). -/
inductive JudgeSeq (A : SemAxioms) : Decls → Env → List Expr → Bool → JCtx → Ty → Env → Decls → Prop where
  | nil {D Γ top ctx} : JudgeSeq A D Γ [] top ctx .nilT Γ D
  | single {D Γ e top ctx τ Γ' D'} :
      Judge A D Γ e top ctx τ Γ' D' →
      (hcpl : fragHead e = false → ∃ cl ∈ A, cl.e = e ∧ τ = cl.τ ∧ Γ' = Γ ∧
          D' = addRows D cl.rows ∧ (cl.rows = [] ∨ ctx.meth = none) ∧
          (∀ cn, cl.reqCls = some cn →
            ctx.cls = cn ∧ ctx.inClassBody = true ∧ ctx.inBlock = false) ∧
          (∀ r ∈ cl.rows, declaresName D r.2.1 = false) :=
        by intro hh; simp [fragHead] at hh) →
      JudgeSeq A D Γ [e] top ctx τ Γ' D'
  | cons {D Γ e e₂ rest top ctx τ₁ Γ₁ D₁ τ Γ' D'} :
      Judge A D Γ e top ctx τ₁ Γ₁ D₁ →
      JudgeSeq A D₁ Γ₁ (e₂ :: rest) top ctx τ Γ' D' →
      (hcpl : fragHead e = false → ∃ cl ∈ A, cl.e = e ∧ τ₁ = cl.τ ∧ Γ₁ = Γ ∧
          D₁ = addRows D cl.rows ∧ (cl.rows = [] ∨ ctx.meth = none) ∧
          (∀ cn, cl.reqCls = some cn →
            ctx.cls = cn ∧ ctx.inClassBody = true ∧ ctx.inBlock = false) ∧
          (∀ r ∈ cl.rows, declaresName D r.2.1 = false) :=
        by intro hh; simp [fragHead] at hh) →
      JudgeSeq A D Γ (e :: e₂ :: rest) top ctx τ Γ' D'

/-- An argument list: the same threading, types kept in order (matched against a
    signature's parameter list). -/
inductive JudgeArgs (A : SemAxioms) : Decls → Env → List Expr → Bool → JCtx → List Ty → Env → Decls → Prop where
  | nil {D Γ top ctx} : JudgeArgs A D Γ [] top ctx [] Γ D
  | cons {D Γ e rest top ctx τ Γ₁ D₁ τs Γ' D'} :
      Judge A D Γ e top ctx τ Γ₁ D₁ →
      JudgeArgs A D₁ Γ₁ rest top ctx τs Γ' D' →
      JudgeArgs A D Γ (e :: rest) top ctx (τ :: τs) Γ' D'

/-- The elements of an array literal: element types erased. A `.splat` element goes
    through `Judge`'s own splat rules, which demand an Array-shaped operand — where
    `chkElems` special-cases `.cls "Array"` inline, the relation just recurses
    (J12: this admits an `.arrayOf` splat `chkElems` refuses; sound, an `arrayOf`
    *is* an Array). -/
inductive JudgeElems (A : SemAxioms) : Decls → Env → List Expr → Bool → JCtx → Env → Decls → Prop where
  | nil {D Γ top ctx} : JudgeElems A D Γ [] top ctx Γ D
  | cons {D Γ e rest top ctx τ Γ₁ D₁ Γ' D'} :
      Judge A D Γ e top ctx τ Γ₁ D₁ →
      JudgeElems A D₁ Γ₁ rest top ctx Γ' D' →
      JudgeElems A D Γ (e :: rest) top ctx Γ' D'

/-- The pairs of a hash literal — key then value, left to right. -/
inductive JudgePairs (A : SemAxioms) : Decls → Env → List (Expr × Expr) → Bool → JCtx → Env → Decls → Prop where
  | nil {D Γ top ctx} : JudgePairs A D Γ [] top ctx Γ D
  | cons {D Γ k v rest top ctx τk Γ₁ D₁ τv Γ₂ D₂ Γ' D'} :
      Judge A D Γ k top ctx τk Γ₁ D₁ →
      Judge A D₁ Γ₁ v top ctx τv Γ₂ D₂ →
      JudgePairs A D₂ Γ₂ rest top ctx Γ' D' →
      JudgePairs A D Γ ((k, v) :: rest) top ctx Γ' D'

/-- The entries of a brace-less keyword-argument marker: each value is judged; a
    `.dyn` entry's key is too. -/
inductive JudgeKwEntries (A : SemAxioms) : Decls → Env → List KwEntry → Bool → JCtx → Env → Decls → Prop where
  | nil {D Γ top ctx} : JudgeKwEntries A D Γ [] top ctx Γ D
  | pair {D Γ k v rest top ctx τ Γ₁ D₁ Γ' D'} :
      Judge A D Γ v top ctx τ Γ₁ D₁ →
      JudgeKwEntries A D₁ Γ₁ rest top ctx Γ' D' →
      JudgeKwEntries A D Γ (.pair k v :: rest) top ctx Γ' D'
  | splat {D Γ v rest top ctx τ Γ₁ D₁ Γ' D'} :
      Judge A D Γ v top ctx τ Γ₁ D₁ →
      JudgeKwEntries A D₁ Γ₁ rest top ctx Γ' D' →
      JudgeKwEntries A D Γ (.splat v :: rest) top ctx Γ' D'
  | dyn {D Γ k v rest top ctx τk Γ₁ D₁ τv Γ₂ D₂ Γ' D'} :
      Judge A D Γ k top ctx τk Γ₁ D₁ →
      Judge A D₁ Γ₁ v top ctx τv Γ₂ D₂ →
      JudgeKwEntries A D₂ Γ₂ rest top ctx Γ' D' →
      JudgeKwEntries A D Γ (.dyn k v :: rest) top ctx Γ' D'

/-- The handlers of a `begin` region, each judged at the region's **entry**
    environment (see the [SOUNDNESS-OPEN] flag at the `begin'` rule), with
    `inRescue` set (that is `retry'`'s license), the table pinned, and each
    handler's exit environment dropped. The bound exception's type is the sole
    named class where there is exactly one, `.any` otherwise — a multi-class
    binding needs the union the type language does not have. -/
inductive JudgeRescues (A : SemAxioms) : Decls → Env → Bool → JCtx →
    List (List Expr × Option (TargetKind × String) × Expr) → List Ty → Prop where
  | nil {D Γ top ctx} : JudgeRescues A D Γ top ctx [] []
  | cons {D Γ top ctx excs tgt hbody rest τs Γx τx Γh τh Γh' τrs} :
      JudgeArgs A D Γ excs top ctx τs Γx D →
      τx = (match τs with | [.clsOf n] => .cls n | _ => .any) →
      Γh = (match tgt with | some (_, x) => envSet Γ x τx | none => Γ) →
      Judge A D Γh hbody top (rescueCtx ctx) τh Γh' D →
      JudgeRescues A D Γ top ctx rest τrs →
      JudgeRescues A D Γ top ctx ((excs, tgt, hbody) :: rest) (τh :: τrs)

/-- The `else` clause of a `begin` region: its type **replaces** the body's where
    present (CRuby: `else` runs only on a no-raise exit and its value is the
    region's). -/
inductive JudgeElse (A : SemAxioms) : Decls → Env → Option Expr → Bool → JCtx → Ty → Ty → Prop where
  | none {D Γ top ctx τb} : JudgeElse A D Γ none top ctx τb τb
  | some {D Γ el top ctx τb τl Γl' } :
      Judge A D Γ el top ctx τl Γl' D → JudgeElse A D Γ (some el) top ctx τb τl

/-- The `ensure` clause: judged for well-typedness, value discarded, table pinned. -/
inductive JudgeEns (A : SemAxioms) : Decls → Env → Option Expr → Bool → JCtx → Prop where
  | none {D Γ top ctx} : JudgeEns A D Γ none top ctx
  | some {D Γ en top ctx τ Γ'} :
      Judge A D Γ en top ctx τ Γ' D → JudgeEns A D Γ (some en) top ctx

/-- **The judgment.** `Judge A D Γ e top ctx τ Γ' D'` — see the module docstring for
    the reading and for what is a deliberate deviation from `chk`. Rules appear in
    the order the grammar declares its heads, so a missing head is visible as a gap
    in the reading. -/
inductive Judge (A : SemAxioms) : Decls → Env → Expr → Bool → JCtx → Ty → Env → Decls → Prop where
  -- ## Literals — derived, each one `evalExpr`'s own answer.
  | int {D Γ n top ctx} : Judge A D Γ (.int n) top ctx .int Γ D
  | flt {D Γ x top ctx} : Judge A D Γ (.flt x) top ctx .float Γ D
  | str {D Γ s top ctx} : Judge A D Γ (.str s) top ctx (.cls "String") Γ D
  | sym {D Γ s top ctx} : Judge A D Γ (.sym s) top ctx .sym Γ D
  | tru {D Γ top ctx} : Judge A D Γ .tru top ctx .bool Γ D
  | fls {D Γ top ctx} : Judge A D Γ .fls top ctx .bool Γ D
  | nil {D Γ top ctx} : Judge A D Γ .nil top ctx .nilT Γ D
  -- `self` has a type only where it is an *instance*; in a class body it is the
  -- class object (a `.clsOf ctx.cls` rule is a candidate widening — refused for
  -- now because at toplevel `self` is `main`, an Object *instance*, and `top`'s
  -- threading does not pin the two cases apart yet; J11).
  | self {D Γ top ctx cc} :
      ctx.selfCls = some cc → Judge A D Γ .self' top ctx (.cls cc) Γ D
  -- ## Variable reads.
  | varLvar {D Γ x top ctx τ} :
      envGet? Γ x = some τ → Judge A D Γ (.var .lvar x) top ctx τ Γ D
  -- An ivar read is `nil` until first write, so the declared type is nilable-lifted.
  | varIvar {D Γ x top ctx cc σ} :
      ctx.selfCls = some cc → ivarTy? D cc x = some σ →
      Judge A D Γ (.var .ivar x) top ctx (mkNilable σ) Γ D
  | varGvar {D Γ x top ctx σ} :
      plainGlobal x = true → globalTy? D x = some σ →
      Judge A D Γ (.var .gvar x) top ctx (mkNilable σ) Γ D
  -- [ASSM] Class variables have no `Decls` channel; the chosen `τ` is discharged
  -- by nothing in this file. A `cvars` field on `Decls` is the future fix (its own
  -- L-number in `Types/`); until then any derivation using this rule is
  -- assumption-carrying (J2).
  | varCvar {D Γ x top ctx} (τ : Ty) :
      Judge A D Γ (.var .cvar x) top ctx (mkNilable τ) Γ D
  -- ## Assignments. The local case refuses inside a block: a block body's write to
  -- an enclosing local is one the block frame's conformance obligation cannot see
  -- (L252) — the artifact's block-capture decision, made explicit (J11).
  | vasgnLvar {D Γ x rhs top ctx τ Γ₁ D₁} :
      ctx.inBlock = false →
      Judge A D Γ rhs top ctx τ Γ₁ D₁ →
      Judge A D Γ (.vasgn .lvar x rhs) top ctx τ (envSet Γ₁ x τ) D₁
  | vasgnIvarDecl {D Γ x rhs top ctx cc τ Γ₁ D₁ σ} :
      ctx.selfCls = some cc →
      Judge A D Γ rhs top ctx τ Γ₁ D₁ →
      ivarTy? D₁ cc x = some σ → SubJ τ σ →
      Judge A D Γ (.vasgn .ivar x rhs) top ctx τ Γ₁ D₁
  -- A write to an *undeclared* ivar is admissible: the read rule requires a row, so
  -- the written value is unreachable through the type system.
  | vasgnIvarFresh {D Γ x rhs top ctx cc τ Γ₁ D₁} :
      ctx.selfCls = some cc →
      Judge A D Γ rhs top ctx τ Γ₁ D₁ →
      ivarTy? D₁ cc x = none →
      Judge A D Γ (.vasgn .ivar x rhs) top ctx τ Γ₁ D₁
  | vasgnGvar {D Γ x rhs top ctx τ Γ₁ D₁ σ} :
      plainGlobal x = true →
      Judge A D Γ rhs top ctx τ Γ₁ D₁ →
      globalTy? D₁ x = some σ → SubJ τ σ →
      Judge A D Γ (.vasgn .gvar x rhs) top ctx τ Γ₁ D₁
  -- [ASSM] The write half of the cvar assumption pair.
  | vasgnCvar {D Γ x rhs top ctx τ Γ₁ D₁} :
      Judge A D Γ rhs top ctx τ Γ₁ D₁ →
      Judge A D Γ (.vasgn .cvar x rhs) top ctx τ Γ₁ D₁
  -- ## Constants. No claim fallback: an assumed constant is a `Decls.consts` row
  -- (deltaRows → residue), not a rule.
  | const {D Γ nm top ctx τ} :
      constTy? D nm = some τ → Judge A D Γ (.const nm) top ctx τ Γ D
  | cpathAbs {D Γ nm top ctx τ} :
      constTy? D nm = some τ → Judge A D Γ (.cpath none nm) top ctx τ Γ D
  | cpathScoped {D Γ base nm top ctx cname Γ₁ D₁ τ} :
      Judge A D Γ base top ctx (.clsOf cname) Γ₁ D₁ →
      scopedConstTy? D₁ cname nm = some τ →
      Judge A D Γ (.cpath (some base) nm) top ctx τ Γ₁ D₁
  -- A constant *write* is judged and its type is **not** installed: `Decls.consts`
  -- belongs to the certificate's table half, where the row is a visible assumption.
  -- **J41: machine-typed at the toplevel only, with three freshness guards.**
  -- The write lands on the current definee — `Object`, at the toplevel — and the
  -- three guards are exactly what the heap invariant charges: a *declared*
  -- constant's `ConstOk`/`ScopedConstOk` would be falsified by a same-name write
  -- (the first two), and `ClassOk`'s per-name read clauses by a readable one (the
  -- third). A **class-body** `casgn` additionally breaks `ClassOk`'s
  -- `NoShadowBefore` clause (the reopened class's own constant table must stay
  -- empty), so `top = true` is a soundness gate, not a convenience — widening it
  -- is a recorded bill (refine `NoShadowBefore` per-name first).
  | casgn {D Γ nm rhs top ctx τ Γ₁ D₁} :
      top = true →
      constTy? D₁ nm = none →
      (∀ cn, scopedConstTy? D₁ cn nm = none) →
      readableClasses.contains nm = false →
      -- J44: and the declared-modules clause — a same-name write at `Object`
      -- would falsify `ModuleNameOk` for a declared `("Object", nm)` pair (and
      -- `nameIfAnonymous` could mint a fake owner), so the name must be off the
      -- modules table entirely.
      (∀ pr ∈ D₁.modules, pr.2 ≠ nm) →
      Judge A D Γ rhs top ctx τ Γ₁ D₁ →
      Judge A D Γ (.casgn nm rhs) top ctx τ Γ₁ D₁
  | cpathAsgn {D Γ base nm rhs top ctx τb Γ₁ D₁ τ Γ₂ D₂} :
      JudgeOpt A D Γ base top ctx τb Γ₁ D₁ →
      Judge A D₁ Γ₁ rhs top ctx τ Γ₂ D₂ →
      Judge A D Γ (.cpathAsgn base nm rhs) top ctx τ Γ₂ D₂
  -- ## Sends.
  -- Block-less: receiver, arguments, then the signature read off the table
  -- (`sigOf` handles the nilable-receiver union internally, L260). No claim
  -- fallback — an asserted signature is a row in `D`.
  | send {D Γ recvO mname args top ctx τr Γ₁ D₁ τs Γ₂ D₂ ps τret} :
      JudgeRecv A D Γ recvO top ctx τr Γ₁ D₁ →
      JudgeArgs A D₁ Γ₁ args top ctx τs Γ₂ D₂ →
      sigOf D₂ τr mname = some (ps, τret) → SubJs τs ps →
      Judge A D Γ (.send recvO mname args none) top ctx τret Γ₂ D₂
  -- A literal-block send with no positional arguments: the row supplies the block's
  -- one parameter type, the type its body must answer, and the send's own answer.
  -- The receiver is explicit — `chk`'s implicit-receiver path here is `lambda` or a
  -- claim, and a claimed block row is a `D` row with `blk` set, consumed by this
  -- same rule (J3).
  | sendIter0 {D Γ r mname ps ls body top ctx τr Γ₁ D₁ x σp βret τret τb Γb'} :
      Judge A D Γ r top ctx τr Γ₁ D₁ →
      blockSend? D₁ τr mname ps ls = some (x, σp, βret, τret) →
      Judge A D₁ ((x, σp) :: anyEnv Γ₁) body false (jBlockCtx ctx) τb Γb' D₁ →
      SubJ τb βret →
      SubEnv ((x, σp) :: anyEnv Γ₁) Γb' →
      ctx.inBlock = false →
      Judge A D Γ (.send (some r) mname [] (some (.block ps ls body))) top ctx τret Γ₁ D₁
  -- A literal-block send with positional arguments. The table is pinned through
  -- every subcomputation, as `chk`'s four-way equality does.
  | sendIterA {D Γ recvO mname a as ps ls body top ctx τr Γ₁ τs Γ₂ x σp βret dps τret τb Γb'} :
      JudgeRecv A D Γ recvO top ctx τr Γ₁ D →
      JudgeArgs A D Γ₁ (a :: as) top ctx τs Γ₂ D →
      blockSendA? D τr mname ps ls = some (x, σp, βret, dps, τret) →
      Judge A D ((x, σp) :: anyEnv Γ₂) body false (jBlockCtx ctx) τb Γb' D →
      SubJs τs dps → SubJ τb βret →
      SubEnv ((x, σp) :: anyEnv Γ₂) Γb' →
      ctx.inBlock = false →
      Judge A D Γ (.send recvO mname (a :: as) (some (.block ps ls body))) top ctx τret Γ₂ D
  -- An implicit-self `lambda { … }`, **opaque**: answers `.any` — the body is
  -- deliberately unjudged (`chk`, transcribed), sound because an `.any`-typed
  -- value is unusable, so typed code can never invoke it.
  | sendLambda {D Γ ps ls body top ctx cc} :
      ctx.selfCls = some cc →
      Judge A D Γ (.send none "lambda" [] (some (.block ps ls body))) top ctx .any Γ D
  -- The same lambda, **typed at an arrow** (L270/J16): the derivation chooses the
  -- parameter types and the declared return (`defDecl`'s shape at a value), the
  -- body is judged below the return with the table pinned, and the answer is the
  -- spine. The body's context is a block's (`jBlockCtx` — enclosing locals at
  -- `.any`, writes refused, no `yield`/`retry`) **except `ret`**: a `return`
  -- inside a *lambda* returns from the lambda [V], so the return target is the
  -- arrow's own answer — the one channel where lambda and block genuinely differ.
  -- `proc {}` / `Proc.new {}` get no arrow: their `return` targets the *enclosing
  -- method* and their arity is lenient, so this rule is deliberately
  -- lambda-only (J16).
  | sendLambdaArrow {D Γ ps ls body top ctx cc τs σa τb Γb'} :
      ctx.selfCls = some cc →
      τs.length = ps.length →
      Judge A D (bindParamsJ ps τs (anyEnv Γ)) body false
        { jBlockCtx ctx with ret := some σa } τb Γb' D →
      SubJ τb σa →
      Judge A D Γ (.send none "lambda" [] (some (.block ps ls body))) top ctx
        (arrowOf τs σa) Γ D
  -- The arrow's eliminator: `.call` on an arrow-typed receiver. Args may sit below
  -- the declared parameters (`SubJs`), arity is exact by the spine's shape — which
  -- is the *lambda* arity semantics, and the intro rule above only mints arrows
  -- for lambdas. Sound alongside the row-based send rule: relations union, and a
  -- `call` row in `D` would be a claim about a different receiver type anyway
  -- (`tyClassNames` names no class for an arrow).
  | sendCall {D Γ r args top ctx τr Γ₁ D₁ τs Γ₂ D₂ ps ret} :
      Judge A D Γ r top ctx τr Γ₁ D₁ →
      arrowParts? τr = some (ps, ret) →
      JudgeArgs A D₁ Γ₁ args top ctx τs Γ₂ D₂ →
      SubJs τs ps →
      Judge A D Γ (.send (some r) "call" args none) top ctx ret Γ₂ D₂
  -- A block-pass `&e`: the operand is judged (or is the anonymous forward, `nil`
  -- via `JudgeOpt.none`), and the send types at the receiver's ordinary signature.
  | sendBlockpass {D Γ recvO mname args bo top ctx τr Γ₁ D₁ τs Γ₂ D₂ τp Γ₃ D₃ ps τret} :
      JudgeRecv A D Γ recvO top ctx τr Γ₁ D₁ →
      JudgeArgs A D₁ Γ₁ args top ctx τs Γ₂ D₂ →
      JudgeOpt A D₂ Γ₂ bo top ctx τp Γ₃ D₃ →
      sigOf D₃ τr mname = some (ps, τret) → SubJs τs ps →
      Judge A D Γ (.send recvO mname args (some (.blockpass bo))) top ctx τret Γ₃ D₃
  -- A bare identifier that is not a local: an implicit-self, zero-argument,
  -- block-less send.
  | vcall {D Γ mname top ctx cc τret} :
      ctx.selfCls = some cc →
      sigOf D (.cls cc) mname = some ([], τret) →
      Judge A D Γ (.vcall mname) top ctx τret Γ D
  -- ## Argument-position markers.
  | kwargs {D Γ entries top ctx Γ' D'} :
      JudgeKwEntries A D Γ entries top ctx Γ' D' →
      Judge A D Γ (.kwargs entries) top ctx (.cls "Hash") Γ' D'
  -- `...` forwards the enclosing method's captured arguments; there is no type for
  -- a forwarded *list*, so the marker answers `.any` and the callee's signature is
  -- what refuses it.
  | fwd {D Γ top ctx} : Judge A D Γ .fwd top ctx .any Γ D
  | splatAnon {D Γ top ctx} : Judge A D Γ (.splat none) top ctx (.cls "Array") Γ D
  | splatArray {D Γ o top ctx Γ₁ D₁} :
      Judge A D Γ o top ctx (.cls "Array") Γ₁ D₁ →
      Judge A D Γ (.splat (some o)) top ctx (.cls "Array") Γ₁ D₁
  | splatArrayOf {D Γ o top ctx τ Γ₁ D₁} :
      Judge A D Γ o top ctx (.arrayOf τ) Γ₁ D₁ →
      Judge A D Γ (.splat (some o)) top ctx (.arrayOf τ) Γ₁ D₁
  -- `yield` invokes the enclosing method's block — **sound** here, via the `blk`
  -- channel the `def` rules set from the chosen declaration (`chk` can only claim
  -- this arm; J2).
  | yield' {D Γ args top ctx τs Γ' D' bs} :
      JudgeArgs A D Γ args top ctx τs Γ' D' →
      ctx.blk = some bs → SubJs τs bs.params →
      Judge A D Γ (.yield' args) top ctx bs.ret Γ' D'
  -- ## Control flow.
  --
  -- The `if` join: **one rule**, with a chosen upper bound `τj` and a chosen
  -- continuation environment `Γc` below *both* branch exits. `chk`'s deterministic
  -- `joinTy` path is an instance (`joinTy_sub`); its claimed path is the same rule
  -- with the unchecked `claimEnv` made checked (J3). This is D1's stackmap arising
  -- as derivation content.
  | ifElse {D Γ cond t el top ctx τc Γ₁ D₁ τt Γt Dt τe Γe τj Γc} :
      Judge A D Γ cond top ctx τc Γ₁ D₁ →
      Judge A D₁ Γ₁ t top ctx τt Γt Dt →
      Judge A D₁ Γ₁ el top ctx τe Γe Dt →
      SubJ τt τj → SubJ τe τj →
      SubEnv Γc Γt → SubEnv Γc Γe →
      Judge A D Γ (.if' cond t (some el)) top ctx τj Γc Dt
  | ifNone {D Γ cond t top ctx τc Γ₁ D₁ τt Γt τj Γc} :
      Judge A D Γ cond top ctx τc Γ₁ D₁ →
      Judge A D₁ Γ₁ t top ctx τt Γt D₁ →
      SubJ τt τj → SubJ .nilT τj →
      SubEnv Γc Γt → SubEnv Γc Γ₁ →
      Judge A D Γ (.if' cond t none) top ctx τj Γc D₁
  -- **Narrowing** (T4's first rung; J5, generalized to unions at J14): a condition
  -- that is a bare local read narrows the local in **both** branches. Truthiness is
  -- the one condition the machine tests without a dispatch, so it cannot be forged
  -- the way a user-redefined `nil?` can (J15 — why there are no `nil?`-condition
  -- rules yet). Then-branch: truthy ⇒ not nil ⇒ `dropNil` (removes the nil half of
  -- a nilable or union; sound for every type, `false : bool` included). Else-branch:
  -- falsy ⇒ nil or `false`, so it narrows to `nilT` exactly when the type is
  -- `boolFree` (`elseNarrow`), and is left unchanged otherwise.
  | ifNarrowElse {D Γ x t el top ctx τ₀ τt Γt Dt τe Γe τj Γc} :
      envGet? Γ x = some τ₀ →
      Judge A D (envSet Γ x (dropNil τ₀)) t top ctx τt Γt Dt →
      Judge A D (envSet Γ x (elseNarrow τ₀)) el top ctx τe Γe Dt →
      SubJ τt τj → SubJ τe τj →
      SubEnv Γc Γt → SubEnv Γc Γe →
      Judge A D Γ (.if' (.var .lvar x) t (some el)) top ctx τj Γc Dt
  | ifNarrowNone {D Γ x t top ctx τ₀ τt Γt τj Γc} :
      envGet? Γ x = some τ₀ →
      Judge A D (envSet Γ x (dropNil τ₀)) t top ctx τt Γt D →
      SubJ τt τj → SubJ .nilT τj →
      SubEnv Γc Γt → SubEnv Γc Γ →
      Judge A D Γ (.if' (.var .lvar x) t none) top ctx τj Γc D
  -- Loops: the chosen loop-head environment `Γl` is the stackmap; the entry must
  -- guarantee it, each subcomputation's exit must re-guarantee it (containment, not
  -- `chk`'s equality — the back edge re-enters at `Γl`, which is all it needs), and
  -- the loop's own exit environment is `Γl` (not the entry `Γ`, which a widened
  -- stackmap would make unsound; J6). A `while` evaluates to `nil`.
  | while' {D Γ Γl cond body top ctx τc Γ₁ τb Γ₂} :
      SubEnv Γl Γ →
      Judge A D Γl cond top (loopCtx ctx Γl) τc Γ₁ D →
      SubEnv Γl Γ₁ →
      Judge A D Γl body top (loopCtx ctx Γl) τb Γ₂ D →
      SubEnv Γl Γ₂ →
      Judge A D Γ (.while' cond body) top ctx .nilT Γl D
  | dowhile {D Γ Γl body cond top ctx τb Γ₁ τc Γ₂} :
      SubEnv Γl Γ →
      Judge A D Γl body top (loopCtx ctx Γl) τb Γ₁ D →
      SubEnv Γl Γ₁ →
      Judge A D Γl cond top (loopCtx ctx Γl) τc Γ₂ D →
      SubEnv Γl Γ₂ →
      Judge A D Γ (.dowhile body cond) top ctx .nilT Γl D
  -- `for`: targets bind in the enclosing scope (the loop variable leaks); an
  -- `arrayOf` collection gives the element type, anything else binds at `.any`.
  -- Ruby's `for` evaluates to the collection.
  | for' {D Γ tgts coll body top ctx τc Γ₁ D₁ τe Γb τb Γ₂} :
      Judge A D Γ coll top ctx τc Γ₁ D₁ →
      τe = (match τc with | .arrayOf τ => τ | _ => .any) →
      Γb = bindTargetsJ tgts τe Γ₁ →
      Judge A D₁ Γb body top (loopCtx ctx Γb) τb Γ₂ D₁ →
      SubEnv Γb Γ₂ →
      Judge A D Γ (.for' tgts coll body) top ctx τc Γb D₁
  -- ## Jumps — each sound only where its target exists, per the context channels.
  -- J39: `ctx.meth.isSome` — a `return` fires only inside a method body (the
  -- machine's `doReturn` pops a `.method` frame; `StackCtx`'s L198/L200 clause is
  -- what turns the open channel into that frame's existence). It is also what
  -- lets `judge_table_ret` treat a row-bearing semantic claim as impossible
  -- along a returning continuation.
  | retSome {D Γ e' top ctx σ τ Γ₁ D₁} :
      ctx.ret = some σ → ctx.meth.isSome = true →
      Judge A D Γ e' top ctx τ Γ₁ D₁ → SubJ τ σ →
      Judge A D Γ (.ret (some e')) top ctx .nilT Γ₁ D₁
  | retNil {D Γ top ctx σ} :
      ctx.ret = some σ → ctx.meth.isSome = true → SubJ .nilT σ →
      Judge A D Γ (.ret none) top ctx .nilT Γ D
  -- `next` restarts the loop in the same frame: the jump point's environment must
  -- re-guarantee the loop head's.
  | nxtNil {D Γ top ctx Γl} :
      top = false → ctx.inLoop = some Γl → SubEnv Γl Γ →
      Judge A D Γ (.nxt none) top ctx .nilT Γ D
  | nxtSome {D Γ e' top ctx Γl τ Γ₁} :
      top = false → ctx.inLoop = some Γl →
      Judge A D Γ e' top ctx τ Γ₁ D → SubEnv Γl Γ₁ →
      Judge A D Γ (.nxt (some e')) top ctx .nilT Γ₁ D
  -- `break` ends the loop, so it owes nothing about the loop head's environment;
  -- what it owes is the loop's own type, which is `nil` for every loop this
  -- judgment types — so a valued `break` must carry `nil` (J6).
  | brkNil {D Γ top ctx Γl} :
      top = false → ctx.inLoop = some Γl →
      Judge A D Γ (.brk none) top ctx .nilT Γ D
  | brkSome {D Γ e' top ctx Γl τ Γ₁ D₁} :
      top = false → ctx.inLoop = some Γl →
      Judge A D Γ e' top ctx τ Γ₁ D₁ → SubJ τ .nilT →
      Judge A D Γ (.brk (some e')) top ctx .nilT Γ₁ D₁
  -- `retry` restarts a `rescue`'s region — sound here via the `inRescue` channel
  -- (`chk` can only claim it; J2).
  | retry' {D Γ top ctx} :
      ctx.inRescue = true → Judge A D Γ .retry' top ctx .nilT Γ D
  -- `redo` restarts the loop *body* at the current environment, so it owes the same
  -- containment `next` does — a premise `chk`'s arm lacks (J7).
  | redo' {D Γ top ctx Γl} :
      ctx.inLoop = some Γl → SubEnv Γl Γ →
      Judge A D Γ .redo' top ctx .nilT Γ D
  -- ## Definition forms.
  --
  -- A `def` with a **chosen declaration** `(τs, σ, bs)` — the generalization of
  -- `chk`'s claimed arm to a full `MethodDecl`, which is what opens the `blk`
  -- channel for `yield`. The body is judged at the declared parameter types, below
  -- the declared return, with the table pinned; no row is installed (a row the
  -- program needs is a `deltaRows` claim, visible in the residue). `declaresName`
  -- guards redefinition of a row in force, which would silently retarget it (J9);
  -- `method_added` is the hook that makes a bare `def` run arbitrary code.
  | defDecl {D Γ name ps body top ctx τs σ bs τb Γb' } :
      declaresName D name = false → (name ≠ "method_added" ∧ name ≠ "define_method") →
      τs.length = ps.length →
      Judge A D (bindParamsJ ps τs []) body false (methodCtx ctx name τs (some σ) bs) τb Γb' D →
      SubJ τb σ →
      Judge A D Γ (.def' name ps body) top ctx .sym Γ D
  -- The **promoted** nullary `def` — `chk`'s deterministic arm, guard for guard:
  -- the row it installs comes into force for the rest of the program, and each
  -- premise is a condition on the table the invariant will carry.
  | defPromote {D Γ name body top ctx τb Γb'} :
      declaresName D name = false → (name ≠ "method_added" ∧ name ≠ "define_method") →
      Judge A D [] body false (methodCtx ctx name [] none none) τb Γb' D →
      top = false → name ≠ "initialize" →
      reopenableClasses.contains ctx.cls = true →
      groundClassNames.contains ctx.cls = false →
      defFree body = true →
      ctx.ret = none → ctx.inLoop = none → ctx.inBlock = false →
      Judge A D Γ (.def' name [] body) top ctx .sym Γ
        (addRow D ctx.cls name { params := [], ret := τb })
  -- `def self.name` / `def obj.name`: the receiver is judged, the body is judged at
  -- a chosen declaration with `selfCls := none` (`self` is the receiver object,
  -- unnameable), and no row is threaded — a singleton row is `deltaRows` territory.
  | defs {D Γ recv name ps body top ctx τrcv Γ₁ D₁ τs σ bs τb Γb'} :
      Judge A D Γ recv top ctx τrcv Γ₁ D₁ →
      τs.length = ps.length →
      Judge A D₁ (bindParamsJ ps τs []) body false (singletonCtx ctx name τs σ bs) τb Γb' D₁ →
      Judge A D Γ (.defs recv name ps body) top ctx .sym Γ₁ D₁
  -- `class C … end` at toplevel reopens a boot class; the body's table extension is
  -- threaded out (a `def` inside the class is available afterwards).
  | classTop {D Γ name body ctx τ Γb' Db} :
      reopenableClasses.contains name = true →
      Judge A D [] body false ({ cls := name, inClassBody := true } : JCtx) τ Γb' Db →
      Judge A D Γ (.class' name none body) true ctx τ Γ Db
  -- With an explicit superclass the "reopen" is a *definition*, whose ancestor
  -- chain the boot heap does not have: the body is judged and its extension
  -- dropped (rows on a program-defined class are `deltaRows`/C9 territory).
  | classSup {D Γ name s body top ctx τs' Γ₁ D₁ τ Γb' Db'} :
      Judge A D Γ s top ctx τs' Γ₁ D₁ →
      Judge A D₁ [] body false ({ cls := name } : JCtx) τ Γb' Db' →
      Judge A D Γ (.class' name (some s) body) top ctx τ Γ₁ D₁
  | module' {D Γ name body top ctx τ Γb' Db'} :
      Judge A D [] body false ({ cls := name } : JCtx) τ Γb' Db' →
      Judge A D Γ (.module' name body) top ctx τ Γ D
  | scopedClass {D Γ base name body top ctx τb' Γ₁ D₁ τ Γb' Db'} :
      JudgeOpt A D Γ base top ctx τb' Γ₁ D₁ →
      Judge A D₁ [] body false ({ cls := name } : JCtx) τ Γb' Db' →
      Judge A D Γ (.scopedClass base name body) top ctx τ Γ₁ D₁
  | scopedModule {D Γ base name body top ctx τb' Γ₁ D₁ τ Γb' Db'} :
      JudgeOpt A D Γ base top ctx τb' Γ₁ D₁ →
      Judge A D₁ [] body false ({ cls := name } : JCtx) τ Γb' Db' →
      Judge A D Γ (.scopedModule base name body) top ctx τ Γ₁ D₁
  -- `class << obj`: the definee is the eigenclass, which has a name only when the
  -- object is a class (`.clsOf`); otherwise the body is judged at the enclosing
  -- definee's name and the extension dropped.
  | sclass {D Γ obj body top ctx τo Γ₁ D₁ nm τ Γb' Db'} :
      Judge A D Γ obj top ctx τo Γ₁ D₁ →
      nm = (match τo with | .clsOf n => n | _ => ctx.cls) →
      Judge A D₁ [] body false ({ cls := nm } : JCtx) τ Γb' Db' →
      Judge A D Γ (.sclass obj body) top ctx τ Γ₁ D₁
  -- ## `begin`/`rescue`/`else`/`ensure`.
  --
  -- The region's exits are the body's (or the `else`'s, which replaces it) and
  -- every handler's; a chosen `τj` bounds them all, and the region's environment is
  -- the **entry** one — the only environment every exit path guarantees.
  --
  -- [SOUNDNESS-OPEN] (J8): handlers are judged at the entry environment `Γ`, but a
  -- raise fires at a *mid-body* environment, and the body may have **retyped** a
  -- local before raising (`x = "s"` after `x : Int` at entry) — at which point the
  -- handler's assumption about `x` is wrong. Transcribed from `chk` (which is not
  -- in the sound fragment here either) so the question is resolved at J1
  -- preservation, not silently patched. Candidate fixes: judge handlers at `Γ`
  -- masked of every local the body assigns (needs an assigned-names predicate), or
  -- carry per-raise-point environments (heavier). CRuby-verifiable question for the
  -- oracle: none — this is a soundness question about the abstraction, not a
  -- semantics question.
  | begin' {D Γ body rescues els ens top ctx τb Γb₂ τrs τe τj} :
      Judge A D Γ body top ctx τb Γb₂ D →
      JudgeRescues A D Γ top ctx rescues τrs →
      JudgeElse A D Γ els top ctx τb τe →
      JudgeEns A D Γ ens top ctx →
      (∀ τ ∈ τe :: τrs, SubJ τ τj) →
      Judge A D Γ (.begin' body rescues els ens) top ctx τj Γ D
  -- ## `super` and `zsuper`: the target is *this method's name*, resolved after the
  -- definee. A block-bearing `super` has no rule — a `blk`-carrying row is
  -- deliberately unreadable by `sigOf`-shaped lookups (L242; J11).
  | super' {D Γ args top ctx mn τs Γ₁ D₁ d} :
      ctx.meth = some mn → mn ≠ "" →
      JudgeArgs A D Γ args top ctx τs Γ₁ D₁ →
      superDecl? D₁ ctx.cls mn = some d → SubJs τs d.params →
      Judge A D Γ (.super' args none) top ctx d.ret Γ₁ D₁
  -- Bare `super` forwards the enclosing method's parameter *values*, so its
  -- argument types are the declared parameter types — the `params` channel.
  | zsuper {D Γ top ctx mn ps d} :
      ctx.meth = some mn → mn ≠ "" → ctx.params = some ps →
      superDecl? D ctx.cls mn = some d → SubJs ps d.params →
      Judge A D Γ (.zsuper none) top ctx d.ret Γ D
  -- `alias new old` is admissible exactly when the *old* name has no row in force:
  -- then no signature can be invalidated by the rebinding. (`undef` has no rule —
  -- see the module docstring.)
  | alias' {D Γ newName old top ctx} :
      declaresName D old = false →
      Judge A D Γ (.alias' newName old) top ctx .nilT Γ D
  -- `defined?(e)`: a String naming what `e` is, or nil; the operand is not
  -- evaluated (artifact 03 §6), so nothing about it is judged.
  | defined {D Γ e top ctx} :
      Judge A D Γ (.defined e) top ctx (.nilable (.cls "String")) Γ D
  -- ## Composites.
  | array {D Γ es top ctx Γ' D'} :
      JudgeElems A D Γ es top ctx Γ' D' →
      Judge A D Γ (.array es) top ctx (.cls "Array") Γ' D'
  -- **`.any`, deliberately** (J40): a hash value is excluded from `plainRecv`
  -- (its payload arm is `false`), so `ValueTy h v (.cls "Hash")` is uninhabitable
  -- and a `.cls "Hash"` conclusion could never be machine-typed — the L261
  -- weakest-honest-type move, at the other container. An element-typed Hash is
  -- `Ty.arrayOf`'s story at another constructor, priced separately.
  | hash {D Γ pairs top ctx Γ' D'} :
      JudgePairs A D Γ pairs top ctx Γ' D' →
      Judge A D Γ (.hash pairs) top ctx .any Γ' D'
  | seq {D Γ es top ctx τ Γ' D'} :
      JudgeSeq A D Γ es top ctx τ Γ' D' →
      Judge A D Γ (.seq es) top ctx τ Γ' D'
  -- ## Subsumption (J4): weaken the type up, weaken the exit environment down
  -- (drop or coarsen bindings the continuation does not need). The one
  -- non-syntax-directed rule, and the reason joins and stackmaps stay one rule
  -- each.
  | sub {D Γ e top ctx τ Γ' D' σ Γ''} :
      Judge A D Γ e top ctx τ Γ' D' →
      SubJ τ σ → SubEnv Γ'' Γ' →
      Judge A D Γ e top ctx σ Γ'' D'
  /-- **The semantic axiom leaf (J31).** A claimed expression judges at the
      canonical indices — `.any`, environment- and table-preserving — under *any*
      table, environment, and context. No syntactic premise about `e` at all: the
      claim's semantic obligation (`SemAxiomsOk` in the proof layer, one
      `EvalOkAt` per claim) is what `judge_sound`-style composed theorems are
      conditional on. The `fragHead` gate keeps claims out of the syntactic
      fragment's head universe, so the two routes never compete for one
      expression (the mixed-state hazard recorded in `implementation-notes.md`
      J31). -/
  | semantic {D Γ top ctx} {cl : SemClaim} :
      cl ∈ A → fragHead cl.e = false →
      (∀ cn, cl.reqCls = some cn →
        ctx.cls = cn ∧ ctx.inClassBody = true ∧ ctx.inBlock = false) →
      -- claimed rows must be *fresh* (J35, `defPromote`'s `declaresName` guard for
      -- the same reason: installing over a row in force would silently retarget it)
      (∀ r ∈ cl.rows, declaresName D r.2.1 = false) →
      -- **The row discipline (J32)**: a row-bearing claim may not sit inside a
      -- method body (`ctx.meth` is `some` exactly there) — method bodies are
      -- `defFree`, `judge_mono` transports them with the table pinned, and a
      -- table-growing claim would break that. Class bodies and the toplevel
      -- (`meth = none`) are exactly where Rails-style generation lives.
      (cl.rows = [] ∨ ctx.meth = none) →
      Judge A D Γ cl.e top ctx cl.τ Γ (addRows D cl.rows)

end

end RubyCore.Judgment
