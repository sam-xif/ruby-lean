import RubyCore.Types.Ty

/-!
# F1a — the static declaration table

`homebrew/typing-a-mutable-method-table.md` §8 F1a, `PLAN.md` D10. The table the
refinement invariant is *relative to*: a static, per-class map from a method name
to its declared signature, computed from the program and never from the heap.

## Why a table at all, when `builtinSig` was a function

`builtinSig : Ty → String → Option (List Ty × Ty)` was keyed on the receiver's
static **type**, which is enough while `Ty` and the dispatch class are in
bijection (`Types/Core.lean` says so in as many words) and stops being enough the
moment a user class has a type. More to the point, D10 changed what the invariant
*says*: not "the method table matches the declarations" but "every method the
declarations name resolves to something conforming to its declared signature".
That sentence quantifies over a table of declarations, so the table has to be an
artifact rather than a function definition — something a step can be shown to
preserve, and something an assumption can be *listed in* (D8: an assumption must
be an artifact, not a residue).

## Keyed on the class name, and why the key is the fragile part

`infer` cannot name an `ObjId` — `check` is a pure function of the program, and
object identities exist only in a heap. So declarations hang off the class
**name**, and the invariant's job is to tie that name to the heap's `ancestors`
(`Proof/Static/Decls.lean`). That is also why `Module#set_temporary_name` and
anonymous-class renaming are outside the D10 fragment: they change the key, not
the table (`typing-a-mutable-method-table.md` §5).

## What is in the table today

`baseDecls` — the three `Integer` builtins P0 tabulated, restated as
declarations. Nothing else: no program construct declares a signature yet, since
`sig` is not in `infer`'s domain. `declsOf` is nevertheless a function of the
program, so that when F1b reads a program's own `sig`s the *shape* of `check`
does not change.
-/

namespace RubyCore.Types

/-- **The signature of the block a method takes** (L242) — the parameter types the
    block is called with, and the type its body must answer.

    A *separate* structure from `MethodDecl` rather than a recursive occurrence of it,
    and the reason is what the two describe. A `MethodDecl` is a claim about a
    **method-table entry**: something `ResolvesAt` finds and `ConformsAt`/`UserConforms`
    discharge. A `BlockSig` is a claim about a **call the callee makes** — the callee
    invokes the block, so the direction of the obligation is reversed: the *caller* owes
    a body that answers `ret` when handed values of `params`, and the *callee* owes to
    call it that way and no other. Nesting `MethodDecl` would suggest a block can itself
    take a block, which no rule will admit and which `reifyBlock` gives no shape to.

    There is no arity slack: `params.length` is the number of values `iterStep` yields
    per iteration, exactly, because `callClosure` binds them positionally. Ruby's
    auto-splat (a one-parameter block receiving a `[k, v]` pair whole) is therefore a
    *different* row and not a widening of this one — `Hash#each` yields one argument,
    and a `|k, v|` block against it is `callClosure`'s destructuring path, which
    `openParams` already refuses by kind. -/
structure BlockSig where
  params : List Ty := []
  ret : Ty
deriving DecidableEq, Repr, Inhabited

/-- A declared signature: parameter types and return type. The receiver's type is
    the key's class, not a field.

    **`blk` is the block the method takes** (L242), `none` for a method that takes
    none — which is every row any shipped table holds, and every row `DeclsOk` can
    currently witness (`ConformsAt` and `UserConforms` each pin it, and each names the
    bill the day it is widened). A defaulted field, so all 130-odd existing literals
    elaborate unchanged. -/
structure MethodDecl where
  params : List Ty
  ret : Ty
  blk : Option BlockSig := none
deriving DecidableEq, Repr, Inhabited

/-- The machine's qualified-name computation, table-side: `enterClassBody` names
    a nested definition `Owner::name` and a toplevel one bare (`defmod = Object`).
    Lives in the Types layer so both the `Judge.module'` rule and the proof-side
    `ModuleNameOk` read the same spelling. -/
def qualifyMod (owner nm : String) : String :=
  if owner = "Object" then nm else owner ++ "::" ++ nm

/-- The static declaration table.

    **A structure with two fields since L176**, where it was an association list
    of method rows. The second field is the **constant** table, and it is here
    rather than in a table of its own for one reason: L160 made the declarations a
    *threaded* judgement — `infer` returns one, `KontOk` carries it as an index,
    `Inv` quantifies it existentially — and a constant assignment needs exactly
    that same threading, for exactly the same reason (`initiation` obliges the
    invariant at the **boot** heap, so a constant the program's own `casgn`
    creates cannot be in a table fixed up front). Putting it in the value that is
    already threaded costs **no new index anywhere**; a parallel table would cost
    one in `infer`'s answer, in three `KontOk` constructors, in `Inv`, in `CtlOk`
    and in every consecution case.

    `rows` is still an association list rather than a `HashMap` for the same
    reason `Env` is one: the proofs case on it, and `List.find?` has equation
    lemmas that reduce. -/
structure Decls where
  /-- class name → method name → declared signature. -/
  rows : List (String × List (String × MethodDecl)) := []
  /-- constant name → the type of its value.

      **Populated and read since L195.** L176 threaded the field and left it empty;
      what made it necessary was `T`. The `.const` read rule was keyed on a *global*
      list (`readableClasses`), and a global list cannot admit a name that exists only
      at the prelude-booted heap: `check_sound` establishes `Inv` at `Machine.init p`,
      the bare boot heap, where an entry naming an absent constant makes its
      obligation false. Measured at L194, not guessed.

      A **declaration** has no such problem, because `Inv` already ∃-quantifies the
      table and ties it to the heap with `DeclsOk`. So the boot-safe table and the
      prelude-aware one are two tables rather than two rule sets, and each is sound at
      the heap it describes. That is also why this is `List (String × Ty)` rather than
      a list of names: `HEAD_VERSION_REGEX : Regexp` is the *same rule* at a different
      type, which is the next population after `T`. -/
  consts : List (String × Ty) := []
  /-- **class name × instance-variable name → the type of its contents** (L196).

      The third table, and it is here rather than in a new `Inv` conjunct for
      `consts`' reason: `DeclsOk` is already threaded and already transported, so a
      *declaration* costs nothing that the two existing halves have not paid for.

      Read the clause it obliges (`Proof/Static/Decls.lean`'s `IvarOk`) before adding
      a row: it is quantified over **every object of the class**, not over one
      receiver, because an ivar read has no receiver to constrain — `@x` reads the
      frame's `self`, and the invariant does not know which object that is beyond its
      class. That is also why the *write* rule now checks conformance: L191 admitted
      `@x = e` freely because nothing claimed anything about ivars, and a row is
      exactly such a claim. -/
  ivars : List ((String × String) × Ty) := []
  /-- **class name × constant name → the type of its value** (L205), for a *scoped*
      read `C::n`.

      The fourth table, and it is a separate one from `consts` rather than a key
      convention inside it because the two are read by different rules against
      different heap facts: `constTy?` answers `::n`, which is `Object`'s own table
      (L203), while this answers `C::n`, which is `constLookupFrom` — the **ancestors**
      walk from the class object named `C`. Two lookups, two clauses.

      `ScopedConstOk` (`Proof/Static/Decls.lean`) is what a row here obliges, and it is
      quantified over **every** class object of that name for `IvarOk`'s reason: the
      rule has a name, not an id, and only `ClassOk`'s uniqueness clause ties a name to
      one id — and that clause covers the *readable* names, not every name a program
      can write. -/
  scopedConsts : List ((String × String) × Ty) := []
  /-- **class name × method name → the signature of that method's `super`** (L211).

      The fifth table, and it is keyed on the *pair* for `scopedConsts`' reason
      inverted: a `super` inside `C#m` re-dispatches `m` starting *after* `C` on the
      receiver's chain, so the answer depends on both the class the body is written in
      and the method it is written in. The alternative — a `parent : String → String`
      table plus `declOf?` on the parent's rows — needs a heap clause tying a *name* to
      a chain position, and `ClassOk`'s uniqueness clause covers only
      `readableClasses`, so a program class's name does not pin an id.

      What a row obliges is `SuperOk` (`Proof/Static/Decls.lean`), and read it before
      adding one: it is quantified over **every** class object named `c` and every
      chain that class is on, because `doSuper` starts its walk at the frame's `defmod`
      and the invariant knows that definee only by its name. -/
  supers : List ((String × String) × MethodDecl) := []
  /-- **global-variable name → the type of its contents** (L228).

      The sixth table, and the **first one that is not about the heap**. The five above
      it are all read against a `DeclsOk` clause — a fact about objects, classes or
      chains — and this one is read against `m.globals`, an association list on the
      machine. So it is the first table whose obligation cannot live in `DeclsOk` and
      needs its own `Inv` conjunct (`GlobalsOk`, `Proof/Static/Konts.lean`), which is
      what makes this rung more than a fourth copy of `ivars`.

      **The name includes the `$`** (`"$__dt_rx3"`), because that is what the AST
      carries and what `Machine.getGlobal` keys on — no normalization anywhere.

      Only *plain* globals may be declared: `$~`, `$!` and the match views
      (`$1`…`$9`, `` $` ``, `$'`) are not in `m.globals` at all — `getGlobal` routes
      them to `currentExc` and `lastMatchValue`, and `matchGlobal` reads the views out
      of the match data — so a row here would describe the wrong storage. The rule
      carries `plainGlobal` for exactly that, and `GlobalsOk` is quantified over the
      plain names only. -/
  globals : List (String × Ty) := []
  /-- **(owner class name, module name) → a declared `module name … end` site** (J44).

      The seventh table, and the first about *definitions* rather than reads: a
      machine-typed `module'` must know which `enterClassBody` branch it takes, and
      at a conformant heap the constant it probes is arbitrary. A declared pair
      obliges `ModuleNameOk` (`Proof/Static/Decls.lean`): the owner's constant `name`
      is either absent (the fresh branch) or a bona-fide module named
      `qualifyMod owner name` with its eigenclass realized and its id off every
      readable pre-`Object` chain segment (the reopen branch). The owner key is the
      judging context's `cls` — `"Object"` at toplevel, the enclosing module's
      qualified name inside a module body. -/
  modules : List (String × String) := []
deriving DecidableEq, Repr, Inhabited

/-- The declared type of a constant, or `none` for "not declared". `declOf?`'s
    shape at the constant table. -/
def constTy? (D : Decls) (n : String) : Option Ty :=
  (D.consts.find? (·.1 == n)).map (·.2)

/-- The declared type of `@x` on instances of `cls`, or `none` for "not declared" —
    which the read rule reports as a *missing declaration* rather than as a missing
    rule (L196). -/
def ivarTy? (D : Decls) (cls x : String) : Option Ty :=
  (D.ivars.find? (·.1 == (cls, x))).map (·.2)

/-- The declared type of `C::n`, or `none` for "not declared" — reported as a missing
    *declaration* by the open front end (L205), exactly as `ivarTy?`'s miss is. -/
def scopedConstTy? (D : Decls) (cls n : String) : Option Ty :=
  (D.scopedConsts.find? (·.1 == (cls, n))).map (·.2)

/-- The declared signature of the `super` a body in `cls#name` re-dispatches to, or
    `none` for "not declared" — which the open front end reports as a *missing
    declaration* rather than as a missing rule (L211), exactly as `ivarTy?`'s miss and
    `scopedConstTy?`'s are. -/
def superDecl? (D : Decls) (cls name : String) : Option MethodDecl :=
  (D.supers.find? (·.1 == (cls, name))).map (·.2)

/-- The declared type of `$x`, or `none` for "not declared" — reported as a missing
    *declaration* by the open front end (L228), exactly as `ivarTy?`'s miss is. -/
def globalTy? (D : Decls) (x : String) : Option Ty :=
  (D.globals.find? (·.1 == x)).map (·.2)

/-- **A global the machine keeps in `m.globals`** (L228) — everything except the two
    machine-backed names and the match views. `Interp.getGlobal`'s three-way split *is*
    this predicate: `$!` is `currentExc`, `$~` is the frame's `lastMatch`, a view is
    computed by `matchGlobal` from the match data, and everything else is the
    association list. A rule about the association list has to say which. -/
def plainGlobal (x : String) : Bool :=
  x != "$!" && x != "$~" && Interp.isMatchView x == false

/-- The declarations of one class, by name. -/
def declsFor (D : Decls) (cls : String) : List (String × MethodDecl) :=
  match D.rows.find? (·.1 == cls) with
  | some (_, ms) => ms
  | none => []

/-- The declared signature of `cls#name`, or `none` for "not declared", which the
    checker reads as `unknown` — never as "no such method". The distinction is
    load-bearing: the invariant is a *lower bound*, so silence about a name is
    silence, not a claim (`typing-a-mutable-method-table.md` §2). -/
def declOf? (D : Decls) (cls name : String) : Option MethodDecl :=
  (declsFor D cls |>.find? (·.1 == name)).map (·.2)

/-- Is `name` declared on **any** class? The side condition a `def` has to pass:
    installing a name the declarations do not mention is an addition, and
    additions are free; installing one they do mention is a redefinition, which
    F1c is where the conformance check lands. Until then a `def` of a declared
    name is `unknown`.

    With `baseDecls` this is exactly P0's `name ≠ "+" ∧ name ≠ "-" ∧ name ≠ "*"`,
    which is why F1a changes no verdict. -/
def declaresName (D : Decls) (name : String) : Bool :=
  (D.rows.any fun cd => cd.2.any fun md => md.1 == name) ||
  -- **L211: and the `super` table's method names.** A `def` installs an entry into a
  -- live method table, and `SuperOk` is a claim about what `doSuper`'s walk *finds* —
  -- so a `def` of a name some `supers` row is keyed on can displace that row's target.
  -- Exactly the side condition `superOk_defineMethod` needs, and free while the table
  -- is empty.
  (D.supers.any fun sd => sd.1.2 == name)

/-- The class names the four *ground* arms of `Ty` already denote. Subtracted from
    the class arm's key set by `tyClassNames`; see the note there. -/
def groundClassNames : List String :=
  ["Integer", "TrueClass", "FalseClass", "NilClass", "Symbol", "Float"]

/-- The classes a value of a ground type can have. A **list**, not a single name,
    because `Ty.bool` is already two classes — which is the shape `T::Boolean`
    (`PLAN.md` W5 T4) needs, arriving here for free rather than as a union in
    `Ty`. -/
def tyClassNames : Ty → List String
  | .int => ["Integer"]
  -- L202: `.int`'s twin, and note it is subtracted from the class arm below by the
  -- same `groundClassNames` list — `Float` now names a *ground* type, so
  -- `.cls "Float"` must not read `Float`'s row for the reason the note gives.
  | .float => ["Float"]
  | .bool => ["TrueClass", "FalseClass"]
  | .nilT => ["NilClass"]
  | .sym => ["Symbol"]
  -- The class type is the arm this function was written for: one name, exactly
  -- the key. Note it is *not* the ancestors walk — a declaration inherited from a
  -- superclass is not visible here, which is `Sub`'s job (`PLAN.md` W5 T2) and is
  -- deliberately still absent, so today a class type sees only its own row.
  --
  -- **The ground names are subtracted, and that is not a technicality.** The two
  -- kinds of arm have *disjoint* inhabitants — `valueTy?` gives an immediate a
  -- ground type and a `.ref` a class type, never both — so if `.cls "Integer"`
  -- read `Integer`'s row, the invariant would owe an `EntryOk` for that row over
  -- receivers the row was never about: objects of some class merely *named*
  -- `Integer`. Nothing in the model rules those out, so the obligation would be
  -- unprovable rather than merely inconvenient. Giving them no declarations makes
  -- the type useless instead of unsound, which is the right failure direction and
  -- is what `Sub` will fix (an `Integer` receiver should be typed `.int`).
  | .cls n => if groundClassNames.contains n then [] else [n]
  -- **The top type names no class** (L183), which is what makes it a *parameter*
  -- type and nothing else: `declFor D .any mname` is `none` for every `mname`, so
  -- `DeclsOk` never obliges anything at it and no send can use it as a receiver.
  -- The imprecision is in `subTy`, at the position a declared parameter occupies.
  | .any => []
  -- **A nilable dispatches from nowhere** (L193), for `.any`'s reason and not for a
  -- new one: a value typed `.nilable τ` may be `nil`, so no row can be promised at
  -- it, and `[]` is what says so — `declFor` never answers at a nilable and
  -- `DeclsOk` obliges nothing. Refining a nilable to its payload is a *narrowing*
  -- rule (`x.nil?` / `if x`), which is `PLAN.md` W5 T3 and not this commit.
  | .nilable _ => []
  -- **A class object has no declarations yet** (L184), and `[]` is a decision
  -- rather than a stub: a row on `.clsOf "String"` is a **singleton** method
  -- (`def self.m`) while a row on `.cls "String"` is an instance method, so the two
  -- need *different keys in the same table* — and picking that key is rung 3's
  -- problem, not this one's. Two candidates and why neither is free:
  --
  -- * the **eigenclass's name** (`#<Class:String>`) is not available:
  --   `scripts/classobj_probe.lean` measures 60 of the booted heap's 87 class
  --   objects with no eigenclass at all, so for most of them the name does not
  --   exist;
  -- * a **prefixed** key (`"%class:" ++ n`) works arithmetically but obliges every
  --   consumer that quantifies over keys to know the prefix is unreachable —
  --   `DeclsOk_addRow` is the one that asks, since it must refute a row at a key it
  --   did not write.
  --
  -- Leaving it `[]` makes `declFor D (.clsOf n) mname = none` for every `mname`, so
  -- `DeclsOk` obliges nothing at the arm and it is a *type* with no declarations —
  -- exactly `Ty.cls`'s position between L141 and L163.
  | .clsOf _ => []
  -- **L238: `[]` for now, and the *measured* reason is worth the paragraph** — because
  -- `["Array"]` is what the arm eventually wants and it is not free.
  --
  -- With `["Array"]` an `arrayOf` receiver dispatches from `Array`'s rows, which is what
  -- `xs.select` needs. But `declFor` then answers at the arm, and `DeclsOk_addRow`'s
  -- `hτ` step — *the only type a freshly added row is read at is `.cls c`* — becomes
  -- **false**: a program may reopen `class Array` and `def` into it, and an `arrayOf`
  -- receiver would resolve there too. Its conclusion has to widen to a disjunction, and
  -- so does every consumer of it. `TyClass` is already ready (the arm is `.cls "Array"`'s
  -- content verbatim), so that lemma statement is the whole cost — but it is a cost, and
  -- this commit is the *type* and its value relation, nothing else.
  --
  -- So today the arm is a **declaration and parameter** type, like `.any`: inhabited by
  -- values (`ValueTy`'s new arm) and dispatching from nowhere.
  | .arrayOf _ => []
  -- **L269: a union dispatches from nowhere** — `.nilable`'s reason verbatim: a
  -- value typed `union σ τ` may be either side, so no single row can be promised
  -- at it, `declFor` never answers, and `DeclsOk` obliges nothing. Refining a
  -- union to a dispatchable member is a *narrowing* rule (`Judgment/Sub.lean`
  -- `dropNil`, and eventually `is_a?`), never this function's business. An
  -- all-members-agree arm (the `sigOf` nilable-union shape, L260) is the future
  -- widening if union receivers ever want direct dispatch.
  | .union _ _ => []
  -- L270: an arrow dispatches from no method table — its one consumer is the
  -- judgment layer's `call` rule, never `declFor`.
  | .arrow0 _ => []
  | .arrowCons _ _ => []

/-- The declared signature of `mname` for a receiver of static type `τ`: `some d`
    only when **every** class such a receiver can have declares it identically.

    Requiring agreement rather than picking the first is what makes the two-class
    types honest: a `T::Boolean` receiver may be either class at runtime, so a
    declaration that holds on only one of them supports no call site. -/
def declFor (D : Decls) (τ : Ty) (mname : String) : Option MethodDecl :=
  match tyClassNames τ with
  | [] => none
  | c :: cs =>
    match declOf? D c mname with
    | none => none
    | some d => if cs.all (fun c' => declOf? D c' mname == some d) then some d else none

/-- The signature in the `(params, ret)` shape `infer` and `KontOk` read. This is
    the direct replacement for P0's `builtinSig`, and the only difference visible
    to the type rules is that it takes the table.

    **A block-taking row is not a signature** (L242), and the filter is the whole
    inertness argument for `MethodDecl.blk`. Every rule in the fragment reads its
    receiver's declaration through this function and *none* of them passes a block, so
    a row that declares one would otherwise let `xs.each` — no block — type against
    `Array#each { |x| … } → Array`, which is a claim about a different step
    (`tryIterator` answers `none` without a block, and the call is an Enumerator the
    model gates). Refusing here rather than at each rule is what makes the field
    unreadable by anything that has not been taught about it. -/
def sigOf (D : Decls) (τ : Ty) (mname : String) : Option (List Ty × Ty) :=
  match τ with
  -- **Union dispatch at a nilable receiver** (L260), and it is the whole
  -- `nilable-receiver` rung: `x&.m` desugars to `t = x; if t.nil? then nil else t.m`, so
  -- the blocker is a plain send whose receiver type is a `.nilable σ` — a type
  -- `declFor` answers `none` at, because `tyClassNames` is `[]` there (L193).
  --
  -- The sound reading is the standard one: the send is admissible when **both** arms of
  -- the union declare the method, at the *same* signature. `NilClass` is a class like any
  -- other, so this is two ordinary `declFor` reads and no new key — which is why the rung
  -- needs no change to `infer`, to `KontOk`, or to `infer.induct`'s case numbering: every
  -- send rule already reads its receiver's row through this function.
  --
  -- `d₁ == d₂` rather than a join of the two signatures: a join would be a second,
  -- weaker notion of conformance to keep sound at dispatch, and the slice needs none of
  -- it. What the census then says at `severity&.to_s&.upcase` is `NilClass ▷ upcase` —
  -- which is exactly the answer a union-typed checker gives.
  | .nilable σ =>
    match declFor D .nilT mname, declFor D σ mname with
    | some d₁, some d₂ =>
      if d₁ == d₂ then
        match d₁.blk with
        | none => some (d₁.params, d₁.ret)
        | some _ => none
      else none
    | _, _ => none
  | _ =>
    match declFor D τ mname with
    | some d => match d.blk with
      | none => some (d.params, d.ret)
      | some _ => none
    | none => none

/-- **The two rows a nilable signature is made of** (L260) — the inversion the dispatch
    case reads, and the reason the rung needs no new `EntryOk` arm: each row is at an
    *ordinary* key, so each is `MethodRowsOk` at that key and dispatches by the machinery
    that was already there. -/
theorem sigOf_nilable {D : Decls} {σ : Ty} {mname : String} {ps : List Ty} {τret : Ty}
    (h : sigOf D (.nilable σ) mname = some (ps, τret)) :
    declFor D .nilT mname = some { params := ps, ret := τret } ∧
      declFor D σ mname = some { params := ps, ret := τret } := by
  simp only [sigOf] at h
  split at h
  · next d₁ d₂ h1 h2 =>
    split at h
    · next hq =>
      simp only [beq_iff_eq] at hq
      subst hq
      split at h
      · next hb =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hp, hr⟩ := h
        subst hp; subst hr
        refine ⟨?_, ?_⟩
        · rw [h1]; cases d₁ with | mk p r b => simp_all
        · rw [h2]; cases d₁ with | mk p r b => simp_all
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **The same read, without the arity-zero restriction** (L259) — what the
    positive-arity block-send rule asks. It hands back the declaration's *parameter
    list* as well, because that is what the argument types have to match.

    `blockSend?` is not defined in terms of this one: its own two inversion lemmas are
    what the L257 proofs read, and restating it would be a rewrite of proofs that are
    done. The duplication is four lines. -/
def blockSendA? (D : Decls) (τr : Ty) (mname : String) (ps : List Param)
    (ls : List String) : Option (String × Ty × Ty × List Ty × Ty) :=
  match ps, ls with
  | [.req x], [] =>
    match declFor D τr mname with
    | some d =>
      match d.blk, (d.blk.map (·.params)).getD [] with
      | some bs, [σp] => some (x, σp, bs.ret, d.params, d.ret)
      | _, _ => none
    | none => none
  | _, _ => none

/-- Its inversion: a successful read names a declaration with a one-parameter block
    signature, and the parameter list it hands back is that declaration's own. -/
theorem blockSendA?_declFor {D : Decls} {τr : Ty} {mname : String} {ps : List Param}
    {ls : List String} {x : String} {σp βret τret : Ty} {dps : List Ty}
    (h : blockSendA? D τr mname ps ls = some (x, σp, βret, dps, τret)) :
    ∃ d, declFor D τr mname = some d ∧ d.params = dps ∧ d.ret = τret ∧
      d.blk = some { params := [σp], ret := βret } := by
  unfold blockSendA? at h
  split at h
  · next x' =>
    split at h
    · next d hd =>
      split at h
      · next bs σ hb hbp =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, hσ, hβ, hdps, hτ⟩ := h
        refine ⟨d, hd, hdps, hτ, ?_⟩
        rw [hb] at hbp ⊢
        simp only [Option.map_some] at hbp
        subst hσ; subst hβ
        cases bs with
        | mk bps br => simp_all
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **The pieces a block send reads off the row and the block node** (L255):
    the block's one parameter name, its declared type, the type its body must answer, and
    the send's own answer.

    One function rather than four guards in the rule, for `sigOf`'s reason: the arm is
    already the deepest nest in `infer`, and a `match` on one `Option` is what
    `infer.induct` can be addressed at. Every refusal in it is a **first-cut**
    restriction, and each names a different thing the block rung has not paid for yet:

    * `[.req x]` — one required positional, which is `callClosure_req1`'s hypothesis
      (L244) and rules out auto-splat, optionals and destructuring;
    * `[]` block-locals — a name first assigned inside the block is pre-bound in the
      block frame's own `locals`, which is the widening L247 prices and this cut skips;
    * `d.params = []` — the *send* takes no positional arguments, which is `each`;
    * `bs.params = [σp]` — the block is called with one value per iteration. -/
def blockSend? (D : Decls) (τr : Ty) (mname : String) (ps : List Param)
    (ls : List String) : Option (String × Ty × Ty × Ty) :=
  match ps, ls with
  | [.req x], [] =>
    match declFor D τr mname with
    | some d =>
      match d.blk, d.params, (d.blk.map (·.params)).getD [] with
      | some bs, [], [σp] => some (x, σp, bs.ret, d.ret)
      | _, _, _ => none
    | none => none
  | _, _ => none

/-- The shape `blockSend?` refuses everything but (L255): its answer pins the block
    node's parameter list and its (empty) block-locals, which `callClosure_req1` needs. -/
theorem blockSend?_shape {D : Decls} {τr : Ty} {mname : String} {ps : List Param}
    {ls : List String} {x : String} {σp βret τret : Ty}
    (h : blockSend? D τr mname ps ls = some (x, σp, βret, τret)) :
    ps = [.req x] ∧ ls = [] := by
  unfold blockSend? at h
  split at h
  · next x' =>
    split at h
    · next d hd =>
      split at h
      · next bs σ hb hp hbp =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨by rw [h.1], rfl⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **The row `blockSend?` read**, recovered — what the invariant's `EntryOk` is about. -/
theorem blockSend?_declFor {D : Decls} {τr : Ty} {mname : String} {ps : List Param}
    {ls : List String} {x : String} {σp βret τret : Ty}
    (h : blockSend? D τr mname ps ls = some (x, σp, βret, τret)) :
    ∃ d, declFor D τr mname = some d ∧ d.params = [] ∧ d.ret = τret ∧
      d.blk = some { params := [σp], ret := βret } := by
  unfold blockSend? at h
  split at h
  · next x' =>
    split at h
    · next d hd =>
      split at h
      · next bs σ hb hp hbp =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        refine ⟨d, hd, hp, h.2.2.2, ?_⟩
        rw [hb, ← h.2.2.1, ← h.2.1]
        cases bs with
        | mk bsp bsr =>
          have hbp' : bsp = [σ] := by simpa [hb] using hbp
          rw [hbp']
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **The enclosing locals, seen from inside a block** (L255) — every name at `.any`.

    Not an approximation of the caller's environment: `ValueTy h v .any` holds of every
    value (L232), so the block frame's `FrameConforms` obligation at an enclosing name is
    discharged with no lookup at all — which is what lets `KontOk.iterK` say **nothing**
    about the frame the closure captured. A *precise* enclosing environment would need
    the pairing `KontOk` cannot express (L249). -/
def anyEnv (Γ : Env) : Env := Γ.map (fun e => (e.1, Ty.any))

/-- A lookup in `anyEnv Γ` succeeds exactly where the same lookup in `Γ` does, at `.any`.
    Induction on the list, and it is the only fact anything needs about `anyEnv`. -/
theorem anyEnv_get (Γ : Env) (y : String) :
    envGet? (anyEnv Γ) y = (envGet? Γ y).map (fun _ => Ty.any) := by
  induction Γ with
  | nil => rfl
  | cons e rest ih =>
    by_cases hy : (e.1 == y) = true
    · simp [anyEnv, envGet?, List.find?, hy]
    · simp only [anyEnv, envGet?, List.map_cons, List.find?, hy, Bool.false_eq_true, if_false]
      simpa [anyEnv, envGet?] using ih

/-- **`anyEnv` is monotone** (L255) — the one step `infer_env_mono`'s block-send case
    takes that the other arms do not: the block body is typed in an environment built
    *from* the send's, so widening the send's widens the body's. -/
theorem anyEnv_subEnv {Γ Γ' : Env} (h : SubEnv Γ Γ') : SubEnv (anyEnv Γ) (anyEnv Γ') := by
  intro y τ hy
  rw [anyEnv_get] at hy ⊢
  cases hg : envGet? Γ y with
  | none => rw [hg] at hy; exact absurd hy (by simp)
  | some σ => rw [h y σ hg]; rw [hg] at hy; exact hy

/-- Extending both sides of a containment by the same head. -/
theorem SubEnv.cons {Γ Γ' : Env} (e : String × Ty) (h : SubEnv Γ Γ') :
    SubEnv (e :: Γ) (e :: Γ') := by
  intro y τ hy
  by_cases hy2 : (e.1 == y) = true
  · simpa [envGet?, List.find?, hy2] using hy
  · simp only [envGet?, List.find?, hy2, Bool.false_eq_true, if_false] at hy ⊢
    exact h y τ hy

/-- **The context a block body is typed in** (L255). Four channels closed and one opened,
    and each closure is the honest reading of where the jump would go:

    * `ret := none` — a `return` inside a block targets the closure's **home method**,
      not this activation, so `.ret`'s rule has no target here;
    * `inLoop := none` — a `next` ends the *block invocation* (`blkFrameK`'s own arm),
      not the enclosing loop;
    * `selfCls := none` — the first cut's one real cost, measured at **one body** of the
      fifteen (`implementation-notes.md` L249): a block whose first evaluated expression
      is a send on its parameter reports a *needed declaration* long before it reaches an
      implicit-self send;
    * `meth := none`/`params := none` — no `super` from inside a block;
    * `inBlock := true` — which is what guards `StackCtx`'s name clause (L250) and
      refuses `x = 1` (L252). -/
def blockCtx (ctx : FrameCtx) : FrameCtx :=
  { cls := ctx.cls, selfCls := none, ret := none, meth := none, params := none,
    inLoop := none, inBlock := true }

/-- The names the `NoHook` heap invariant keeps off every class's dispatch chain
    (J34): `method_added` is the def-hook; `define_method` is the reflective
    installer, whose *claimed* uses (the semantic-axiom layer) need the dispatch
    to be invariant-determined — a user override is exactly what it cannot
    determine. The `def` rules of both checkers and both judgment layers refuse
    these names, which refuses nothing real. -/
def hookFreeNames : List String := ["method_added", "define_method"]

/-- **One table is carried by another**: every signature the first supports, the
    second supports identically.

    Stated over `declFor` rather than over the row lists because that is the only
    thing any rule reads, and because the structural version would be false for
    the shape that matters: `declFor` on a two-class ground type demands
    *agreement*, so a table can gain a row (`TrueClass#foo`) and support strictly
    fewer signatures than before unless the agreement survives. Requiring the
    conclusion directly makes the relation say what its users need and leaves the
    proof obligation at the step that grows the table, which is where the
    information is.

    This is the slack the F1b.8 threading needs. `infer` threads the table in
    force, and a method body checked at one point in the program is *called* at a
    later one, by which time the table has grown; carrying the smaller table in
    the witness and relating the two by `SubDecls` is what avoids needing `infer`
    to be monotone in the table — which it is **not** (`declaresName` is
    name-global, so a new row refuses a `def` of that name). -/
def SubDecls (F F' : Decls) : Prop :=
  (∀ τ mname d, declFor F τ mname = some d → declFor F' τ mname = some d) ∧
  -- **The constant table is *equal*, not merely contained** (L195), and it is worth
  -- saying why the weaker relation would be wrong rather than just unnecessary: the
  -- `.const` rule reads the type *out of* the table, so a `F'` that answered a
  -- different type at the same name would make `infer_mono` false, not just
  -- unprovable. Nothing in the fragment grows `consts` — there is no `casgn` rule —
  -- so equality costs nothing today and `casgn` will have to say what it means for a
  -- constant to be *added*, which is a real question about shadowing.
  F.consts = F'.consts ∧
  -- L196: and the ivar table, for the constant table's reason — the read rule takes
  -- its answer out of it.
  F.ivars = F'.ivars ∧
  -- L205: and the scoped-constant table, same reason again.
  F.scopedConsts = F'.scopedConsts ∧
  -- L211: and the `super` table, same reason a third time — the `super` rule reads its
  -- answer out of it, so a `F'` disagreeing at the same key would make `infer_mono`
  -- false rather than merely unprovable.
  F.supers = F'.supers ∧
  -- L228: and the globals table, same reason a fourth time.
  F.globals = F'.globals ∧
  -- J44: and the declared-modules table — the `module'` rule reads membership out
  -- of it, and the invariant clause it obliges is per-entry.
  F.modules = F'.modules

/-- **`blockSend?` is monotone in the table** (L255), which is the half `infer_mono` needs:
    it reads `declFor` and nothing else, and `SubDecls`' first component is exactly that
    reading preserved. -/
theorem SubDecls.blockSend_eq {F F' : Decls} (hs : SubDecls F F') {τr : Ty}
    {mname : String} {ps : List Param} {ls : List String} {r : String × Ty × Ty × Ty}
    (h : blockSend? F τr mname ps ls = some r) : blockSend? F' τr mname ps ls = some r := by
  unfold blockSend? at h ⊢
  cases ps with
  | nil => exact absurd h (by simp)
  | cons p rest =>
    cases p <;> cases rest <;> cases ls <;>
      simp only [] at h ⊢ <;>
      first
        | exact absurd h (by simp)
        | (cases hd : declFor F τr mname with
           | none => rw [hd] at h; exact absurd h (by simp)
           | some d =>
             rw [hd] at h
             rw [hs.1 τr mname d hd]
             exact h)

/-- And `blockSendA?` likewise (L259) — the same one-line reading, same proof. -/
theorem SubDecls.blockSendA_eq {F F' : Decls} (hs : SubDecls F F') {τr : Ty}
    {mname : String} {ps : List Param} {ls : List String}
    {r : String × Ty × Ty × List Ty × Ty}
    (h : blockSendA? F τr mname ps ls = some r) : blockSendA? F' τr mname ps ls = some r := by
  unfold blockSendA? at h ⊢
  cases ps with
  | nil => exact absurd h (by simp)
  | cons p rest =>
    cases p <;> cases rest <;> cases ls <;>
      simp only [] at h ⊢ <;>
      first
        | exact absurd h (by simp)
        | (cases hd : declFor F τr mname with
           | none => rw [hd] at h; exact absurd h (by simp)
           | some d =>
             rw [hd] at h
             rw [hs.1 τr mname d hd]
             exact h)

theorem SubDecls.refl (F : Decls) : SubDecls F F :=
  ⟨fun _ _ _ h => h, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SubDecls.trans {F F' F'' : Decls} (h₁ : SubDecls F F') (h₂ : SubDecls F' F'') :
    SubDecls F F'' :=
  ⟨fun τ m d h => h₂.1 τ m d (h₁.1 τ m d h), h₁.2.1.trans h₂.2.1,
    h₁.2.2.1.trans h₂.2.2.1, h₁.2.2.2.1.trans h₂.2.2.2.1,
    h₁.2.2.2.2.1.trans h₂.2.2.2.2.1, h₁.2.2.2.2.2.1.trans h₂.2.2.2.2.2.1,
    h₁.2.2.2.2.2.2.trans h₂.2.2.2.2.2.2⟩

/-- The constant-table form, which is what the `.const` rule reads. -/
theorem SubDecls.constTy_eq {F F' : Decls} (hs : SubDecls F F') (n : String) :
    constTy? F' n = constTy? F n := by
  unfold constTy?; rw [hs.2.1]

/-- And the ivar table's (L196). -/
@[simp] theorem SubDecls.ivarTy_eq {F F' : Decls} (hs : SubDecls F F') (c x : String) :
    ivarTy? F' c x = ivarTy? F c x := by
  unfold ivarTy?; rw [hs.2.2.1]

/-- And the scoped-constant table's (L205). -/
@[simp] theorem SubDecls.scopedConstTy_eq {F F' : Decls} (hs : SubDecls F F') (c n : String) :
    scopedConstTy? F' c n = scopedConstTy? F c n := by
  unfold scopedConstTy?; rw [hs.2.2.2.1]

/-- And the `super` table's (L211). -/
@[simp] theorem SubDecls.superDecl_eq {F F' : Decls} (hs : SubDecls F F') (c n : String) :
    superDecl? F' c n = superDecl? F c n := by
  unfold superDecl?; rw [hs.2.2.2.2.1]

/-- And the globals table's (L228). -/
@[simp] theorem SubDecls.globalTy_eq {F F' : Decls} (hs : SubDecls F F') (x : String) :
    globalTy? F' x = globalTy? F x := by
  unfold globalTy?; rw [hs.2.2.2.2.2.1]

/-- And the declared-modules table's (J44). -/
@[simp] theorem SubDecls.modules_eq {F F' : Decls} (hs : SubDecls F F') :
    F'.modules = F.modules := hs.2.2.2.2.2.2.symm

/-- The `sigOf` form, which is what the type rules read. -/
theorem SubDecls.sigOf_eq {F F' : Decls} (hs : SubDecls F F') {τ : Ty} {mname : String}
    {ps : List Ty} {τret : Ty} (h : sigOf F τ mname = some (ps, τret)) :
    sigOf F' τ mname = some (ps, τret) := by
  unfold sigOf at h ⊢
  cases τ with
  -- L260: the nilable arm reads *two* rows, so it moves by two applications of the
  -- same `declFor` monotonicity the others use one of.
  | nilable σ =>
    simp only [] at h ⊢
    cases h1 : declFor F Ty.nilT mname with
    | none => rw [h1] at h; exact absurd h (by simp)
    | some d₁ =>
      cases h2 : declFor F σ mname with
      | none => rw [h1, h2] at h; exact absurd h (by simp)
      | some d₂ =>
        rw [hs.1 _ mname d₁ h1, hs.1 _ mname d₂ h2]
        rw [h1, h2] at h; exact h
  | _ =>
    all_goals (
      simp only [] at h ⊢
      first
        | (cases hd : declFor F (Ty.cls _) mname with
           | none => rw [hd] at h; exact absurd h (by simp)
           | some d => rw [hs.1 _ mname d hd]; rw [hd] at h; exact h)
        | (rename_i a
           cases hd : declFor F a mname with
           | none => rw [hd] at h; exact absurd h (by simp)
           | some d => rw [hs.1 _ mname d hd]; rw [hd] at h; exact h)
        | (cases hd : declFor F _ mname with
           | none => rw [hd] at h; exact absurd h (by simp)
           | some d => rw [hs.1 _ mname d hd]; rw [hd] at h; exact h))

/-! ## The reopenable classes

`class C … end` takes one of three branches in `enterClassBody`
(`Interp/Dispatch.lean:236`): **reopen** if `constOwn defmod name` answers a class
object of matching kind, **`TypeError`** if it answers anything else, and
**allocate** if it answers nothing. Only the first is a step the invariant can
survive today — the third writes a class into the heap, which is what
`PlainGrow`'s *nothing became a class* clause forbids, and the second is a `.jump`,
which `CtlOk` refuses outright.

So the rule is admissible for a name the invariant can *promise* takes the reopen
branch, and this is that list. Every entry is a proof obligation of exactly the
same kind as a `baseDecls` row — `ClassOk` (`Proof/Static/Decls.lean`) is what the
invariant carries and `classOkB` is what the certificate decides — and widening it
is a table row plus a `decide`.

`String` is the one entry, and it is not arbitrary: it is the only ground class
the fragment can currently *produce a value of* (`.str`, L151), so it is the only
one for which reopening buys a call site.

**Since L189 the list has a second reader, and it is the one that now sets its
size**: the `.const` *read* rule answers `.clsOf n` exactly for `n` on this list, so
a row buys a constant reference and not only a reopen. L192 adds the **error class
names** for that reason and for no other — `--sets` reports three singleton-`{const}`
method bodies whose only blocker is one of `ArgumentError`, `NotImplementedError`
and `NoMethodError`, read as `raise ArgumentError, "…"`.

The rows are free, and *measured* free: `scripts/reopen_probe.lean` decides all seven
`ClassOk` clauses for every candidate, and all fourteen below pass all seven. Nothing
in `Proof/` changes — `ClassOk` is quantified over the list — so the whole cost is
`classOkB` still answering `true`, which `check-proofs.sh` runs. (The probe also
refuses `IOError`: it is not a constant of `Object` at the booted heap at all.) -/
def reopenableClasses : List String :=
  ["String", "Integer", "Symbol", "NilClass", "TrueClass", "FalseClass",
   "Proc", "Exception",
   -- L192. Ordered as the probe reports them.
   "ArgumentError", "NoMethodError", "NotImplementedError", "TypeError",
   "RuntimeError", "StandardError", "NameError", "IndexError", "KeyError",
   "ZeroDivisionError", "FrozenError", "StopIteration", "RangeError",
   "LocalJumpError"]

/-- **The names the `.const` *read* rule admits** (L194) — a *superset* of
    `reopenableClasses`, because the read needs strictly fewer facts than the reopen.

`class C … end` must know the object is a class and not a module, that its ancestor
chain starts at itself (a `def` in the body has to land where `lookup` finds it), and
that nothing before `Object` on its chain owns a constant (a constant read *inside*
the body has to reach the toplevel table). **A read of `C` itself needs none of
those** — only that the name is in `Object`'s own table, uniquely, at a legal
receiver, and that no other class object owns the name.

Splitting the two is worth **seven method bodies** of the slice, and both entries
below are there because a measurement put them there
(`scripts/reopen_probe.lean` decides both clause sets per candidate):

* **`T`** is the slice's most-read constant by a factor of five — 259 occurrences,
  `T.let`/`T.must`/`T.nilable` — and it is a **module**, so it can never be
  reopenable. Six bodies.
* **`Float`** owns `NAN` and `INFINITY`, so something in front of `Object` on its
  chain owns a constant and `NoShadowBefore` fails. That clause is about reading
  constants from *inside* `Float`, which reading the name `Float` does not do. One
  body.

`Comparable` and `Kernel` are also free by the same measurement and are **not** here:
nothing in the slice reads them, and a row with no call site is the speculative clause
L191 warned about. `Array`, `Hash` and `Range` are refused — `T::Array` and friends
own those names too, so sole ownership fails — and `Regexp` is refused because
`classRecv` excludes its id (L106). -/
def readableClasses : List String :=
  reopenableClasses ++ ["Float"]

/-- Every reopenable name is readable — the inclusion `ClassOk`'s consumers use to
    read the reopen clauses out of the one quantified block. `simp` proves it because
    the table is a literal `++`. -/
theorem readable_of_reopenable {n : String} (h : n ∈ reopenableClasses) :
    n ∈ readableClasses := by
  unfold readableClasses
  exact List.mem_append_left _ h

/-- **The boot-safe constant table.** Every name is a class object that exists in
    `Boot.initHeap`, so `ClassOk` supplies the obligation and `check_sound` is
    unaffected. -/
def baseConsts : List (String × Ty) :=
  readableClasses.map (fun n => (n, Ty.clsOf n))

/-- **The prelude-aware table** (L195), which is what the *tool* reports against:
    the model the difftest SUT runs, and the heap `--assn` describes, is the
    prelude-booted one.

    One extra row, and it is the whole point: **`T`** — `sorbet-runtime`'s namespace,
    the slice's most-read constant by a factor of five (259 occurrences of
    `T.let`/`T.must`/`T.nilable`), and a *module*, so it can never be reopenable.
    `scripts/reopen_probe.lean` decides its four read clauses and
    `scripts/consts_probe.lean` decides this table's obligation at the booted heap;
    `check-proofs.sh` runs both, so the row is certified rather than assumed. -/
def preludeConsts : List (String × Ty) :=
  baseConsts ++ [("T", Ty.clsOf "T")]

/-- **A row, added.** Prepending shadows: `declsFor` reads `D.find?`, which stops
    at the first entry for the class, so the new entry carries the class's old rows
    plus the new one and every other class is found further down unchanged.

    The alternative — rewriting the existing entry in place — needs a `List.map`
    whose `find?` behaviour is a lemma; this way the only fact anything needs is
    `List.find?`'s own equation. -/
def addRow (D : Decls) (cls name : String) (d : MethodDecl) : Decls :=
  { D with rows := (cls, (name, d) :: declsFor D cls) :: D.rows }

/-! ## The base table

`static-soundness-poc.md` §5's builtin signatures, as declarations. Every entry
is a **proof obligation** — `Proof/Static/Decls.lean`'s `DeclsOk` is what the
invariant carries, and `tableOk_declsOk` is the proof for these three. Entries
whose conformance is not proved may not appear; the notable absences and their
reasons are unchanged from P0 (`/` and `%` raise `ZeroDivisionError`, `**` makes
a Rational, and the `Float` promotions would need the argument type unpinned).
-/

-- L195: `consts` is folded into `baseDecls` rather than layered on with a structure
-- update. `infer` reads `D.consts`, so `EntryOk baseDecls` and `EntryOk` at an updated
-- table are *different* propositions, and every `baseDecls` lemma would have had to be
-- restated at the update.
def baseDecls : Decls := { consts := baseConsts, rows :=
  [("Integer",
    [("+", { params := [.int], ret := .int }),
     ("-", { params := [.int], ret := .int }),
     ("*", { params := [.int], ret := .int }),
     -- **The first nullary row** (L152), and it is here to *exercise* the zero-arity
     -- rule rather than for its own sake: without a row whose `params` is `[]`,
     -- `sigOf` never answers `some ([], _)` and the new `infer` arm, `KontOk.recvK0`
     -- and its consecution case would all be unreachable code with a proof attached.
     -- `zero?` was picked over `even?`/`abs` for two measured reasons. Constraint 2:
     -- `declaresName` is name-global, so every row added here refuses `def <name>`
     -- program-wide — and `def zero?` appears in **0** of the 1,227 bootstraptest
     -- programs. And resolution: `ResolvesAt` requires `fromPrelude = false`, while
     -- `abs` is defined **twice** in `prelude/prelude.rb`, so its row would be
     -- unwitnessable at the prelude-booted heap even though it is fine at the boot
     -- one. Check both before adding a row, not just the first.
     ("zero?", { params := [], ret := .bool })])] }

/-- Changing `consts` leaves every method-table function alone, and the equality is
    `rfl` — stated as a `simp` lemma so the `baseDecls` refutation lemmas apply to
    `declsOf p` without an unfold (L195). -/
@[simp] theorem declFor_consts (c : List (String × Ty)) (τ : Ty) (m : String) :
    declFor { baseDecls with consts := c } τ m = declFor baseDecls τ m := rfl

/-- The declarations in force while checking `p`.

    A function of the program, and constant today: no construct in `infer`'s
    domain declares a signature, so the program contributes nothing. F1b's `def`
    and W8's `sig`s are what make it non-constant, and threading it now is what
    keeps that change local — the same argument L137 makes for heap-indexing a
    judgement whose arms do not yet read the heap. -/
def declsOf (_p : Expr) : Decls := baseDecls

/-- **The table `--assn` reports against** (L195). Same rows, one more constant, and
    the difference is `T`. Placed here rather than inside `declsOf` because
    `check_sound` establishes `Inv` at the *bare boot* heap, where `T` does not exist:
    the boot-safe table and the prelude-aware one are two tables, each sound at the
    heap it describes. `scripts/consts_probe.lean` decides this one's obligation at the
    booted heap and `check-proofs.sh` runs it. -/
def preludeDecls : Decls := { baseDecls with consts := preludeConsts }




/-- P0's table, recovered. Kept as a checked fact rather than a comment so that
    "F1a accepts no new programs" has a witness in the build. -/
example : sigOf baseDecls .int "+" = some ([Ty.int], Ty.int) := by
  simp [sigOf, declFor, declOf?, declsFor, baseDecls, tyClassNames]

example : sigOf baseDecls .int "/" = none := by
  simp [sigOf, declFor, declOf?, declsFor, baseDecls, tyClassNames]

/-- Nothing is declared on the two-class type, and `declFor` says so by
    *agreement* failing rather than by the type being absent — the case that
    matters once anything is declared on one of `TrueClass`/`FalseClass`. -/
example : sigOf baseDecls .bool "+" = none := by
  simp [sigOf, declFor, declOf?, declsFor, baseDecls, tyClassNames]

/-- The `def` side condition agrees with P0's three-name exclusion. -/
example : declaresName baseDecls "+" = true := by
  simp [declaresName, baseDecls]

example : declaresName baseDecls "f" = false := by
  simp [declaresName, baseDecls]

end RubyCore.Types
