import RubyCore.Types.OpenSelf
import RubyCore.Types.Discharge

/-!
# L263 — `inferProgram`: the open front end, over a whole program

`inferOpen` refuses `def` and `class` (`Types/OpenSelf.lean`'s two `outOfFragment` arms),
and the reason it gives is about the *body* it was built for: `infer`'s `def` arm requires
`defFree body`, so a body that declares a method is outside the nominal fragment already,
and keeping the table fixed is what makes `inferOpen_factors`' conclusion carry `D` in both
positions.

That reason is sound and it is not a reason to refuse a **program**. A program is exactly a
sequence of `class`es and `def`s, and typing one is a different question with a different
answer:

> what would the types have to be for this program's constraints to be satisfiable?

This file answers it, and the answer is an assertion.

## The pass is a *driver*, not an extension of `inferOpen`

`inferProgram` walks the **declaration-shaped** constructors — `seq`, `class'`, `module'`,
`scopedClass`/`scopedModule`, `def'`, `defs`, `begin'` — and hands every *expression* to
`inferOpen` unchanged. So:

* `inferOpen` gains no arm, and `inferOpen_factors`, `inferOpen_mono` and their four
  companions are untouched. Each body's typing is still a nominal typing.
* What is new is between bodies, and that is where the new theorem is
  (`Proof/Static/Discharge.lean`'s `discharge_sound`).

The cost of being a driver rather than an arm is stated rather than hidden: a `def` nested
inside a **method body** is still refused, by `inferOpen`. Nothing in the slice has one.

## One variable per class, and that is the whole mechanism

`bodyReports` gives every body a *fresh* store at `{}` and `self := 0`, so two bodies of one
class share nothing and no requirement can ever be answered. Here every class name has

* **`α_C`** — an *instance* of `C`, which is `self` inside every `def` of `C`; and
* **`β_C`** — the *class object* `C`, which is `self` inside `class C … end`'s own body.

allocated once, from one counter, into one store. So the requirement a `vcall` in one body
records and the provision the `def` next to it supplies land at the same variable, and
`discharge` cancels them. That cancellation is the deliverable: a program whose classes
answer their own bodies closes to `emp`.

**Two variables and not one**, because `self` in a class body is the class and `self` in a
method body is an instance — the same conflation `infer` avoids by refusing `self` when
`selfCls` is `none`. Merging them would let `attr_accessor :x` in a class body discharge a
`x` requirement from a method body, which is false.

## What it does not claim

A program-level accept reads **"types under these class obligations"**. That is weaker than
`--assn`'s per-body accept (which is already only *types under this precondition*, never
*is safe* — `homebrew/slice-verdict.md` §1) and much weaker than `check`'s `accept`, which
is the only verdict `check_sound` licenses. Nothing in this file feeds `check`.

## Three deliberate refusals

* **A `def` under an `if` or a `while` provides nothing.** It may not run, so recording its
  row as a provision would be a claim the program does not support. The pass answers
  `outOfFragment "def-in-if"` rather than pretending either way.
* **A `def` whose parameters are not all required positionals provides nothing** — it
  accepts a *range* of arities and `ASig` records one (`Types/Discharge.lean`'s second
  refusal). Its body is still typed, and its callers' requirements simply survive.
* **No provision is seeded from a superclass.** `class Foo < Formula` is typed exactly as
  `class Foo`, and the requirements survive as `Foo ⊒ R`. Seeding `Formula`'s rows onto
  `α_Foo` would be a *false* provision: `SatProvs` obliges `sigOf D (θ α) n` to answer, and
  `sigOf` does not walk ancestors, so the premise `discharge_sound` needs would not hold.
  The obligation is the honest output, and inheritance is what discharges an obligation.
-/

namespace RubyCore.Types

/-! ## 1. The pass's state -/

/-- `OState` **plus** the two name→variable maps.

    A separate structure rather than two more fields on `OState`, and the reason is the
    metatheory: `OState` appears in the statement of every lemma in
    `Proof/Static/OpenSelf.lean` — `inferOpen_mono`, `inferOpen_rets`, the five `Factors`
    motives — and a new field would re-elaborate all of them for a field none of them
    reads. `inferOpen` is handed `s.o` and hands one back. -/
structure PState where
  o : OState := {}
  /-- `α_C` — an instance of `C`. `self` inside every `def` of `C`. -/
  selves : List (String × TyVar) := []
  /-- `β_C` — the class object `C`. `self` inside `class C … end`'s body. -/
  metas : List (String × TyVar) := []
deriving Repr, Inhabited

/-- Allocate-or-look-up. The *allocate* half is why this returns a state: the variable has
    to come from the same counter every body's fresh variables come from, or two classes
    could be handed the same one. -/
def PState.selfOf (s : PState) (c : String) : TyVar × PState :=
  match s.selves.find? (·.1 == c) with
  | some (_, α) => (α, s)
  | none =>
    (s.o.fresh, { s with o := { s.o with fresh := s.o.fresh + 1 },
                         selves := (c, s.o.fresh) :: s.selves })

/-- `selfOf`'s twin at the class object. -/
def PState.metaOf (s : PState) (c : String) : TyVar × PState :=
  match s.metas.find? (·.1 == c) with
  | some (_, β) => (β, s)
  | none =>
    (s.o.fresh, { s with o := { s.o with fresh := s.o.fresh + 1 },
                         metas := (c, s.o.fresh) :: s.metas })

/-- The pass's answer. `OResult`'s three constructors at `PState`; the failures are
    forwarded verbatim, because §11's whole value is in *which* construct stopped the
    program and a driver that collapsed them would throw that away. -/
inductive PResult where
  | ok (τ : ATy) (Γ : AEnv) (s : PState)
  | missing (τ : ATy) (n : String) (params : List ATy)
  | outOfFragment (head : String)
deriving Repr

/-- Lift `inferOpen`'s answer, re-attaching the maps it does not know about. -/
def PResult.ofOpen (s : PState) : OResult → PResult
  | .ok τ Γ o => .ok τ Γ { s with o := o }
  | .missing τ n ps => .missing τ n ps
  | .outOfFragment h => .outOfFragment h

/-! ## 2. The provision a `def` supplies

Read off `openParams`' **output**, never mirrored from its allocation order.
`openParamTys` exists and cannot be used here: it hard-codes `1, 2, …, n`, which is right
under `inferBodyWith`'s convention (`fresh` starts at `1`) and wrong under a shared counter.
That mirror is the kind of copy this project has been burned by twice (`SUPPORTED`), and
here it would be a *soundness* bug rather than a stale report — a provision at the wrong
variables would cancel a requirement it does not answer. -/

/-- Are all the parameters required positionals? Exactly when the `def`'s arity is a
    single number, which is exactly when `ASig` can record it. -/
def allRequired (ps : List Param) : Bool :=
  ps.all fun p => match p with | .req _ => true | _ => false

/-- The parameter types the body was actually opened at, in source order — `Γ_b`'s
    payloads. Sound to use as a signature only when `allRequired`, because that is when
    `openParams` binds one entry per parameter and nothing else. -/
def paramTysOf (Γb : AEnv) : List ATy := Γb.map (·.2)

/-! ## 3. The pass -/

mutual

/-- Type a program — or any declaration-shaped fragment of one — in class scope `cls`,
    with `selfV` standing for `self`.

    `selfV` is a parameter rather than derived from `cls` because the two `self`s of a class
    differ: a `def` body's is `α_cls`, a class body's is `β_cls`. -/
def inferProgram (D : Decls) (Γ : AEnv) (e : Expr) (cls : String) (selfV : TyVar)
    (s : PState) : PResult :=
  match e with
  | .seq es => inferProgramSeq D Γ es cls selfV s
  -- `begin … end` with no handlers is its body; a handler is a second control path whose
  -- environment join this pass has no rule for, so it is named rather than approximated.
  | .begin' body [] none none => inferProgram D Γ body cls selfV s
  | .begin' _ _ _ _ => .outOfFragment "begin-handlers"
  -- **A class body**, in its own frame: no locals, and `self` is the class object. The
  -- superclass is *recorded and not seeded* — see the header's third refusal.
  | .class' name sup body =>
    match sup with
    | none => inferClassBody D name body s
    | some (.const _) => inferClassBody D name body s
    | some (.cpath _ _) => inferClassBody D name body s
    | some _ => .outOfFragment "class-superclass-expr"
  | .module' name body => inferClassBody D name body s
  | .scopedClass _ name body => inferClassBody D name body s
  | .scopedModule _ name body => inferClassBody D name body s
  -- `class << obj` reopens the eigenclass of a *value*, and the pass has no variable for
  -- the eigenclass of anything but a class name. Named, not approximated.
  | .sclass _ _ => .outOfFragment "sclass"
  -- **The rung.** An instance method: provisions land on `α_cls`.
  | .def' n ps body =>
    let (α, s₁) := s.selfOf cls
    inferDefBody D cls n ps body α s₁ Γ
  -- **A singleton method** — `def self.x` — provisions land on `β_cls`, the class object,
  -- which is where the method really is installed. A receiver that is not `self` is a
  -- different object and the pass has no variable for it.
  | .defs (.self') n ps body =>
    let (β, s₁) := s.metaOf cls
    -- **The name is not prefixed**, unlike `bodyReports`' display convention: the method
    -- really is called `n`, and what says it is a singleton is the *variable* it is
    -- provisioned at. A `self.` prefix here would leave `Foo.make` in the class body
    -- requiring `make` on `β_Foo` while the provision sat under a name nothing asks for —
    -- a silent failure to cancel.
    inferDefBody D cls n ps body β s₁ Γ
  | .defs _ _ _ _ => .outOfFragment "defs-receiver"
  -- **Everything else is an expression**, and goes to `inferOpen` unchanged. The
  -- `defFree` guard is what makes that safe *and* is the honest refusal for a `def` in a
  -- position this pass has no rule for: the label names the construct it was under, so
  -- `def` inside an `if` reads `def-in-if` rather than disappearing into `if`.
  | e =>
    if defFree e then
      PResult.ofOpen s
        (inferOpen D Γ e { cls := cls, self := selfV } none s.o)
    else .outOfFragment ("def-in-" ++ headName e)

/-- A class or module body. Its own frame, so the environment it is typed in is empty and
    the caller's is handed back untouched; its value is the body's, as `infer`'s `class'`
    arm has it.

    `rets` is saved and restored for `inferDefBody`'s reason. -/
def inferClassBody (D : Decls) (name : String) (body : Expr) (s : PState) : PResult :=
  let (β, s₁) := s.metaOf name
  match inferProgram D [] body name β { s₁ with o := { s₁.o with rets := [] } } with
  | .ok τ _ s' => .ok τ [] { s' with o := { s'.o with rets := s₁.o.rets } }
  | r => r

/-- One `def`'s body, typed with its parameters open and its answer recorded as a
    **provision** on `selfV`.

    Three pieces of bookkeeping, each with a reason:

    * **`rets := []` around the body, restored after.** `OState.rets` accumulates what
      every `return` in *this* body handed back and `joinRets` spends it at the end
      (L201/L229); a shared state means the enclosing scope's must not be spent here, and
      this body's must not leak out.
    * **the store and the counter are *not* reset.** That is the entire point: a
      requirement this body records has to be visible to the sibling `def` that answers it.
    * **`ctx.params` is read off `Γ_b`**, and only when `allRequired` — see §2.

    The `def` itself evaluates to a Symbol (`Types/Core.lean`'s arm, and
    `Interp.lean:2624`), so that is the type, and the caller's environment is unchanged. -/
def inferDefBody (D : Decls) (cls n : String) (ps : List Param) (body : Expr)
    (selfV : TyVar) (s : PState) (Γ : AEnv) : PResult :=
  -- `params := none` while the *defaults* are typed: a default is an expression in the
  -- callee frame and the parameter list is not built yet, so a `zsuper` inside one has
  -- nothing to forward. All-required lists have no defaults, so this costs them nothing.
  let ctx₀ : OCtx := { cls := cls, self := selfV, meth := some n, params := none }
  match openParams D ctx₀ ps [] { s.o with rets := [] } with
  | none => .outOfFragment ("def-params-" ++ (firstUnbound ps).getD "dflt")
  | some (Γb, o₁) =>
    let ctx : OCtx :=
      { ctx₀ with params := if allRequired ps then some (paramTysOf Γb) else none }
    match inferOpen D Γb body ctx none o₁ with
    | .ok τ _ o₂ =>
      match joinRets o₂.rets τ with
      | none => .outOfFragment "return-join"
      | some τj =>
        let o₃ : OState := { o₂ with rets := s.o.rets }
        if allRequired ps then
          match o₃.st.addProv selfV n { params := paramTysOf Γb, ret := τj } with
          | some st' => .ok (.nom .sym) Γ { s with o := { o₃ with st := st' } }
          -- ★★ upstream: two `def`s of this name at different signatures. No provision,
          -- so the callers' requirements survive — a refusal to cancel, not a wrong one.
          | none => .ok (.nom .sym) Γ { s with o := o₃ }
        else .ok (.nom .sym) Γ { s with o := o₃ }
    | .missing τ m ps' => .missing τ m ps'
    | .outOfFragment h => .outOfFragment h

/-- The statement sequence, threading the environment and the state. `inferOpenSeq`'s shape
    at the driver, and it cannot delegate to it: a `seq` is where the `def`s are. -/
def inferProgramSeq (D : Decls) (Γ : AEnv) (es : List Expr) (cls : String) (selfV : TyVar)
    (s : PState) : PResult :=
  match es with
  | [] => .ok (.nom .nilT) Γ s
  | [e] => inferProgram D Γ e cls selfV s
  | e :: rest =>
    match inferProgram D Γ e cls selfV s with
    | .ok _ Γ₁ s₁ => inferProgramSeq D Γ₁ rest cls selfV s₁
    | r => r

end

/-! ## 4. The whole-program verdict -/

/-- What the pass concluded about a program, in the shape §11 prints a body's verdict.

    `assn` is the answer: the discharged store, with every *instance* variable closed into
    a class obligation. What is left is `C ⊒ R` per class that wants something it does not
    supply, plus the residual `req`/`eqv` atoms — and `emp` when a program answers
    itself. -/
inductive ProgramVerdict where
  /-- Types, under this assertion. `ty` is the program's own value type. -/
  | acceptedUnder (ty : ATy) (assn : Assn) (classes : List (String × TyVar × Option TyVar))
  | blocked (τ : ATy) (n : String) (params : List ATy)
  | outOfFragment (head : String)
deriving Repr, DecidableEq

/-- Close every class's *instance* variable into an obligation on its name (§7.3's
    `Σ ∖ α ∧ (c ⊒ R)`, once per class).

    **Class-object variables are left open**, and that is not an oversight: `Assn.obl c R`
    reads *`C`'s instances satisfy `R`*, and a row on `β_C` is about the class object, so
    closing it at the same key would assert something false. It stays a `req (.var β) …`
    atom, and `ProgramVerdict.classes` says which class each variable belongs to so the
    atom is readable. Giving it a nominal home is what `Ty.clsOf` is for, and that is the
    next rung — it wants the ground case, which is `new`. -/
def closeClasses (s : PState) (st : Store) : Store :=
  s.selves.foldl (fun acc e => acc.closeAt e.2 e.1) st

/-- The program's verdict: run the pass, cancel, close, render. -/
def programVerdict (D : Decls) (prog : Expr) : ProgramVerdict :=
  let (α, s₀) := (PState.mk {} [] []).selfOf "Object"
  match inferProgram D [] prog "Object" α s₀ with
  | .ok τ _ s =>
    .acceptedUnder τ (closeClasses s (discharge s.o.st)).toAssn
      -- **`Option` for the class-object variable**, because a class whose body was never
      -- entered has none — a toplevel `def` puts `Object` in `selves` and nothing in
      -- `metas`, and reporting `0` there would collide with a real variable.
      (s.selves.map fun e =>
        (e.1, e.2, (s.metas.find? (·.1 == e.1)).map (·.2)))
  | .missing τ n ps => .blocked τ n ps
  | .outOfFragment h => .outOfFragment h

/-! ## 5. Examples — the shapes the header claims

`simp` over the equation lemmas rather than `decide`: the pass is a `mutual` block, so it
is compiled by well-founded recursion and does not reduce in the kernel — the same reason
`Types/OpenSelf.lean`'s examples name `inferOpen` in their `simp` set. `native_decide` is
banned outright (`PLAN.md` §4 norm 5). -/

/-- **The deliverable.** A class that answers its own body: the `vcall` in `get` requires
    `value` on `α_String`, the `def value` beside it supplies it, `discharge` cancels, and
    the class obligation closes **empty** — so the whole assertion is the one equality the
    cancellation owed. This is what `bodyReports` structurally cannot say: it gives each
    body its own store at `{}`, so the two halves never meet. -/
example :
    programVerdict baseDecls
        (.class' "String" none (.seq [
          .def' "value" [] (.int 1),
          .def' "get" [] (.vcall "value")]))
      = .acceptedUnder (.nom .sym) (.eqv 3 (.nom .int))
          [("String", 2, some 1), ("Object", 0, none)] := by
  simp [programVerdict, inferProgram, inferProgramSeq, inferClassBody, inferDefBody,
    inferOpen, PState.selfOf, PState.metaOf, openParams, allRequired, paramTysOf,
    joinRets, requireRow, closeClasses, discharge, dischargeRows, dischargeEntries,
    dischargeSig, pinPair, pinPairs, Store.addProv, Store.provOf, Store.rowIn,
    Store.rowOf, Store.setRow, Store.closeAt, Store.toAssn, Row.get?, Row.insert,
    Row.empty, Assn.all, defFree]

/-- **Parameters, cancelled across two bodies** — the case `infer`'s own `def` rule cannot
    reach at all (`params.isEmpty`). `add`'s parameter is opened at `α₃`, `use` calls it at
    `Integer`, and the two equalities are exactly the solved instantiation: the parameter
    is an `Integer` and the call's result is whatever the parameter was. -/
example :
    programVerdict baseDecls
        (.class' "String" none (.seq [
          .def' "add" [.req "a"] (.var .lvar "a"),
          .def' "use" [] (.send none "add" [.int 1] none)]))
      = .acceptedUnder (.nom .sym)
          (.and (.eqv 3 (.nom .int)) (.eqv 4 (.var 3)))
          [("String", 2, some 1), ("Object", 0, none)] := by
  simp [programVerdict, inferProgram, inferProgramSeq, inferClassBody, inferDefBody,
    inferOpen, PState.selfOf, PState.metaOf, openParams, allRequired, paramTysOf,
    joinRets, requireRow, closeClasses, discharge, dischargeRows, dischargeEntries,
    dischargeSig, pinPair, pinPairs, Store.addProv, Store.provOf, Store.rowIn,
    Store.rowOf, Store.setRow, Store.closeAt, Store.toAssn, Row.get?, Row.insert,
    Row.empty, Assn.all, PResult.ofOpen, aenvGet?, inferOpenArgs, defFree, isSelf,
    sigOf, declFor, declOf?, declsFor, baseDecls, Store.addEq, subATy]

/-- **The Homebrew shape.** An unknown superclass and a body calling a method it inherits:
    nothing supplies `system`, so the requirement survives the cancellation and
    `closeClasses` turns it into the obligation `Foo ⊒ ⟨ system : (String) → α₃ ⟩` — which
    is the honest statement that `Formula`, which no table describes, must declare it. -/
example :
    programVerdict baseDecls
        (.class' "Foo" (some (.const "Formula"))
          (.def' "install" [] (.send none "system" [.str "make"] none)))
      = .acceptedUnder (.nom .sym)
          (.obl "Foo" { entries := [("system", { params := [.nom (.cls "String")],
                                                 ret := .var 3 })] })
          [("Foo", 2, some 1), ("Object", 0, none)] := by
  simp [programVerdict, inferProgram, inferProgramSeq, inferClassBody, inferDefBody,
    inferOpen, PState.selfOf, PState.metaOf, openParams, allRequired, paramTysOf,
    joinRets, requireRow, closeClasses, discharge, dischargeRows, dischargeEntries,
    dischargeSig, pinPair, pinPairs, Store.addProv, Store.provOf, Store.rowIn,
    Store.rowOf, Store.setRow, Store.closeAt, Store.toAssn, Row.get?, Row.insert,
    Row.empty, Assn.all, PResult.ofOpen, aenvGet?, inferOpenArgs, defFree, isSelf,
    sigOf, declFor, declOf?, declsFor, baseDecls, Store.addEq, subATy]

/-- **An optional parameter provides nothing**, and the body still types. `add` accepts
    zero *or* one argument and `ASig` records one arity, so no provision is recorded and
    `use`'s requirement survives — a weaker output, never a wrong cancellation. -/
example :
    programVerdict baseDecls
        (.class' "String" none (.seq [
          .def' "add" [.opt "a" (.int 0)] (.var .lvar "a"),
          .def' "use" [] (.send none "add" [.int 1] none)]))
      = .acceptedUnder (.nom .sym)
          (.obl "String" { entries := [("add", { params := [.nom .int],
                                                 ret := .var 3 })] })
          [("String", 2, some 1), ("Object", 0, none)] := by
  simp [programVerdict, inferProgram, inferProgramSeq, inferClassBody, inferDefBody,
    inferOpen, PState.selfOf, PState.metaOf, openParams, allRequired, paramTysOf,
    joinRets, requireRow, closeClasses, discharge, dischargeRows, dischargeEntries,
    dischargeSig, pinPair, pinPairs, Store.addProv, Store.provOf, Store.rowIn,
    Store.rowOf, Store.setRow, Store.closeAt, Store.toAssn, Row.get?, Row.insert,
    Row.empty, Assn.all, PResult.ofOpen, aenvGet?, inferOpenArgs, defFree, isSelf,
    sigOf, declFor, declOf?, declsFor, baseDecls, Store.addEq, subATy]

/-- **`def self.x` lands on the class object**, and a call in the class body finds it
    there. The two `self`s are different variables and that is what makes this work: had
    they been merged, this would have cancelled against an *instance* row. -/
example :
    programVerdict baseDecls
        (.class' "Foo" none (.seq [.defs .self' "make" [] (.int 1), .vcall "make"]))
      = .acceptedUnder (.var 2) (.eqv 2 (.nom .int)) [("Object", 0, none)] := by
  simp [programVerdict, inferProgram, inferProgramSeq, inferClassBody, inferDefBody,
    inferOpen, PState.selfOf, PState.metaOf, openParams, allRequired, paramTysOf,
    joinRets, requireRow, closeClasses, discharge, dischargeRows, dischargeEntries,
    dischargeSig, pinPair, pinPairs, Store.addProv, Store.provOf, Store.rowIn,
    Store.rowOf, Store.setRow, Store.closeAt, Store.toAssn, Row.get?, Row.insert,
    Row.empty, Assn.all, PResult.ofOpen, aenvGet?, inferOpenArgs, defFree, isSelf,
    sigOf, declFor, declOf?, declsFor, baseDecls, Store.addEq, subATy]

/-- **A toplevel `def`, called** — `Object` is the class and the cancellation is the same
    one. (`infer`'s table refuses this row for a different and correct reason: a toplevel
    `def` installs a *private* method, L162. An assertion is not a table.) -/
example :
    programVerdict baseDecls (.seq [.def' "f" [] (.int 1), .vcall "f"])
      = .acceptedUnder (.var 1) (.eqv 1 (.nom .int)) [("Object", 0, none)] := by
  simp [programVerdict, inferProgram, inferProgramSeq, inferClassBody, inferDefBody,
    inferOpen, PState.selfOf, PState.metaOf, openParams, allRequired, paramTysOf,
    joinRets, requireRow, closeClasses, discharge, dischargeRows, dischargeEntries,
    dischargeSig, pinPair, pinPairs, Store.addProv, Store.provOf, Store.rowIn,
    Store.rowOf, Store.setRow, Store.closeAt, Store.toAssn, Row.get?, Row.insert,
    Row.empty, Assn.all, PResult.ofOpen, aenvGet?, inferOpenArgs, defFree, isSelf,
    sigOf, declFor, declOf?, declsFor, baseDecls, Store.addEq, subATy]

/-- **A `def` under an `if` provides nothing**, and says so by name rather than
    disappearing into the `if`: it may not run, so recording its row would be a claim the
    program does not support. -/
example :
    programVerdict baseDecls (.if' .tru (.def' "f" [] (.int 1)) none)
      = .outOfFragment "def-in-if" := by
  simp [programVerdict, inferProgram, PState.selfOf, defFree, headName]

end RubyCore.Types
