/-
The executable step function (lean-model-sketch §3): `stepFn` is one
small-step transition of the machine; `run` iterates it under fuel.

The inductive `Step : Config → Config → Prop` (the definition of record)
will be authored against this — `stepFn` is its constructive witness; for
now the interpreter comes first so the model can meet the difftest engine
immediately (sketch §4). Note the helpers below are NOT mutually recursive:
each performs exactly one transition — evidence the machine really is
small-step.

Out-of-fragment RubyCore constructs surface as `.unsupported` — the SUT
contract's clean gate, never a guessed value.
-/
import RubyCore.Interp.Kont

namespace RubyCore

namespace Interp

/-- `defined?(e)` (artifact 03 §6, L67). The operand is **not** evaluated — the
    answer comes from the shape of `e` plus a heap/frame lookup — except a send's
    receiver and a cpath's base, which CRuby does evaluate (under a guard that
    turns any raise into nil). Strings are CRuby's exact spellings [V]. -/
def evalDefined (m : Machine) (e : Expr) : StepResult :=
  let str : String → StepResult := fun s =>
    let (v, m) := Builtins.allocStr m s
    .next (withCtl m (.value v))
  let nilR : StepResult := .next (withCtl m (.value .nil))
  let strIf : Bool → String → StepResult := fun b s => if b then str s else nilR
  match e with
  | .nil => str "nil"
  | .tru => str "true"
  | .fls => str "false"
  | .self' => str "self"
  | .var .lvar _ =>
    -- Always "local-variable" — and this is *exact*, not an approximation: the
    -- desugarer only emits a `var local` node for a name the parser knows to be a
    -- local in this scope (an unknown bare name becomes a vcall `send`), which is
    -- precisely CRuby's static rule. So `y = 1 if false; defined?(y)` answers
    -- "local-variable" even though no binding exists at runtime [V] (L72).
    str "local-variable"
  | .var .ivar x =>
    let has := match m.currentFrame.self with
      | .ref o => (m.heap.get o).ivars.any (·.1 == x)
      | _ => false
    strIf has "instance-variable"
  | .var .gvar x =>
    let has :=
      if x == "$!" then m.currentExc.isSome
      -- `$~` is *always* "global-variable", match or not — unlike its views, where
      -- `defined?($1)` with no match is nil [V] (L121). It used to answer from
      -- `globals`, which happened to agree only because any match attempt put the
      -- key there; frame-local storage has no such key to consult.
      else if x == "$~" then true
      else match matchGlobal m x with
        -- a match global is "defined" exactly when the last match filled it [V]
        | some (v, _) => match v with | .nil => false | _ => true
        | none => m.globals.any (·.1 == x)
    strIf has "global-variable"
  | .var .cvar x =>
    -- `defined?(@@a)` at toplevel is nil, *not* the access RuntimeError [V]
    match cvarScope m with
    | none => .unsupported "defined?(@@x) in a singleton-class scope"
    | some scope => strIf (cvarLookupIn m.heap scope x).isSome "class variable"
  | .const n =>
    let lexical := m.currentFrame.cref.firstM (fun c => constOwn m.heap c n)
    match lexical.orElse (fun _ => constLookupFrom m.heap m.currentFrame.defmod n) with
    | some _ => str "constant"
    | none =>
      -- same fidelity split as a constant *read*: a constant CRuby has but we
      -- don't model must not answer nil.
      if (crubyToplevelConstants.contains n || crubyStdlibConstants.contains n) then .unsupported s!"defined?(unmodeled constant {n})"
      else nilR
  | .cpath (some base) name =>
    -- the base *is* evaluated (`defined?(A::B)` runs `A`), under the guard
    let k := Kont.definedCpathK name :: Kont.definedGuardK :: m.kont
    let m := { m with ctl := Ctl.eval base, kont := k }
    .next m
  | .cpath none name =>
    match constLookup m.heap name with
    | some _ => str "constant"
    | none =>
      if (crubyToplevelConstants.contains name || crubyStdlibConstants.contains name) then
        .unsupported s!"defined?(unmodeled constant {name})"
      else nilR
  | .send none mname _ _ | .vcall mname =>
    -- implicit self: method existence only; args are never evaluated [V].
    -- `defined?(foo)` on a vcall answers "method" too when it resolves — the
    -- local-variable case never reaches here (the desugarer emits `var`).
    match definedMethod? m m.currentFrame.self mname with
    | some b => strIf b "method"
    | none => .unsupported s!"defined?(unmodeled method {mname})"
  | .send (some recv) mname _ _ =>
    let k := Kont.definedRecvK mname :: Kont.definedGuardK :: m.kont
    let m := { m with ctl := Ctl.eval recv, kont := k }
    .next m
  | .yield' _ => strIf m.currentFrame.blk.isSome "yield"
  | .super' .. | .zsuper .. =>
    -- would `super` find a method? (no call, artifact 02 §2) [V]
    let f := m.frames.getD (methodFrameOf m) default
    if f.meth == "" then nilR
    else
      let after := ((ancestors m.heap (classOf m.heap f.self)).dropWhile (· != f.defmod)).drop 1
      let found := after.any fun c =>
        match m.heap.classPayload? c with
        | some cp => match cp.methods.find? (·.1 == f.meth) with
          | some (_, md) => !md.undefined
          | none => false
        | none => false
      if found then str "super"
      else if (crubyShadow m.heap after f.meth).isSome then
        .unsupported s!"defined?(super) of unmodeled method {f.meth}"
      else nilR
  | .vasgn .. | .casgn .. | .cpathAsgn .. => str "assignment"
  | _ => str "expression"

/-- Evaluate one expression head. -/
def evalExpr (m : Machine) (e : Expr) : StepResult :=
  match e with
  | .int n => .next (withCtl m (.value (.int n)))
  | .flt x => .next (withCtl m (.value (.flt x)))
  | .str s =>
    -- string literals allocate a fresh unfrozen String [V]
    let (v, m) := Builtins.allocStr m s
    .next (withCtl m (.value v))
  | .sym s => .next (withCtl m (.value (.sym s)))
  | .tru => .next (withCtl m (.value (.bool true)))
  | .fls => .next (withCtl m (.value (.bool false)))
  | .nil => .next (withCtl m (.value .nil))
  | .self' => .next (withCtl m (.value m.currentFrame.self))
  | .var kind x =>
    match kind with
    | .lvar => .next (withCtl m (.value (m.getLocal x)))
    | .gvar =>
      match matchGlobal m x with
      | some (v, m) => .next (withCtl m (.value v))
      | none => .next (withCtl m (.value (m.getGlobal x)))
    | .ivar =>
      match m.currentFrame.self with
      | .ref o =>
        let v := ((m.heap.get o).ivars.find? (·.1 == x)).map (·.2) |>.getD .nil
        .next (withCtl m (.value v))
      | _ => .next (withCtl m (.value .nil))  -- unset ivar on immediate self → nil
    | .cvar =>
      match cvarScope m with
      | none => .unsupported "class variable in a singleton-class scope"
      | some scope =>
        if scope == Boot.objectId && m.currentFrame.kind == .toplevel then
          .next (raiseErr m Boot.runtimeErrorId "class variable access from toplevel")
        else
          match cvarLookupIn m.heap scope x with
          | some v => .next (withCtl m (.value v))
          | none =>
            .next (raiseErr m Boot.nameErrorId
              s!"uninitialized class variable {x} in {className m.heap scope}")
  | .vasgn kind x rhs => .next (withKont m (.eval rhs) (.asgnK kind x))
  | .const n =>
    -- artifact 03 §4: lexical phase (each cref scope's OWN consts, innermost
    -- first), then inheritance phase (ancestors of the innermost class/defmod).
    let lexical := m.currentFrame.cref.firstM (fun c => constOwn m.heap c n)
    match lexical.orElse (fun _ => constLookupFrom m.heap m.currentFrame.defmod n) with
    | some v => .next (withCtl m (.value v))
    | none =>
      -- same fidelity split as methods: a constant CRuby has but we don't
      -- model gates as Unsupported; a genuine miss is a real NameError
      if (crubyToplevelConstants.contains n || crubyStdlibConstants.contains n) then
        .unsupported s!"unmodeled constant {n}"
      else
        -- CRuby qualifies the miss with the **innermost cref**, not the bare
        -- name: inside `module A; class B` a missing `Foo` is
        -- `uninitialized constant A::B::Foo` [V]. Toplevel (cref empty or
        -- Object) keeps the bare form.
        let pre := match m.currentFrame.cref with
          | c :: _ => if c == Boot.objectId then "" else className m.heap c ++ "::"
          | [] => ""
        .next (raiseErr m Boot.nameErrorId s!"uninitialized constant {pre}{n}")
  | .casgn n rhs => .next (withKont m (.eval rhs) (.casgnK n))
  | .cpath base name =>
    match base with
    | none =>
      -- `::name` — absolute toplevel (Object namespace)
      match constLookup m.heap name with
      | some v => .next (withCtl m (.value v))
      | none =>
        if (crubyToplevelConstants.contains name || crubyStdlibConstants.contains name) then .unsupported s!"unmodeled constant {name}"
        else .next (raiseErr m Boot.nameErrorId s!"uninitialized constant {name}")
    | some baseExpr => .next (withKont m (.eval baseExpr) (.cpathK name))
  | .cpathAsgn base name rhs =>
    -- eval order: base then rhs [V]. `::name = rhs` sets on Object.
    match base with
    | none => .next (withKont m (.eval rhs) (.cpathAsgnValK name Boot.objectId))
    | some baseExpr => .next (withKont m (.eval baseExpr) (.cpathAsgnK name rhs))
  | .send recv mname args blk =>
    let pblk : PendingBlk := match blk with
      | none => .none
      | some (.block ps ls body) => .lit ps ls body
      | some (.blockpass (some e)) => .passExpr e
      | some (.blockpass none) => .passAnon
      | some _ => .none  -- desugar guarantees blk ∈ {block, blockpass}; unreachable
    match recv with
    | some r =>
      -- a *literal* `self.m` may call private methods (Ruby 2.7+), while any other
      -- receiver may not — so the site kind is decided here, syntactically [V].
      let site : SendSite := match r with | .self' => .selfRecv | _ => .explicit
      .next (withKont m (.eval r) (.recvK mname args pblk site))
    | none =>
      -- **J33: `define_method(:name) { … }` composes to one step.** The literal
      -- symbol's evaluation is pure (no heap effect), so the three-step route
      -- (push argsK / deliver the symbol / dispatch) and this direct dispatch
      -- have byte-identical observable behaviour — only the step count differs.
      -- Composing it is what makes the construct's *semantic-claim obligation*
      -- provable: the invariant need not cover the intermediate `argsK` state,
      -- whose `KontOkJ` constructor demands a declared row `define_method`
      -- cannot have. Scrutinize `pblk` first so block-less sends (the syntactic
      -- fragment) reduce past this match with `mname`/`args` still symbolic.
      match pblk with
      | .lit ps ls body =>
        match mname, args with
        | "define_method", [.sym nm] =>
          finishSend m m.currentFrame.self .implicit "define_method" [.sym nm]
            (.lit ps ls body)
        | mname, args =>
          startArgs m m.currentFrame.self .implicit mname [] args (.lit ps ls body)
      | pblk => startArgs m m.currentFrame.self .implicit mname [] args pblk
  -- A vcall is an implicit-self, zero-arg, block-less send; only the miss
  -- message differs (L75), and that is carried by the `.vcall` site.
  | .vcall mname => startArgs m m.currentFrame.self .vcall mname [] [] .none
  | .block .. => .stuck "bare block node outside send"
  | .kwargs .. => .stuck "bare kwargs node outside call position"
  | .fwd => .stuck "bare fwd (...) node outside call position"
  | .yield' args => startYield m [] args
  | .blockpass .. => .stuck "bare blockpass node outside send"
  | .if' c t e => .next (withKont m (.eval c) (.ifK t e))
  | .while' c body => .next (withKont m (.eval c) (.whileCondK c body))
  | .dowhile body cond =>
    -- run body once, then behave as `while cond`: `whileBodyK` already
    -- sequences "after body → eval cond (whileCondK) → loop", and `unwind`
    -- already routes break/next through it [V].
    .next (withKont m (.eval body) (.whileBodyK cond body))
  | .for' targets coll body =>
    .next (withKont m (.eval coll) (.forStartK targets body))
  | .def' name params body =>
    let defmod := m.currentFrame.defmod
    let md : MethodDef :=
      { params, body, owner := defmod, cref := m.currentFrame.cref,
        fromPrelude := m.preludeMode,
        -- `private`/`protected` with no arguments set the default for the rest of
        -- the class body (artifact 02 §5); `initialize` is always private, and so
        -- is a **toplevel** `def` (a private method of Object) [V] — which is why
        -- `public def m …` at toplevel exists at all (L72).
        visibility :=
          if name == "initialize" then .priv
          else if m.currentFrame.kind == .toplevel then .priv
          else m.currentFrame.defVis }
    let m := { m with heap := defineMethod m.heap defmod name md }
    -- CRuby fires `Module#method_added(:name)` on the defining module right after
    -- installing, and `def` still evaluates to the name. The model has no builtin
    -- `method_added`, so a lookup miss means "no hook" — the common case costs one
    -- lookup. This is the hook sorbet-runtime's `sig` is built on: `sig` records a
    -- pending declaration and `method_added` wraps the method that follows, so
    -- without it a `sig` cannot enforce anything (prelude §T).
    if m.preludeMode then .next (withCtl m (.value (.sym name)))
    else
      match lookup m.heap (.ref defmod) "method_added" with
      | some (owner, hookMd) =>
        -- CRuby defines `Module#method_added` as a private no-op, which *shadows*
        -- anything further down the class object's ancestry. So a plain toplevel
        -- `def method_added` (an Object instance method, and Object comes after
        -- Module in a class object's chain) must NOT fire — verified against CRuby,
        -- which prints nothing for it. Resolving to Object/Kernel/BasicObject here
        -- means we walked past where CRuby's no-op sits: treat it as no hook.
        if hookMd.undefined
            || owner == Boot.objectId || owner == Boot.kernelId
            || owner == Boot.basicObjectId then
          .next (withCtl m (.value (.sym name)))
        else
          let m := { m with kont := .methodAddedK name :: m.kont }
          enterUserMethod m (.ref defmod) "method_added" hookMd [.sym name] none
      | none => .next (withCtl m (.value (.sym name)))
  | .defined e => evalDefined m e
  | .undef names => undefNames m m.currentFrame.defmod names
  | .alias' newN oldN =>
    -- `alias` captures the current definition of `oldN` (walking ancestors) and
    -- installs an independent copy under `newN` on the current definee; a later
    -- redefinition of `oldN` does not affect `newN` [V]. A tombstone or a
    -- genuine miss raises `NameError`. Returns nil.
    let defmod := m.currentFrame.defmod
    match methodOn m.heap defmod oldN with
    | some (_, md) =>
      if md.undefined then undefAliasMiss m oldN
      else
        -- keep the original name for `super` (L108); same-module only, see
        -- the `alias_method` rule for why
        let md := if md.owner == defmod then { md with superName := some (md.superName.getD oldN) }
                  else md
        let m := { m with heap := defineMethod m.heap defmod newN md }
        .next (withCtl m (.value .nil))
    | none => undefAliasMiss m oldN
  | .array elems => continueArray m [] elems
  | .hash pairs =>
    match pairs with
    | [] =>
      let (v, m) := Builtins.allocHsh m #[]
      .next (withCtl m (.value v))
    | (kE, vE) :: rest =>
      .next (withKont m (.eval kE) (.hshKeyK [] vE rest))
  | .splat _ => .unsupported "splat outside call/array position"
  | .ret e =>
    -- only meaningful inside a method (the desugar gates toplevel return)
    match e with
    | some e => .next (withKont m (.eval e) (.jumpValK .retK))
    | none => doReturn m .nil
  | .brk e =>
    match e with
    | some e => .next (withKont m (.eval e) (.jumpValK .brkK))
    | none => .next (withCtl m (.jump (.brkJ .nil)))
  | .nxt e =>
    match e with
    | some e => .next (withKont m (.eval e) (.jumpValK .nxtK))
    | none => .next (withCtl m (.jump (.nxtJ .nil)))
  | .retry' => .next (withCtl m (.jump .retryJ))
  | .redo' => .next (withCtl m (.jump .redoJ))
  | .begin' body rescues els ens =>
    -- gate rescue targets we can't bind yet
    if rescues.any (fun (_, ref, _) => match ref with
        | some (.cvar, _) => true | _ => false) then
      .unsupported "class-variable rescue target"
    else
      let node : BeginNode := { body, rescues, els, ens }
      .next (withKont m (.eval body) (.beginBodyK node))
  | .class' name sup body =>
    match sup with
    | some supExpr => .next (withKont m (.eval supExpr) (.classDefK name body))
    | none => enterClassBody m name false none body
  | .module' name body => enterClassBody m name true none body
  | .scopedClass base name body =>
    match base with
    | some baseExpr => .next (withKont m (.eval baseExpr) (.scopedClassDefK name false body))
    | none => .unsupported "absolute-scoped class definition (::Name)"
  | .scopedModule base name body =>
    match base with
    | some baseExpr => .next (withKont m (.eval baseExpr) (.scopedClassDefK name true body))
    | none => .unsupported "absolute-scoped module definition (::Name)"
  | .sclass obj body => .next (withKont m (.eval obj) (.sclassK body))
  | .defs recv name params body =>
    .next (withKont m (.eval recv) (.defsK name params body))
  | .super' args blk =>
    -- explicit `super(args)`; forward the method's block unless a literal one
    -- is given here (block-pass on super is beyond L2b)
    match blk with
    | none => startSuperArgs m [] args (methodBlk m)
    | some (.block ps ls body) =>
      let (v, m) := reifyBlock m ps ls body false
      startSuperArgs m [] args (some v)
    | some _ => .unsupported "super with a block-pass / anonymous block"
  | .zsuper blk =>
    -- bare `super`: forward the current param values + the method's block
    match blk with
    | none =>
      match zsuperArgs m with
      | some (args, kw) => doSuper m args (methodBlk m) kw
      | none =>
        -- A `define_method` body has no formal parameter list to forward from;
        -- CRuby raises rather than guessing [V].
        let f := m.frames.getD (methodFrameOf m) default
        if f.runFromDM then
          .next (raiseErr m Boot.runtimeErrorId
            "implicit argument passing of super from method defined by define_method() is not supported. Specify all arguments explicitly.")
        else .unsupported "zsuper param reconstruction (unsupported param shape)"
    | some _ => .unsupported "zsuper with an explicit block"
  | .seq es =>
    match es with
    | [] => .next (withCtl m (.value .nil))
    | [e] => .next (withCtl m (.eval e))
    | e :: rest => .next (withKont m (.eval e) (.seqK rest))

/-- One small step. -/
def stepFn (m : Machine) : StepResult :=
  match m.ctl with
  | .eval e => evalExpr m e
  | .value v => applyKont m v
  | .jump j => unwind m j

inductive RunResult where
  | value (v : Value) (m : Machine)
  | uncaught (exc : Value) (m : Machine)
  | unsupported (reason : String) (m : Machine)
  | outOfFuel (m : Machine)
  | stuck (msg : String) (m : Machine)

/-- Iterate `stepFn` under fuel. `outOfFuel` is distinguished from `stuck`
    from day one (sketch §5: keep co-divergence checking possible). -/
def run (fuel : Nat) (m : Machine) : RunResult :=
  match fuel with
  | 0 => .outOfFuel m
  | fuel + 1 =>
    match stepFn m with
    | .next m' => run fuel m'
    | .done v m' => .value v m'
    | .uncaught exc m' => .uncaught exc m'
    | .unsupported r => .unsupported r m
    | .stuck msg => .stuck msg m

end Interp

end RubyCore
