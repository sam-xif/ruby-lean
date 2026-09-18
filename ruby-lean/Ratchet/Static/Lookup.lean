import Ratchet.Static.Purity

/-!
# `Ratchet/Static/Lookup.lean`

**Reading the two tables**: `defDeclared?`/`defGet?` (declared versus callable, the §F3
guard stated once), the assumption table, a class body's constant literals, and the
environment a method body starts in (`paramBind` and its two wrappers).
-/

namespace Ratchet

/-- Is a method of this name **declared** at all — the raw table lookup, with no
callability filter. Read by `Judge.bareName`, whose premise means "this name is not a method
of the program" and must not be weakened by `defGet?`'s guard: a `def x` whose body declares
is still a `def x`, and a `vcall x` that reaches it is not a `NameError`. -/
def defDeclared? (D : DefTable) (m : String) : Option Defn := D.find? (·.name == m)

/-- The method a call rule may type against: declared, **and** with a body that declares
nothing (§F3 above). Every body-fetching lookup in this file goes through here — top-level
methods, instance and singleton methods (`defGet? c.methods`, `mroGet?`), and `resolveAliases`
— so the guard is stated once. -/
def defGet? (D : DefTable) (m : String) : Option Defn :=
  match D.find? (·.name == m) with
  | some d => if declFree d.body then some d else none
  | none => none

/-- `D` after performing statement `e`: one entry longer if `e` is a top-level `def`,
unchanged otherwise. -/
def extendDefs (D : DefTable) : Expr → DefTable
  | .def' n ps body => ⟨n, ps, body⟩ :: D
  | _ => D

/-- One **assumed** instantiation: "a call to `name` whose arguments synthesize `argTys`
returns `ret`". Keyed by the argument types, not just the name, because this checker types
a body once per call-site shape (see `Judge.callDef`) rather than inferring one signature
per method. -/
structure Asm where
  name : String
  argTys : List Ty
  ret : Ty

/-- The instantiations currently **assumed**, to break the cycle a recursive method
creates.

**Read a `Judge D Δ Γ e τ Γ'` with a non-empty `Δ` as a *conditional* claim** — "if every
assumption in `Δ` holds, then `e : τ`". Only `Δ = []` is an absolute one, and `validate`
starts there. `Judge.callAsm` on its own is therefore blatantly unsound (`Δ` could say
anything); what makes the whole judgment sound is that `Judge.callDef` is the *only* rule
that ever extends `Δ`, and it discharges what it adds. -/
abbrev AsmTable := List Asm

def asmGet? (Δ : AsmTable) (m : String) (τs : List Ty) : Option Ty :=
  (Δ.find? (fun a => a.name == m && a.argTys == τs)).map (·.ret)

/-! ### A class body's constants (tier 13)

`Ctx.consts` maps a constant's absolute path to its type, and it is grown by `extendConsts`,
which is a **function of syntax alone** — `Ctx.afterStmt` gets the statement's type, and that
is the type of the `class` statement (`.any`), not of anything inside its body.

So a class-body constant's type has to be readable off its initializer's syntax. That is
`constLitTy?`, and its restriction to literals is the price of this tier's second rung. The
restriction is not the soundness argument, though — `constLitTy?` is just a guess until
`Judge.classStmt`'s `JudgeConsts` premise **judges the initializer at exactly that type**, in
the context in force at the class statement. Two things follow:

- soundness of `constLitTy?` reduces to soundness of `Judge`, so this function may be widened
  freely: a wrong row costs a rung (the premise fails) and never a wrong type;
- and the judgment happens at the **definition site**. That matters more than it looks.
  Judging the initializer lazily, at each *read*, is unsound: `κ.classes` only grows, a
  reopened class can redefine a method, and `class Box; V = Helper.new.f; end` re-judged after
  `class Helper; def f; "s"; end; end` would type `V` as a `String` while it holds the
  `Integer` the original `f` returned.

Top-level constants need none of this: their type comes from the judgment directly, because
there `Ctx.afterStmt` is handed the statement's own type. -/
mutual

def constLitTy? : Expr → Option Ty
  | .int _ => some .int
  | .flt _ => some .float
  | .str _ => some (.cls "String")
  | .sym _ => some .sym
  | .tru => some .bool
  | .fls => some .bool
  | .nil => some .nilT
  -- A hash literal's type carries nothing about its pairs (tier 5), so this row could read
  -- `.hash _ => some (.cls "Hash")` and be right about the type. It checks the pairs anyway,
  -- because `constLitTy?_sound` — "an expression this function types really does have that
  -- type, in any context, unconditionally" — is what lets the same function be used for an
  -- **optional parameter's default** (tier 14a) with no premise anywhere to discharge, and
  -- that theorem needs the pairs to type.
  | .hash pairs =>
    match constLitPairTys? pairs with
    | some (kτ, vτ) => some (.hashOf kτ vτ)
    | none => none
  | .array es => (constLitTys? es).map (fun τs => .arrayOf (elemTy τs))
  -- `.freeze` is the idiom every frozen constant table in the slice is written with, and it is
  -- the identity on the value (`PrimSig.freezeId`), so it is the identity here.
  | .send (some r) "freeze" [] none => constLitTy? r
  | _ => none

def constLitTys? : List Expr → Option (List Ty)
  | [] => some []
  | e :: es => match constLitTy? e, constLitTys? es with
    | some τ, some τs => some (τ :: τs)
    | _, _ => none

/-- The joined key and value types of a **literal** hash, folded exactly as `JudgePairs`
folds them (tier 17b). Replaced `constLitPairs?`, which only asked whether the pairs typed --
now the types are the answer. -/
def constLitPairTys? : List (Expr × Expr) → Option (Ty × Ty)
  | [] => some (.never, .never)
  | (k, v) :: ps =>
    match constLitTy? k, constLitTy? v, constLitPairTys? ps with
    | some kτ, some vτ, some (kr, vr) => some (joinT kτ kr, joinT vτ vr)
    | _, _, _ => none

end

/-! ### The environment a method body starts in

**Only its parameters**, bound to what the call site supplied. Two decisions in one small
function:

- **A fresh environment, not the caller's.** A Ruby method body does not see the caller's
  locals, so the body is judged in `paramBind`'s result and the call's *outgoing* environment
  is the caller's own (after the arguments), never the body's.
- **Matching is greedy, left to right**, and the reason that is safe is worth stating: it
  either agrees with Ruby or fails. Ruby fills post-optional and post-rest *required*
  parameters first (`def f(a, b = 1, c)` with two arguments binds `a` and `c`), and greedy
  matching there binds `a` and `b`, then meets a `.req` with no argument left, and answers
  `none`. There is no argument count at which greedy succeeds with a binding Ruby would not
  have made. Length mismatch is also `none`, which is what rejects `fun-wrong-arity`.

### One walk, three entry points (tier 14c)

`paramEnv`, `paramEnvB` and the keyword-aware binder are the *same* left-to-right walk over a
parameter list, differing only in what is available to bind from. So there is one function,
`paramBind`, taking all three inputs — the block (out of band), the positional argument types,
and the keyword arguments as name/type pairs — and the two older names are abbreviations for it
at empty inputs. Every derivation on file still discharges its `paramEnv … = some Γb` premise by
`rfl`, because `paramBind`'s behaviour at `kws = []` on required parameters is unchanged.

One behaviour did change on the way, in the direction of being more right: `paramEnv` used to
refuse a `Param.block` outright (only `paramEnvB` accepted one), and now binds it to `.nilT`,
which is what Ruby does when a method with a `&b` parameter is called with no block. -/
def kwGet? (kws : List (String × Ty)) (k : String) : Option Ty :=
  (kws.find? (·.1 == k)).map (·.2)

/-- Drop the *matched* keyword, so that whatever is left at the end of the walk is the set of
keywords the method has no parameter for — which raises `ArgumentError`, inside the family. -/
def kwErase : List (String × Ty) → String → List (String × Ty)
  | [], _ => []
  | (k, τ) :: kws, x => if k == x then kwErase kws x else (k, τ) :: kwErase kws x

/-- **Is every remaining parameter one that cannot consume a positional argument?** The exact
condition under which a rest parameter may be greedy: `def f(*a, b)` fails it (Ruby binds
`b` first), while `def f(*a, c:, **kw, &blk)` passes, because keywords, a keyword-rest and a
block all come from somewhere other than the positional list.

Tier 14b stated this as "the rest parameter must be last", which was the same condition for the
parameter kinds that existed then. -/
def noPositionalParams (ps : List Param) : Bool :=
  ps.all (fun p => match p with
    | .key _ _ | .kwrest _ | .block _ => true
    | _ => false)

def paramBind (blk : Option Ty) : List Param → List Ty → List (String × Ty) → Option Env
  -- Every parameter bound and every argument consumed. **The `kws.isEmpty` check is a
  -- soundness condition**, not tidiness: a keyword the method has no parameter for raises
  -- `ArgumentError` (tier 14c).
  | [], [], kws => if kws.isEmpty then some [] else none
  | .req x :: ps, τ :: τs, kws => (paramBind blk ps τs kws).map (fun Γ => (x, τ) :: Γ)
  -- Tier 14a: an **optional** parameter. Two cases, and the matching is greedy left to right.
  -- An argument was supplied, so the default is irrelevant:
  | .opt x _ :: ps, τ :: τs, kws => (paramBind blk ps τs kws).map (fun Γ => (x, τ) :: Γ)
  -- Or it was not, and the parameter holds the default's value. Its type comes from
  -- `constLitTy?`, which needs no premise to license it: `constLitTy?_sound` says an
  -- expression this function types really has that type in *any* context, unconditionally.
  -- A non-literal default (`def pad(s, n = s.length)`) is `none` here — see §Frontier.
  | .opt x d :: ps, [], kws =>
    match constLitTy? d with
    | some τ => (paramBind blk ps [] kws).map (fun Γ => (x, τ) :: Γ)
    | none => none
  -- Tier 14b: a **rest** parameter. The element type is `elemTy` of the argument types it
  -- swallows, exactly as for an array literal, which makes the zero-argument case
  -- `arrayOf .never`: the array really is empty, and `.never` is the most precise thing to say
  -- about the elements of an empty array (see `elemTy`, and `IterSig.injectEmpty` for what
  -- consumes it). Greedy only when `noPositionalParams` holds.
  | .rest (some x) :: ps, τs, kws =>
    if noPositionalParams ps then
      (paramBind blk ps [] kws).map (fun Γ => (x, .arrayOf (elemTy τs)) :: Γ)
    else none
  | .rest none :: ps, _, kws =>
    if noPositionalParams ps then paramBind blk ps [] kws else none
  -- Tier 14c: a **keyword** parameter, matched **by name** and only once the positional list is
  -- exhausted, because a keyword parameter never consumes a positional argument. Three
  -- outcomes, and the third is the soundness one: supplied, defaulted, or **missing and
  -- required**, which raises `ArgumentError`.
  | .key k dflt :: ps, [], kws =>
    match kwGet? kws k with
    | some τ => (paramBind blk ps [] (kwErase kws k)).map (fun Γ => (k, τ) :: Γ)
    | none =>
      match dflt with
      | some d =>
        match constLitTy? d with
        | some τ => (paramBind blk ps [] kws).map (fun Γ => (k, τ) :: Γ)
        | none => none
      | none => none
  -- A keyword-rest collects everything left, and tier 17b gives it a *useful* type: the keys
  -- are symbols (the call site wrote `k: v`) and the value type is the join of what was
  -- passed, folded exactly as a hash literal's is.
  | .kwrest (some x) :: ps, [], kws =>
    (paramBind blk ps [] []).map
      (fun Γ => (x, .hashOf .sym (elemTy (kws.map (·.2)))) :: Γ)
  | .kwrest none :: ps, [], _ => paramBind blk ps [] []
  | .block (some x) :: ps, τs, kws =>
    (paramBind blk ps τs kws).map (fun Γ => (x, blk.getD .nilT) :: Γ)
  | .block none :: ps, τs, kws => paramBind blk ps τs kws
  | _, _, _ => none

def paramEnv (ps : List Param) (τs : List Ty) : Option Env := paramBind none ps τs []

/-- **Split a call's argument list into positional arguments and a trailing `kwargs`**
(tier 14c). `Expr.kwargs` only ever occurs as the last element of an argument list (see its
docstring), and it is *not a value* — so it cannot be typed by `JudgeAll` and every call shape
that admits keywords needs the split.

`none` when there is no trailing `kwargs`, which is the ordinary call and the arm already on
file. `splitKw?_sound` (`Proof/ChkSound.lean`) is the bridge to the rule, which states the
split as `args = pos ++ [.kwargs entries]` rather than as a call to this function. -/
def splitKw? : List Expr → Option (List Expr × List KwEntry)
  | [.kwargs es] => some ([], es)
  | e :: rest => (splitKw? rest).map (fun p => (e :: p.1, p.2))
  | [] => none

/-- The name a keyword-carrying call binds its parameters through; `paramEnv` is this at no
keywords, and the two are deliberately the same function so that a rule written for one shape
cannot disagree with the other about arity. -/
def paramEnvK (ps : List Param) (τs : List Ty) (kws : List (String × Ty)) : Option Env :=
  paramBind none ps τs kws

end Ratchet
