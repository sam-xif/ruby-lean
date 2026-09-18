import Ratchet.Static.Iterators

/-!
# `Ratchet/Static/Capture.lean`

A **closure's creation context** (tier 11) and the ivar/capture agreement guards:
`Ctx.inClosure`, `capIntact`, the `ivarAgree*` family, `ivarAsgnOk`, `bodyResult`,
`procRetOk`. What a body judged elsewhere is allowed to have changed.
-/

namespace Ratchet

/-! ### A closure's creation context (tier 11)

`Ty.clos`'s third field records the `self` of the closure's *creation* site. These two
functions decode it, and `Ctx.inClosure` is the context a body is judged in.

The point of the whole arrangement, stated once: **a closure body's `self` and instance
variables come from where the closure was made; its class/method tables come from where it is
called.** The first half is what these functions are for. The second half is deliberate and
correct: Ruby resolves a method call inside a block at *call* time, so a body that calls a
method defined after the block literal but before the invocation works, and carrying the call
site's tables is what models that. -/

/-- The `self` type a closure was created under, or `none` for one created where `self` was
not typed (top level), which `Ty.clos` encodes as `.never`. -/
def closSelf? (σ : Ty) : Option Ty := if σ == .never then none else some σ

/-- The ivar spine a closure's body must be judged against: the instance variables of the
object that was `self` when it was created.

`.ivar0` for anything that is not an `.inst`, which covers both the top-level case (`.never`)
and a closure created inside a singleton method (`.clsOf n`, whose `self` is a class object
with no ivars this checker models). Relies on an invariant every body-entering rule maintains:
where `κ.selfTy = some (.inst n I)`, the threaded spine *is* `I` (`Judge.callMethod`,
`Judge.selfCall`). -/
def closSpine (σ : Ty) : Ty :=
  match σ with
  | .inst _ ivars => ivars
  | _ => .ivar0

/-- The context a closure's body is judged in: the recorded `self`, and **no frame and no
block**.

Both erasures are conservative rather than principled, and each is recorded as such: a
`super` inside a closure body has no rule (`frame = none`), and a `yield` inside a closure
body has no rule (`blockTy = none`) even though Ruby resolves it to the enclosing method's
block. Making either precise means recording it in `Ty.clos` too, exactly as `selfTy` now is;
no rung asks. -/
def Ctx.inClosure (κ : Ctx) (σ : Ty) : Ctx :=
  { κ with scope := { κ.scope with selfTy := closSelf? σ, frame := none, blockTy := none } }

/-- The block-local list of a `|x; y|` block (the desugarer's third `block` field), bound at
`.nilT`.

`.nilT` and not "unbound" because that is what Ruby does: a block-local is *declared* by the
`; y`, and reading it before assigning yields `nil` — the same fact `ivarGet?`'s defaulting
records one state over. Every rung that has one assigns before reading, so the value is never
observed; binding it anyway is what makes the name in scope at all. -/
def blockLocals : List String → Env
  | [] => []
  | x :: xs => (x, .nilT) :: blockLocals xs

/-- **Every name a closure captured still has the type it had on entry to its body.**

The premise that stops a block from retyping a captured local out from under its caller —
`callMethod`'s no-retyping premise, for locals instead of instance variables. The two are the
same rule stated twice, and the general form is worth naming: *a callee may not retype state
its caller can still see.*

Why it is needed, concretely (this was a real bug, found by fuzzing a class-plus-block program
and fixed in clink 11):

```ruby
def t; yield(1); end
a = 1
t { |x| a = "s" }
a + 1                 # TypeError
```

A Ruby block captures locals **by reference**, but `Ty.clos` captures by *value* into a spine
and the call rules discard the body's outgoing environment. So without this premise the caller
still believes `a : Int` after the block ran, and `a + 1` certifies a program that raises.

`Γin` is the body's incoming environment (`paramEnv … ++ spineToEnv cap`), not the spine
itself, so a captured name **shadowed by a block parameter** is compared at the parameter's
slot. That is stricter than necessary — assigning to a shadowing parameter cannot affect the
outer variable — and rejects `a = 1; lambda { |a| a = 2 }.call(3)`. Conservative, no rung
shadows, and recorded here rather than fixed because the precise version needs the premise to
know which names `paramEnv` bound.

What it costs in general: a block that accumulates into an outer local at a *different* type
is rejected. A block that accumulates at the *same* type (`a = a + x`) is fine — the value
changes, the type does not — which is the common case and the same boundary
`class-setter-method` sits on for ivars. The precise alternative is to thread the body's
outgoing environment back out and join it with the caller's (a block may run zero times, so a
join is required, and for `each` it would need a fixpoint). Not built; no rung needs it. -/
def capIntact : Ty → Env → Env → Bool
  | .ivarCons x _ rest, Γin, Γout =>
    (envGet? Γout x == envGet? Γin x) && capIntact rest Γin Γout
  | _, _, _ => true

/-- **Does every spine in this type agree with `τ` about the instance variable `x`?** —
`found-issues.md` §F17's guard.

An `.inst n I` type carries a spine, and a spine entry for `x` is a claim about *some* object's
`@x`. An assignment to `self`'s `@x` invalidates such a claim when the object is `self` — which
the type cannot tell — so the check has to be conservative about *which* object and precise
about *what*: a spine that says nothing about `x` is untouched (the spine is a **lower bound**,
so an unmentioned ivar is unconstrained), and a spine that says `x : τ` is still right if the
value written is a `τ`. Only a spine that records a *different* type is refused.

Both halves matter for the corpus. Refusing every mention would reject every assignment inside
a method, because `κ.selfTy`'s own spine records the ivars; accepting every mention is
`corpus/240`, where `@a : Integer` is overwritten with a `String` while a local holds `self`.

Recursive through every constructor that can *contain* an `.inst` — `union`, `nilable`,
`arrayOf`, `hashOf`, `sameAs`, and the spines themselves. The arrow arms are exempt and a
`clos`'s two type components are not; see the note in `Judge.ivarAsgn`. -/
def ivarAgree (x : String) (τ : Ty) : Ty → Bool
  | .inst _ I => (match ivarGet? I x with | none => true | some ρ => ρ == τ) && ivarAgree x τ I
  | .union σ ν => ivarAgree x τ σ && ivarAgree x τ ν
  | .nilable ρ | .arrayOf ρ | .sameAs _ ρ => ivarAgree x τ ρ
  | .hashOf κ' ν => ivarAgree x τ κ' && ivarAgree x τ ν
  | .ivarCons n σ rest =>
    (n != x || σ == τ) && ivarAgree x τ σ && ivarAgree x τ rest
  -- **The arrow arms are fine, and the reason is `Later`.** An arrow's denotation is a claim
  -- about *future* runs, quantified over `Later`-futures of the machine, so it survives any
  -- change that relation admits — an ivar write included. A `clos` is not quantified: it reads
  -- the captured frame and creation `self` at *this* machine, so its two type components have
  -- to be checked.
  | .arrow0 _ | .arrowCons _ _ => true
  | .clos _ cap selfT => ivarAgree x τ cap && ivarAgree x τ selfT
  | _ => true

/-- The same over an environment, and over `κ.selfTy` — which records the running method's own
`self`, spine and all, and is therefore the *usual* place a mention appears. -/
def ivarAgreeEnv (x : String) (τ : Ty) (Γ : Env) : Bool :=
  Γ.all (fun p => ivarAgree x τ p.2)

def ivarAgreeSelf (x : String) (τ : Ty) : Option Ty → Bool
  | none => true
  | some σ => ivarAgree x τ σ

/-- **The incoming `self` spine, checked everywhere except at `@x` itself.**

The sixth place, and the one that is not context: `I'` is what the *judgment* has inferred
about `self`'s instance variables, and `SelfSpineOk` reads every entry of it through
`ivarOf … self`. An entry `@a : C[@x : Int]` describes an object that could *be* `self`
(`@a = self`), and then writing `@x` at a different type falsifies it.

The top-level `@x` entry is **exempt**, and it has to be: `ivarSet` replaces it with `τ`, so
its old type is not read after the write. Requiring agreement there instead of exempting it
would reject every type-changing reassignment — `if flag then @v = 1 else @v = "s"`, which is
the program that put `joinIvars` in `Ratchet/Lang/Ty.lean` in the first place. -/
def ivarAgreeIvars (x : String) (τ : Ty) : Ty → Bool
  | .ivarCons n σ rest => (n == x || ivarAgree x τ σ) && ivarAgreeIvars x τ rest
  | _ => true

/-- **Everything the context records that could hold a spine mentioning `@x`.** Five places,
and the list is not a guess: it is the `StateOk` components whose statement applies `denM` to a
type the *context* supplies — the environment, the right-hand side's own type, `self`'s type,
the block's type, and the constant table. The others read only the heap's shape, which an
instance-variable write leaves alone. -/
def ivarAsgnOk (κ : Ctx) (x : String) (τ : Ty) (Γ' : Env) (I' : Ty) : Bool :=
  ivarAgreeEnv x τ Γ' && ivarAgree x τ τ && ivarAgreeSelf x τ κ.selfTy &&
  ivarAgreeSelf x τ κ.blockTy && ivarAgreeEnv x τ κ.consts && ivarAgreeIvars x τ I'

/-- The expression whose type is a body's **result**.

For almost every body that is the body itself. The one case that differs is a body which is
exactly `return e`: calling it evaluates `e` and returns it, so the result type is `e`'s —
whereas `.ret` has no rule of its own and the body would otherwise be untypeable
(`lambda-explicit-return`).

**Why this is a function on the body rather than a `Judge` rule for `.ret`.** The obvious rule
— `.ret e` synthesizes `e`'s type — is *unsound*: it makes `def f; return "a"; 2; end`
validate at `Int`, because `JudgeSeq` takes the last statement's type and the `return` never
lets the last statement run. Typing `.ret e` as `.never` does not help for the same reason.
Matching the body's *whole shape* sidesteps it: a `return` anywhere other than as the entire
body still has no rule, so `seq [return "a", 2]` remains underivable. The general fix — a
judgment that accumulates return types across a body — is a real design and no rung needs
it. Applied only at `closCall`, because only a lambda rung asks; a *method* whose body is
exactly `return e` is still not typed. -/
def bodyResult : Expr → Expr
  | .ret (some e) => e
  | e => e

/-- **A `return` is local to a lambda and not to a proc**, which is what `bodyResult` above
did not distinguish (`found-issues.md` §F19).

`lambda { return e }.call` evaluates `e` and hands it back to the caller — so rewriting the
body to `e` is exactly right, and `lambda-explicit-return` (rung 105) is that rung.
`proc { return e }.call` does something else entirely: the `return` returns from the
**enclosing method**, so the call never comes back at all and the *method's* value becomes
`e`'s. Typing the call as `e`'s type is then wrong twice over — the call has no type, and the
method's recorded return type is a lie.

`Judge.lambdaLit` is the only rule that turns a block literal into a callable `Ty.clos`, and it
admits `lambda` and `proc` alike, so this is the one place the distinction can be drawn without
adding a field to `Clos`. It is drawn as a **refusal**: a `proc` whose body is exactly
`return e` gets no type, so `closCall` never sees one and `bodyResult` stays sound where it is
still used.

Note the guard has to match `bodyResult`'s pattern and not merely mention `.ret`: a `return`
anywhere *other* than as the whole body has no rule of its own, so those bodies were already
untypeable and this refuses nothing new. -/
def procRetOk (m : String) (body : Expr) : Bool :=
  match body with
  | .ret (some _) => m == "lambda"
  | _ => true

end Ratchet
