import Denote.Sem.Core.Transport

/-!
# `Denote/Sem/Core/Frame.lean` — `StateOk` describes the whole world, and nothing more

Three rungs stalled this ladder for one reason wearing three costumes, and the reason is that
`StateOk` was only ever a **lower bound**. Every component says "each thing `κ` records is
really there"; none says "and there is nothing else". So a rule whose truth depends on the
*absence* of something — `Judge.bareName` ("`x` is not a method"), `Judge.lambdaLit` ("the
program did not `def lambda`") — had a hypothesis that could not reach its conclusion, and a
rule that redefines something had components that were unsatisfiable rather than false
(`Denote/Sem/notes.md`, sixth and ninth stall points).

The fix is a **frame lemma**, and this file is where it is stated. "`StateOk` describes the
whole state of the world, and nothing more" is two claims, and separating them is the point:

## 1. The frame rule for conformance — *already proved, and named here*

Conformance reads the heap, the frames and the frame stack; it does **not** read `ctl` or
`kont`. Everything it does not read is *frame*, and a change confined to the frame cannot
disturb it. That is `StateOk_reCtl` (`Denote/Rules/Core.lean`), which since clink 45 is a
corollary of `StateOk_ext` — so the state-side frame rule exists and has one proof.
`frameOnly` below gives it its name, so the two halves can be talked about separately.

Worth recording why `ctl`/`kont` are the *only* frame: the arrow arms of `denM` and `AsmsOk`
quantify over **runs**, and a run reads `globals`, `out` and `preludeMode` as well as the
heap. They survive a `ctl`/`kont` change for a sharper reason than "they don't look" —
`applyIn`/`sendIn` *overwrite* both on the way in, so the run a call denotes is literally the
same run from both machines (`denM_ctl`).

## 2. "And nothing more" — the exactness half, which is new

`MethodsExact` is the general form: **every method the machine can dispatch is either the
model's own or one `κ` records** — with `NameFreeOk` as its sharpening where a rule needs
absence rather than non-authorship, and `SelfLive` as the reference-integrity fact both need. Not a fixed list of names, not a claim about one rule —
one universally quantified statement about the heap, with the model's own two discriminators
(`MethodDef.builtin`, the axiomatized builtins; `MethodDef.fromPrelude`, Ruby's core library
written in RubyCore) doing the work of saying which methods are not the user's program.

Measured before it was stated: at the real prelude-booted heap the number of installed methods
that are neither builtin nor prelude is **zero** (`Denote/Sem/Core/Boot.lean`'s `methodsExactB`). So
this is not a hopeful invariant — it is a fact about the machine the ladder starts from, and
`κ.declaresName` is exactly the room a program needs to grow into it.

**What it does and does not buy**, stated up front because two of the three stalls it was
written for are *not* fixed by it:

* **Fixed:** the ninth stall point, at the conformance level. A negative table premise now
  has an upper bound to consume. It took **two** components, not one, and the second is the
  interesting one: `MethodsExact` allows a *prelude* method, while `Judge.bareName` needs `x`
  to resolve to **nothing** — "not the user's" is not "not there". So `NameFreeOk` sharpens
  exactness (`builtin.isSome ∨ undefined` in place of the prelude escape) on the fixed list of
  names the rules reason from, and localises it to the receiver's own ancestor chain.

  Chain-local rather than heap-global because the heap-global form is **false**, which is a
  finding rather than a technicality: the prelude *does* define a method named `proc` —
  `T.proc`, the sorbet shim's type constructor, a **singleton** method on the `T` module. It
  sits on `#<Class:T>`, off every ordinary receiver's chain, so `finishSend`'s shadowing test
  (which walks `methodOn (classOf recv)`) is right about it and the component has to be stated
  at the same walk in order to say so.
* **Also forced, and it is a real gap it closes:** `SelfLive`. `NameFreeOk`'s claim is about
  the chain at `self`, `classOf` reads `Heap.get`, and `Heap.get` is *total* — so at a machine
  whose `self` is a dangling reference an allocation changes what `self` is an instance of, and
  the claim does not survive the push. Nothing in `StateOk` had ever said `self` is a real
  object.
* **Fixed:** the sixth stall point's item (1), the vacuity risk. Under exactness a stale
  declaration table makes `StateOk` **false** at the post-machine rather than unsatisfiable at
  the pre-machine, which is the honest failure and the one `Denote/Sem/Core/Boot.lean` can see.
* **Not fixed:** the sixth stall point's item (2). `Judge.defStmt` concludes at the *incoming*
  `κ`, and no component can make that true — the fix is `κ` threaded through `Judge`'s
  signature.
* **Not fixed:** the fifth stall point. That is the *other* frame rule — locality in the
  continuation tail (§3) — and it is a theorem about `stepFn`, not about `StateOk`.

## 3. The interpreter's frame rule — stated, not proved, and **refuted** *(clink 52)*

The continuation tail is frame too, and by exactly the same argument: `StateOk` does not
describe it, so a run must not depend on it. `KontFrame` states that, and it was the **single
named target** the ~40 rungs behind the fifth stall point were to consume.

**It is false, and `not_KontFrame` is the counterexample** (clink 52, §3 below). `stepFn` is
head-local in `kont` at every *writer* — thirteen sites, all pushes, which is what the
measurement checked — and there is exactly one **reader**: `throw` scans the whole
continuation for a matching `catch` tag. Both statements need `CatchFree K` as a hypothesis,
and both get it for free at every use site the ladder has, since the konts a *rule* pushes are
literals. `KontFrameCatchFree` is the corrected target; the decomposition needs the same
hypothesis and needs it for a sharper reason (a sub-run can return under the empty
continuation and *not* under `K` — see the Ruby program in §3).

That this went unnoticed for a clink is the argument for writing the target down as a `def` in
the first place: it was `Prop`-shaped and named, so it could be attacked. Nothing in this
package takes either version as a hypothesis and no rung is counted on them.

Its cost is measured in `Denote/Sem/notes.md` §The fifth stall point: a dependency chain of
one-line lemmas over ~100 machine-taking functions in `RubyCore/Interp/` and
`RubyCore/Builtins/`, blocked at one `partial def` (`destructureBind`). It belongs in
`RubyCore/Proof/`, next to `stepFn`.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## 1. The frame, named -/

/-- **The frame**: `m₂` is `m` with a change confined to what `StateOk` does not describe.
`ctl` and `kont` are the whole of it — see the module docstring for why the run-quantifying
components survive that and nothing coarser. -/
def frameOnly (m m₂ : Machine) : Prop :=
  ∃ c k, m₂ = reCtl m c k

theorem frameOnly_reCtl (m : Machine) (c : Ctl) (k : List Kont) :
    frameOnly m (reCtl m c k) := ⟨c, k, rfl⟩

/-- **The frame rule for conformance.** A change confined to the frame cannot disturb the
description. Stated generally; the proof is `StateOk_ext`'s, through the degenerate `Ext` that
`reCtl` is. -/
theorem StateOk_frame {κ : Ctx} {Γ : Env} {I : Ty} {m m₂ : Machine}
    (h : StateOk κ Γ I m) (hf : frameOnly m m₂) : StateOk κ Γ I m₂ := by
  obtain ⟨c, k, rfl⟩ := hf
  exact StateOk_reCtl h c k

/-! ## 2. "And nothing more" -/

/-- The form a rule actually consumes: what `lookup` finds is subject to exactness. One
induction over the ancestor walk. -/
theorem MethodsExact.lookup {κ : Ctx} {m : Machine} (h : MethodsExact κ m)
    {v : Value} {n : String} {o : ObjId} {md : MethodDef}
    (hl : lookup m.heap v n = some (o, md)) :
    md.fromPrelude = true ∨ md.builtin.isSome = true ∨ nameFreeN κ n = false := by
  have go : ∀ (ks : List ObjId), lookup.go m.heap n ks = some (o, md) →
      md.fromPrelude = true ∨ md.builtin.isSome = true ∨ nameFreeN κ n = false := by
    intro ks
    induction ks with
    | nil => intro hg; exact absurd hg (by simp [lookup.go])
    | cons k rest ih =>
      intro hg
      rw [lookup.go] at hg
      split at hg
      · rename_i cp hp
        split at hg
        · rename_i nm md' hf
          have hmem : (nm, md') ∈ cp.methods := List.mem_of_find?_eq_some hf
          have hname : nm = n := by simpa using List.find?_some hf
          have hmd : md' = md := by
            have := Option.some.inj hg
            simpa using congrArg Prod.snd this
          subst hname; subst hmd
          exact h k cp hp nm md' hmem
        · exact ih hg
      · exact ih hg
  exact go _ hl

/-! ## 3. The interpreter's frame rule — the ladder's named target -/

/-- The continuation tail, appended. -/
def pushK (K : List Kont) (m : Machine) : Machine := { m with kont := m.kont ++ K }

/-- A step result, with the tail carried through. -/
def frameR (K : List Kont) : StepResult → StepResult
  | .next m => .next (pushK K m)
  | r => r

/-- **The interpreter's frame rule.** `stepFn` does not read below the head of `kont`, so a
step from a machine with more continuation behind it is the same step with more continuation
behind it.

The side condition is the two *pass-through* points, and they are the content rather than
fine print: `applyKont` at `kont = []` answers `.done` (it is the run's own result that a
longer stack would instead deliver) and `unwind` at `kont = []` escapes. Both are exactly the
states at which a sub-run *ends*, which is why the decomposition the compound rungs need holds
for precisely the runs `SemJudge` quantifies over.

**Stated, not proved, and nothing here assumes it.** No rung is counted on it and no
definition takes it as a hypothesis; it is written down so the ~40 rules behind the fifth
stall point have one target instead of forty arguments. Its measured cost and the one
`partial def` that currently blocks it are in `Denote/Sem/notes.md`. It belongs in
`RubyCore/Proof/` — a second copy of a proof about the same `stepFn` is a second thing to
drift (`Semantics/Interp.lean`). -/
def KontFrame : Prop :=
  ∀ (m : Machine) (K : List Kont),
    (m.kont ≠ [] ∨ ∃ e, m.ctl = .eval e) →
    Interp.stepFn (pushK K m) = frameR K (Interp.stepFn m)

/-! ### … and it is **false as stated** *(clink 52)*

`stepFn` is head-local in `kont` at every *writer* — thirteen sites, all `k :: m.kont`, which
is what `Denote/Sem/notes.md` §The fifth stall point checked. There is one **reader** it
missed, and one is enough: `throw` asks whether *any* frame of the continuation carries a
matching `catch` tag (`RubyCore/Interp/Reflect.lean`, `m.kont.any fun k => match k with |
.catchK t => t.identEq tag | _ => false`). So a `throw` with no matching `catchK` in `m.kont`
raises `UncaughtThrowError` *at the throw site* — deliberately, so an enclosing `rescue` sees
it — while the same state under a longer continuation jumps. The counterexample below is that,
at the smallest machine that reaches the dispatch.

**The repair, and it is a hypothesis rather than a redefinition.** Both statements want
`CatchFree K`: the appended tail carries no `catchK`. That is available at every use site the
ladder has — the konts a *rule* pushes are literals (`asgnK`, `argsK`, `seqK`, `arrK`, …), and
a `catch` inside the sub-expression pushes its `catchK` **above** `K`, where both sides see it
alike. So the corrected target is `KontFrameCatchFree` below, and it is the one the compound
rungs should be written against.

**`EvalsDecompose` is false for the same reason, and this is the sharper half**: it is *not*
rescued by "the sub-run must return", because a sub-run can return under the empty continuation
and not under `K`. In Ruby:

```ruby
catch(:t) do
  x = begin
        throw :t
      rescue UncaughtThrowError
        1
      end
  x + 1
end
```

Under the empty continuation the `begin` block **returns 1** (the throw raises at the site and
its own `rescue` catches it); under the enclosing `catch` the same `throw` is a jump that
leaves the `begin` entirely. So the run under `K` does not pass through the state delivering
the sub-run's value to `K`, which is exactly what the decomposition claims. Same repair. -/

/-- The appended continuation tail carries no `catch` marker — the hypothesis both statements
above are missing. Decidable, and true by inspection at every kont a `Judge` rule pushes. -/
def CatchFree (K : List Kont) : Prop :=
  ∀ k ∈ K, ∀ t : Value, k ≠ .catchK t

/-- **The corrected interpreter frame rule**: `KontFrame` plus `CatchFree`.

**Now proved, and elsewhere.** `RubyCore.Proof.stepFn_frame` is this statement, in
`RubyCore/Proof/KontFrameStep.lean` — which is where the paragraph above said it belonged,
next to `stepFn` rather than in a second copy here. `Denote/Sem/Core/Decompose.lean` consumes it
and `RubyCore.Proof.done_inv` to prove the run-level decomposition `EvalsDecompose` was
stating. This `def` is kept as the *statement of record*: it is what the wall was, it carries
the refutation below, and the proof's own side condition is the one it predicted.

One correction to the prediction: the side condition is needed for the **`jump`** arm and not
for `.value` — `unwind`'s `retJ` case at an empty continuation *steps* (to
`raiseErr … "unexpected return"`) rather than escaping, so "the run cannot end in `.value`" is
not what rules it out; being an empty continuation is. -/
def KontFrameCatchFree : Prop :=
  ∀ (m : Machine) (K : List Kont), CatchFree K →
    (m.kont ≠ [] ∨ ∃ e, m.ctl = .eval e) →
    Interp.stepFn (pushK K m) = frameR K (Interp.stepFn m)

/-! ### The counterexample, computed

The smallest machine that reaches the `throw` dispatch: a value in flight, one `argsK`
delivering it to an implicit-self `throw`, and an **empty heap** (so `lookup` misses and
`dispatchMiss` reaches `tryReflect`). Under the empty tail the step raises; under one
`catchK` with the matching tag it jumps.

Conditional on two `Bool`s rather than `decide`d, for the reason `Denote/Sem/Core/Boot.lean`'s
`bootOkB` is: `Interp.invoke` is compiled by well-founded recursion, so it is not
`rfl`-reducible, and `native_decide` would cost an axiom this package does not spend. The
`#guard`s below are the build gate. -/
def throwM : Machine :=
  { ctl := .value (.sym "t"),
    kont := [.argsK .nil .implicit "throw" [] [] .none],
    stack := [], frames := #[], heap := ⟨#[]⟩ }

def catchTail : List Kont := [.catchK (.sym "t")]

/-- Which kind of outcome a step produced — enough to separate the two. -/
def tagOf : StepResult → String
  | .next m => match m.ctl with
    | .jump (.raiseJ _) => "raise"
    | .jump (.throwJ _ _) => "throw"
    | _ => "other"
  | .unsupported r => "unsupported: " ++ r
  | .stuck r => "stuck: " ++ r
  | .done _ _ => "done"
  | .uncaught _ _ => "uncaught"

/-- `frameR` rewrites `kont` and nothing else, so it cannot change the outcome's kind. -/
theorem tagOf_frameR (K : List Kont) (r : StepResult) : tagOf (frameR K r) = tagOf r := by
  cases r <;> rfl

/-- **`KontFrame` is refutable.** -/
theorem not_KontFrame
    (hbare : tagOf (Interp.stepFn throwM) = "raise")
    (hunder : tagOf (Interp.stepFn (pushK catchTail throwM)) = "throw") : ¬ KontFrame := by
  intro h
  have heq := h throwM catchTail (Or.inl (by simp [throwM]))
  rw [heq, tagOf_frameR, hbare] at hunder
  exact absurd hunder (by decide)

-- **The gate.** The two computations the refutation is conditional on.
#guard tagOf (Interp.stepFn throwM) == "raise"
#guard tagOf (Interp.stepFn (pushK catchTail throwM)) == "throw"

/-- **What the rungs will actually use**: the decomposition. A run of `e` under continuation
`K` passes through the state that delivers `e`'s value to `K` — so a compound rule's premise,
which is about the run of `e` under the *empty* continuation, is about a prefix of the run its
conclusion is about.

Stated as a consequence of `KontFrame` rather than independently, because that is what it is:
`stepFn` is a function, so the equation runs backwards for free — `frameR K r = .next m₂`
forces `r = .next m'` with `m₂ = pushK K m'`. What it is *not* is unconditional in `K`: a `K`
whose head is a handler (`beginBodyK`) can turn a sub-run that escaped into an outer run that
returns, so the hypothesis is about runs that return a value, which is the only shape
`SemJudge` imposes anything on.

**Now proved, as `Decompose.lean`'s `run_split`**, and that second paragraph is exactly its
third hypothesis: `JumpOpaque K`, "`K` cannot turn an escaping jump into a returned value".
The proof needs one thing this statement does not mention — `RubyCore.Proof.done_inv`, the
fact that `.done` is constructed at one site in the interpreter — because "the inner run
stopped here" has to be turned into "and *here* is a value under an empty continuation" before
the outer run can be continued from it. -/
def EvalsDecompose : Prop :=
  ∀ (m : Machine) (e : Ratchet.Expr) (K : List Kont) (v : Value) (m' : Machine),
    (∃ fuel, Interp.run fuel (pushK K (evalFrom m e)) = .value v m') →
    ∀ (w : Value) (m₁ : Machine), Evals m e w m₁ →
      ∃ fuel, Interp.run fuel (pushK K (reCtl m₁ (.value w) [])) = .value v m'

#print axioms StateOk_frame
#print axioms MethodsExact.lookup
#print axioms not_KontFrame

end Ratchet.Denote
