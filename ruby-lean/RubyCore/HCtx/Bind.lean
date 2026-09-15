/-
  RubyCore.HCtx.Bind — can we have iris-lean's `wp_bind` for the RubyCore machine?

  **Diagnosis and prior art**: `../../docs/semantics/answer-typed-judgments.md`
  (§2.4–§2.5 cite this file; §3 is why the answer is structural).

  **The question.** `Denote/Sem/Decompose.lean`'s `run_split` and
  `Denote/Rules/VasgnStuck.lean`'s `stuckFreeRun_pushK_le` are two
  hand-rolled decompositions of "a run under an appended continuation", one per
  axis, each ~90 lines, each needing per-continuation side conditions
  (`CatchFree`, `JumpOpaque`, `JumpStuckFree`). Iris has the general form,
  proved once:

      wp_bind (K : Expr → Expr) [Language.Context K] :
        wp e {v. wp (K (ofVal v)) Φ} ⊢ wp (K e) Φ

  and `Language.Context K` asks for only three laws. J36 already seated the
  machine as an iris-lean `Language` (`RubyCore/HJudge/Lang.lean`). So: is the
  bind rule one instance away?

  **Answer: no, and the obstruction is exact rather than an effort estimate.**
  Two findings, both mechanised below.

  1. **J36's instance cannot bind at all**, for a structural reason: its `Val`
     is `ROutcome`, a *whole-program* answer carrying only `(value, heap)`.
     `wp_bind` needs `K (ofVal v)` to be the computation resumed with `v`, and
     a whole-program outcome has no frames to resume into. A binding instance
     needs `Val` = "an answer in flight, plus the ambient control state", which
     is what `HCtx.CVal` below is. That instance is built here and is fine.

  2. **`Language.Context (fillK Ks)` is FALSE for the binding instance**, and
     `ctx_law3_fails` is the counterexample. Law 3 (`primStep_fill_inv`) says a
     step of `K e` is a step of `e` under `K`. At a control configuration whose
     `ctl` is an escaping jump and whose `kont` is empty, that is simply untrue:
     `e` unwinds at `[]` and escapes, `K e` unwinds *into `Ks`* and does
     something else entirely.

     The obvious repair — make an escaping jump a *value* of the sub-language,
     which is the effect-handler reading (a sub-computation answers with a value
     **or** an effect) — is blocked by `Language.val_stuck`: values may not step,
     and two of Ruby's seven jumps *do* step at an empty continuation
     (`retJ` and an uncaught `throwJ` both reach `raiseErr`, which is why
     `ratchet`'s `jump_empty_never_value` is an induction and not a computation).
     So the jump family splits into five that could be values and two that
     cannot, and no choice of `toVal` satisfies both laws at once.

  **What that means.** `CatchFree`/`JumpOpaque`/`JumpStuckFree` were not
  incidental bookkeeping — they are the side conditions that carve out the
  sub-language on which the bind rule *would* hold, and Iris's `Context` class
  has no room to state them (it is a global instance on `K`, with no hypothesis
  about `e`). The literature's answer for exactly this is a WP indexed by a
  **protocol** for what the surrounding handler may do with an escape — de
  Vilhena & Pottier's Hazel logic for effect handlers — not `Language.Context`.

  So the recommendation this file supports: do not spend the Iris seat on
  `wp_bind`. Either keep the hand-rolled decomposition and give it a
  *context-carrying* continuation predicate (which also repairs the false
  `JumpStuckFree`, see `Denote/Rules/WhileStuck2.lean`), or budget for a
  protocol-indexed WP. Both are larger than "one instance".

  House rules, inherited from `HJudge/`: no sorry, no new axioms.
-/
import Iris.ProgramLogic.Language
import RubyCore.Interp
import RubyCore.Proof.KontFrameStep

set_option autoImplicit false

namespace RubyCore.HCtx

open RubyCore
open Iris.ProgramLogic

/-! ## The binding instance

`Expr` is the control configuration (`HJudge.MCfg`'s shape, redefined here so
the two instances cannot form a diamond); `Val` is an answer *in flight* at an
empty continuation, carried with the ambient state so `ofVal` can resume. -/

/-- Everything in a control configuration except `ctl` and `kont` — the part a
value carries so that resuming it is possible. -/
structure MRest where
  stack : List FrameId
  frames : Array Frame
  globals : List (String × Value) := []
  out : String := ""
  currentExc : Option Value := none
  preludeMode : Bool := false
deriving Inhabited

/-- A control configuration. -/
structure Cfg where
  ctl : Ctl
  kont : List Kont := []
  rest : MRest
deriving Inhabited

def Cfg.load (c : Cfg) (h : Heap) : Machine :=
  { ctl := c.ctl, kont := c.kont, stack := c.rest.stack, frames := c.rest.frames,
    heap := h, globals := c.rest.globals, out := c.rest.out,
    currentExc := c.rest.currentExc, preludeMode := c.rest.preludeMode }

def _root_.RubyCore.Machine.hcfg (m : Machine) : Cfg :=
  { ctl := m.ctl, kont := m.kont,
    rest := { stack := m.stack, frames := m.frames, globals := m.globals,
              out := m.out, currentExc := m.currentExc,
              preludeMode := m.preludeMode } }

@[simp] theorem load_hcfg (m : Machine) : m.hcfg.load m.heap = m := rfl
@[simp] theorem hcfg_load (c : Cfg) (h : Heap) : (c.load h).hcfg = c := rfl

/-- **The language's values**: a returned value at an empty continuation, plus
the state it leaves behind. Deliberately *not* including escaping jumps — see
the module header, finding 2. -/
structure CVal where
  v : Value
  rest : MRest
deriving Inhabited

def CVal.toCfg (w : CVal) : Cfg := { ctl := .value w.v, kont := [], rest := w.rest }

def cfgToVal : Cfg → Option CVal
  | { ctl := .value v, kont := [], rest := r } => some ⟨v, r⟩
  | _ => none

/-- One `stepFn`, no observations, no forks. `.done`/`.uncaught`/`.unsupported`/
`.stuck` have no step: they are terminal, which is what makes `val_stuck` hold. -/
inductive CStep : Cfg × Heap → List Empty → Cfg × Heap × List Cfg → Prop where
  | next {c : Cfg} {h : Heap} {m' : Machine} :
      Interp.stepFn (c.load h) = .next m' →
      CStep (c, h) [] (m'.hcfg, m'.heap, [])

/-- **The binding `Language` instance**, all fields at once — `HJudge/Lang.lean`'s
"cerberus no-diamond discipline", which turns out to be forced: `Language`
*extends* `PrimStep` and `ToVal`, so separate parent instances are not found.

`val_stuck` is where the design pays off: a value at an empty continuation has
`stepFn = .done`, and `CStep` has no constructor for that. -/
instance instLanguageCfg : Language Cfg Heap Empty CVal where
  toVal := cfgToVal
  ofVal := CVal.toCfg
  coe_of_toVal_eq_some {e w} h := by
    rcases e with ⟨ctl, kont, r⟩
    cases ctl <;> cases kont <;> simp_all [cfgToVal, CVal.toCfg]
    subst h
    exact ⟨rfl, rfl⟩
  toVal_coe w := by cases w; rfl
  primStep := CStep
  val_stuck {e σ obs e' σ' eₜ} h := by
    cases h with
    | next hf =>
      rcases e with ⟨ctl, kont, r⟩
      cases ctl <;> cases kont <;>
        first
          | rfl
          | (exfalso
             simp [Cfg.load, Interp.stepFn, Interp.applyKont] at hf)

/-! ## The context former, and the laws -/

/-- Any jump at an empty continuation — the shape both obstructions live at. -/
def jumpCfg (j : Jump) (r : MRest) : Cfg := { ctl := .jump j, kont := [], rest := r }

/-- Appending a continuation — the `K` of `wp_bind`, and exactly `ratchet`'s
`pushK`. On a value it is the delivery state (`ratchet`'s `deliver`). -/
def fillK (Ks : List Kont) (c : Cfg) : Cfg := { c with kont := c.kont ++ Ks }

/-- **Law 1** — filling a non-value leaves a non-value. Holds for every `Ks`:
appending to the continuation cannot make it empty unless it already was, and
then `Ks` must be empty too. -/
theorem toVal_eq_none_fillK {Ks : List Kont} {c : Cfg}
    (h : cfgToVal c = none) : cfgToVal (fillK Ks c) = none := by
  rcases c with ⟨ctl, kont, r⟩
  cases ctl <;> cases kont <;> cases Ks <;> simp_all [cfgToVal, fillK]

/-- Filling and loading commute — the bridge to `RubyCore/Proof/`'s `pushK`. -/
theorem fillK_load (Ks : List Kont) (c : Cfg) (h : Heap) :
    (fillK Ks c).load h = RubyCore.Proof.pushK Ks (c.load h) := rfl

/-- **Law 2 holds — but only with two hypotheses Iris's `Context` cannot state.**

`RubyCore.Proof.stepFn_frame` is proved over the whole of `stepFn` and is exactly
this law, except that it needs `CatchFree Ks` (a condition on the *context*,
which `Context` could in principle carry by being instantiated only at such
`Ks`) **and** `hside` (a condition on the *expression* — that it is not a value
or jump at an empty continuation, which is precisely the configuration law 3
dies on).

`Language.Context K` quantifies over all `e` with no hypothesis available, so
the second one has nowhere to live. This is the same obstruction as
`ctx_law3_fails`, seen from the other side: the law is true on the sub-language
the side conditions carve out, and the class cannot name that sub-language. -/
theorem law2_of_stepFn_frame {Ks : List Kont} (hK : RubyCore.Proof.CatchFree Ks)
    {c : Cfg} {h : Heap} {m' : Machine}
    (hside : c.kont ≠ [] ∨ ∃ e, c.ctl = .eval e)
    (hf : Interp.stepFn (c.load h) = .next m') :
    Interp.stepFn ((fillK Ks c).load h)
      = .next ((fillK Ks m'.hcfg).load m'.heap) :=
  RubyCore.Proof.stepFn_frame Ks hK (c.load h) m' hside hf

/-! ### Why "make a jump a value" does not rescue it

The natural repair for `ctx_law3_fails` is to let an escaping jump be a *value*
of the sub-language — the effect-handler reading, where a sub-computation
answers with a value **or** an effect. `Language.val_stuck` forbids it: values
may not step, and two of the seven jumps step at an empty continuation. -/

/-- A `retJ` at an empty continuation **steps** (to `raiseErr`'s freshly
allocated `LocalJumpError`), so it cannot be a value of any `Language`
instance over this machine. `ratchet`'s `jump_empty_never_value` needs an
induction for exactly this reason. -/
theorem retJ_steps_at_empty (v : Value) (t : FrameId) (r : MRest) (h : Heap) :
    ∃ m', Interp.stepFn ((jumpCfg (.retJ v t) r).load h) = .next m' :=
  ⟨_, rfl⟩

/-! ## Law 3 fails, and here is the configuration that breaks it

`primStep_fill_inv` reads

    toVal e = none → (K e, σ) → (K_e', σ', eₜ) → ∃ e', K_e' = K e' ∧ (e, σ) → (e', σ', eₜ)

Take `e` = a `retJ` at an empty continuation, `Ks = [asgnK .lvar x]`.

* `toVal e = none` — a jump is not a value of this language.
* `fillK Ks e` steps: `unwind` finds `asgnK`, whose default arm pops the frame
  and passes the jump on, reaching `{ctl := jump j, kont := []}` — which is `e`
  itself.
* `e` steps too, but somewhere else entirely: `unwind []` on a `retJ` reaches
  `raiseErr` (a freshly allocated `LocalJumpError`).

So the successor of `K e` is `e`, and the law demands it be `K e'` for some `e'`
that `e` steps to. `K e' = { e' with kont := e'.kont ++ Ks }` has `kont = []`
only when `Ks = []`. With `Ks` non-empty there is no such `e'`, and the law
fails — for every non-empty continuation, which is every interesting one.

The statement below is the arithmetic half of that argument, which is the part
worth machine-checking: **no filled configuration has an empty continuation**.
Everything else in the paragraph is `unwind`'s definition read off the source
(`Interp/Kont.lean`, the `_ => .next (withCtl m (.jump j))` arm). -/
theorem fillK_kont_ne_nil {Ks : List Kont} (hne : Ks ≠ []) (c : Cfg) :
    (fillK Ks c).kont ≠ [] := by
  simp only [fillK]
  intro h
  exact hne (List.eq_nil_of_append_eq_nil h).2

/-- …and therefore a configuration whose continuation *is* empty is not in the
image of `fillK Ks` for any non-empty `Ks`. This is the obstruction, stated
without reference to which jump it was: law 3 must produce `K e'`, and the
successor it has to match has an empty continuation. -/
theorem not_in_image_of_fillK {Ks : List Kont} (hne : Ks ≠ []) (c : Cfg)
    (hc : c.kont = []) : ¬ ∃ e', fillK Ks e' = c := by
  rintro ⟨e', rfl⟩
  exact fillK_kont_ne_nil hne e' hc

/-! ### The counterexample itself -/

/-- **The step that breaks the law**, and it is a `rfl`: with `[asgnK]` appended,
`unwind`'s default arm pops the frame and hands the jump straight back — so the
successor of `K e` is `e` itself, a configuration with an *empty* continuation.
(This is `ratchet`'s `jumpOpaque_asgnK` read for a different purpose.) -/
theorem step_fill_jump (x : String) (j : Jump) (r : MRest) (h : Heap) :
    Interp.stepFn ((fillK [.asgnK .lvar x] (jumpCfg j r)).load h)
      = .next ((jumpCfg j r).load h) := rfl

/-- **Law 3 is false**, for every `asgnK` context — the simplest continuation in
the language, the one `Judge.vasgn` pushes, and the one whose hand-rolled
decomposition already works.

The law would have to produce an `e'` with `K e' = e`, and `e` has an empty
continuation while every `K e'` has a non-empty one. So `wp_bind` is not
available for this language: not "hard to instantiate", **unavailable**. -/
theorem ctx_law3_fails (x : String) (h : Heap) :
    ¬ Language.Context (Expr := Cfg) (State := Heap) (Obs := Empty) (Val := CVal)
        (fillK [.asgnK .lvar x]) := by
  intro hC
  obtain ⟨e', heq, -⟩ :=
    hC.primStep_fill_inv (e := jumpCfg (.brkJ .nil) default) (σ := h)
      rfl (CStep.next (step_fill_jump x (.brkJ .nil) default h))
  exact not_in_image_of_fillK (by simp) _ rfl ⟨e', heq.symm⟩


/-! ### Correction: the `asgnK` witness is unreachable, the `seqK` one is not

**The objection.** `ctx_law3_fails` above is witnessed by a jump in flight under
an `asgnK`. Ruby's grammar forbids that outright — a jump is a *void value
expression* and cannot be the right-hand side of an assignment [V]:

```
$ ruby -e 'x = (break)'
> 1 | x = (break)
    |      ^~~~~ Invalid break
```

and the same for `next`, `redo`, `retry`, `return`. Bare `break`/`next`/`redo`/
`retry` at toplevel are syntax errors too — the model says so itself, in
`unwind`'s empty-continuation arm: *"jump escaped the program (break/next/retry
at toplevel)"*. So the theorem is true but its witness is a configuration no
CRuby-parseable program produces, and as a claim *about Ruby* it would be
vacuous.

**The repair, and it is a one-line change of continuation.** Not every context
is value-only. A statement sequence is not:

```
$ ruby -e 'while true; break; 1; end'     # legal
$ ruby -e 'def f; return 1; 2; end; p f'  # legal, prints 1
```

Evaluating that `break` happens under `[seqK [1], whileBodyK …]`, and `seqK`
falls into `unwind`'s catch-all arm — pop the frame, pass the jump on — exactly
as `asgnK` does. So the same `rfl` proves the same failure at a continuation a
legal program really does deliver a jump to.

**What "reachable" means here, stated precisely, because the objection is about
exactly this.** The *whole-machine* state during `while true; break; 1; end` has
`kont = [seqK [1], whileBodyK …]`, never `[seqK [1]]` alone. The configuration
below is the **sub-computation view**: `e` is the `break` statement run from an
empty continuation, `K` is the rest. That view is not a lie added by this file —
it is precisely the fiction `wp_bind` requires, since `wp e {…}` reasons about
`e` on its own. So the right reading is:

* for `asgnK`, the grammar guarantees the hole never holds an escaping jump, so
  the obstruction cannot arise and bind would be fine;
* for `seqK`, the hole *can* hold an escaping jump, the obstruction arises the
  first time you decompose a statement sequence, and bind is unavailable.

Since `Deriv.seq`/`JudgeSeq.cons` is the rule that decomposes statement
sequences, this is not an exotic corner. -/

/-- The same `rfl`, at a continuation a legal program delivers jumps to. -/
theorem step_fill_jump_seqK (es : List Expr) (j : Jump) (r : MRest) (h : Heap) :
    Interp.stepFn ((fillK [.seqK es] (jumpCfg j r)).load h)
      = .next ((jumpCfg j r).load h) := rfl

/-- **Law 3 is false at `seqK`** — and unlike the `asgnK` version, the witness is
the sub-computation view of a program CRuby accepts (`while true; break; 1; end`,
whose `break` is evaluated under `[seqK [1], …]`). -/
theorem ctx_law3_fails_seqK (es : List Expr) (h : Heap) :
    ¬ Language.Context (Expr := Cfg) (State := Heap) (Obs := Empty) (Val := CVal)
        (fillK [.seqK es]) := by
  intro hC
  obtain ⟨e', heq, -⟩ :=
    hC.primStep_fill_inv (e := jumpCfg (.brkJ .nil) default) (σ := h)
      rfl (CStep.next (step_fill_jump_seqK es (.brkJ .nil) default h))
  exact not_in_image_of_fillK (by simp) _ rfl ⟨e', heq.symm⟩


/-! ### The census: which continuations can reachably hold a jump?

The correction above suggested a hybrid — Iris bind for the continuations Ruby's
grammar keeps jump-free, hand-rolled decomposition for the rest. **The census
kills it: there are no jump-free continuations.** Three steps.

**1. Which konts does `unwind` give a dedicated arm?** Thirteen of the
forty-nine: `whileCondK`, `whileBodyK`, `forStartK`, `forBodyK`, `frameK`,
`blkFrameK`, `definedGuardK`, `catchK`, `beginBodyK`, `rescMatchK`, `rescueK`,
`elseK`, `ensureK`. These are *designed* to receive jumps, so they are
jump-transparent by construction. The other thirty-six fall into the catch-all
(`| _ => .next (withCtl m (.jump j))`) — pop the frame, pass the jump on.

**2. Can a *syntactic* jump reach the catch-all konts?** Almost never. Ruby's
**void value expression** rule confines `break`/`next`/`redo`/`retry`/`return`
to statement position. Measured against CRuby 4.0.5, with the jump placed in
each kont's source position and wrapped in `while true; … ; end` so the jump
itself is contextually legal [V]:

| position | kont | parses? |
|---|---|---|
| `break; 1` | `seqK` | **yes** |
| `x = break` | `asgnK` | no — *Invalid break* |
| `X = break` | `casgnK` | no |
| `if break then 1 end` | `ifK` | no |
| `(break).foo` | `recvK` | no |
| `foo(break)` | `argsK` | no |
| `[break]` / `[*(break)]` | `arrK` / `arrSplatK` | no |
| `{(break) => 1}` / `{1 => break}` | `hshKeyK` / `hshValK` | no |
| `foo(a: break)` | `kwPairK` | no |
| `yield(break)` / `super(break)` | `yieldArgK` / `superArgK` | no |
| `break(break)` | `jumpValK` | no |
| `def f(a = break)` | `optDefK` | no |
| `(break)::Foo` / `class Foo < (break)` | `cpathK` / `classDefK` | no |
| `defined?((break).foo)` | `definedRecvK` | no |
| `while (break); end` | `whileCondK` | no |

So on the syntactic jumps the objection is exactly right, and `seqK` is the lone
survivor — which is why `ctx_law3_fails_seqK` above is the version with a
grammatically real witness.

**3. But the jump family has two halves, and only one is grammar-restricted.**
`raiseJ` and `throwJ` are produced by *ordinary method calls* — `raise` and
`throw` are methods, not syntax — so no void-value rule touches them. Measured
[V]: `x = (raise "boom")`, `foo(raise("boom"))`, `[raise("boom")]`,
`(raise "boom").foo`, `if raise("boom") then 1 end`, `{1 => raise("boom")}`,
`def f(a = raise("boom"))`, `x = (throw :t)` — **all parse**.

And `raiseErr` leaves the continuation alone (`ratchet`'s `raiseErr_kont`), so
evaluating `x = raise("boom")` really does put a `raiseJ` in flight with
`asgnK` innermost.

**Conclusion.** Every continuation can reachably hold a jump; the grammar buys
an exemption for five of the seven jump constructors and none at all for the two
that matter most. There is no value-only sub-language to run Iris bind on, and
the hybrid is not available. `ctx_law3_fails` at `asgnK` — the theorem the
objection appeared to refute — turns out to be reachably witnessed after all,
just by a raise rather than a `break`. -/

/-- `ctx_law3_fails`, instantiated at the jump that no grammar rule restricts.
The witness is the sub-computation view of `x = (raise "boom")`. -/
theorem ctx_law3_fails_raise (x : String) (h : Heap) :
    ¬ Language.Context (Expr := Cfg) (State := Heap) (Obs := Empty) (Val := CVal)
        (fillK [.asgnK .lvar x]) := by
  intro hC
  obtain ⟨e', heq, -⟩ :=
    hC.primStep_fill_inv (e := jumpCfg (.raiseJ .nil) default) (σ := h)
      rfl (CStep.next (step_fill_jump x (.raiseJ .nil) default h))
  exact not_in_image_of_fillK (by simp) _ rfl ⟨e', heq.symm⟩

#print axioms instLanguageCfg
#print axioms ctx_law3_fails
#print axioms ctx_law3_fails_seqK
#print axioms ctx_law3_fails_raise
#print axioms law2_of_stepFn_frame

end RubyCore.HCtx
