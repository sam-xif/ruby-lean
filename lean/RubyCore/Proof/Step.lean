/-
Proof-of-concept metatheory for the L0 stepper (kept OUT of the default build
target — see `implementation-notes.md` L13). This file authors an inductive
`Step` relation as an idiomatic rendering of `stepFn`'s transitions over an
effect-light *control-core* fragment, and is the substrate for the adequacy /
determinism / preservation theorems (`Adequacy.lean`).

Fragment (deliberately small so the PoC compiles and PROVES; extend head-by-
head, or scrap at L1):

  literals (int/flt/str/sym/true/false/nil/self), var + vasgn for
  local/ivar/global (ivar with a `ref` self — always true at toplevel), seq,
  if, while, dowhile, break/next/redo (the three loop jumps), and jump
  propagation past neutral konts.

Deliberately EXCLUDED — each is simply "no `Step` exists", which matches
`stepFn` returning `.unsupported`/`.stuck`/`.done`: send/dispatch, `return`
(needs a method frame from a send), begin/rescue/ensure, class/module/def,
const/casgn, arrays/hashes, class variables, and the frozen-immediate `@x=`
error path (unreachable in-fragment).

Why soundness is mechanical: `stepFn` and its helpers are total *structural*
functions, so each constructor's target is *definitionally* the value `stepFn`
produces — one uniform `cases` + `simp` discharges every rule.
-/
import RubyCore.Interp

namespace RubyCore
namespace Proof

open Interp

/-- The machine after consuming the top kont (mirrors the
    `let m := { m with kont := rest }` opening `applyKont`/`unwind`). -/
abbrev pop (m : Machine) (rest : List Kont) : Machine := { m with kont := rest }

/-- Popping a kont leaves the current frame (and hence `self`) unchanged;
    lets the `ivar` rules relate `(pop m rest).currentFrame` to `m`'s. -/
@[simp] theorem pop_currentFrame (m : Machine) (rest : List Kont) :
    (pop m rest).currentFrame = m.currentFrame := rfl

/-- Popping a kont leaves the heap unchanged (needed by the frozen-`@x=` rule,
    whose guard reads `(pop m rest).heap`). -/
@[simp] theorem pop_heap (m : Machine) (rest : List Kont) :
    (pop m rest).heap = m.heap := rfl

/-- One transition of the control-core fragment, authored to mirror `stepFn`.
    Every constructor's image is syntactically the value `stepFn` produces. -/
inductive Step : Machine → Machine → Prop where
  /- ── literals & self (eval → value) ── -/
  | intLit {m n} :
      m.ctl = .eval (.int n) → Step m (withCtl m (.value (.int n)))
  | fltLit {m x} :
      m.ctl = .eval (.flt x) → Step m (withCtl m (.value (.flt x)))
  | strLit {m s} :
      m.ctl = .eval (.str s) →
      Step m (withCtl
        { m with heap := { objs := m.heap.objs.push
                             { klass := Boot.stringId, payload := .str s } } }
        (.value (.ref m.heap.objs.size)))
  | symLit {m s} :
      m.ctl = .eval (.sym s) → Step m (withCtl m (.value (.sym s)))
  | truLit {m} :
      m.ctl = .eval .tru → Step m (withCtl m (.value (.bool true)))
  | flsLit {m} :
      m.ctl = .eval .fls → Step m (withCtl m (.value (.bool false)))
  | nilLit {m} :
      m.ctl = .eval .nil → Step m (withCtl m (.value .nil))
  | selfLit {m} :
      m.ctl = .eval .self' → Step m (withCtl m (.value m.currentFrame.self))
  /- ── variable reads ── -/
  | varLvar {m x} :
      m.ctl = .eval (.var .lvar x) → Step m (withCtl m (.value (m.getLocal x)))
  /-- A **plain** global read. `$1`…`$9`, `$&`, `` $` `` and `$'` are views of the
      last match, derived rather than stored (L101), so a read of one is not a
      `getGlobal` at all; `matchGlobal` is consulted first. The hypothesis is the
      semantic one `stepFn` actually branches on, and `Adequacy`'s fragment
      predicate supplies it from the *syntactic* `isMatchView` (N40). -/
  | varGvar {m x} :
      m.ctl = .eval (.var .gvar x) → matchGlobal m x = none →
      Step m (withCtl m (.value (m.getGlobal x)))
  | varIvar {m x o} :
      m.ctl = .eval (.var .ivar x) → m.currentFrame.self = .ref o →
      Step m (withCtl m (.value
        (((m.heap.get o).ivars.find? (·.1 == x)).map (·.2) |>.getD .nil)))
  /- ── variable writes (evaluate RHS under an asgnK) ── -/
  | vasgnLvar {m x rhs} :
      m.ctl = .eval (.vasgn .lvar x rhs) →
      Step m (withKont m (.eval rhs) (.asgnK .lvar x))
  | vasgnIvar {m x rhs} :
      m.ctl = .eval (.vasgn .ivar x rhs) →
      Step m (withKont m (.eval rhs) (.asgnK .ivar x))
  | vasgnGvar {m x rhs} :
      m.ctl = .eval (.vasgn .gvar x rhs) →
      Step m (withKont m (.eval rhs) (.asgnK .gvar x))
  /- ── control-flow eval ── -/
  | ifEval {m c t e} :
      m.ctl = .eval (.if' c t e) → Step m (withKont m (.eval c) (.ifK t e))
  | whileEval {m c body} :
      m.ctl = .eval (.while' c body) →
      Step m (withKont m (.eval c) (.whileCondK c body))
  | dowhileEval {m body cond} :
      m.ctl = .eval (.dowhile body cond) →
      Step m (withKont m (.eval body) (.whileBodyK cond body))
  | brkSome {m e} :
      m.ctl = .eval (.brk (some e)) →
      Step m (withKont m (.eval e) (.jumpValK .brkK))
  | brkNone {m} :
      m.ctl = .eval (.brk none) → Step m (withCtl m (.jump (.brkJ .nil)))
  | nxtSome {m e} :
      m.ctl = .eval (.nxt (some e)) →
      Step m (withKont m (.eval e) (.jumpValK .nxtK))
  | nxtNone {m} :
      m.ctl = .eval (.nxt none) → Step m (withCtl m (.jump (.nxtJ .nil)))
  | redoEval {m} :
      m.ctl = .eval .redo' → Step m (withCtl m (.jump .redoJ))
  /- ── seq eval ── -/
  | seqNil {m} :
      m.ctl = .eval (.seq []) → Step m (withCtl m (.value .nil))
  | seqOne {m e} :
      m.ctl = .eval (.seq [e]) → Step m (withCtl m (.eval e))
  | seqCons {m e a b} :
      m.ctl = .eval (.seq (e :: a :: b)) →
      Step m (withKont m (.eval e) (.seqK (a :: b)))
  /- ── kont application (value in flight) ── -/
  | seqKNil {m v rest} :
      m.ctl = .value v → m.kont = .seqK [] :: rest →
      Step m (withCtl (pop m rest) (.value v))
  | seqKCons {m v e es rest} :
      m.ctl = .value v → m.kont = .seqK (e :: es) :: rest →
      Step m (withKont (pop m rest) (.eval e) (.seqK es))
  | asgnKLvar {m v x rest} :
      m.ctl = .value v → m.kont = .asgnK .lvar x :: rest →
      Step m (withCtl ((pop m rest).setLocal x v) (.value v))
  | asgnKGvar {m v x rest} :
      m.ctl = .value v → m.kont = .asgnK .gvar x :: rest →
      Step m (withCtl ((pop m rest).setGlobal x v) (.value v))
  | asgnKIvar {m v x o rest} :
      m.ctl = .value v → m.kont = .asgnK .ivar x :: rest →
      m.currentFrame.self = .ref o → (m.heap.get o).frozen = false →
      Step m (withCtl (bindIvar (pop m rest) x v) (.value v))
  /-- `@x = v` with a *frozen* `ref` self raises `FrozenError` (L2); the
      message embeds the receiver's `inspect`, so this fires only when that
      `inspect` is pure (`= .ok r`) — otherwise `stepFn` gates (`.unsupported`,
      no `Step`). -/
  | asgnKIvarFrozen {m v x o rest r} :
      m.ctl = .value v → m.kont = .asgnK .ivar x :: rest →
      m.currentFrame.self = .ref o → (m.heap.get o).frozen = true →
      Builtins.inspectP (pop m rest) (.ref o) = .ok r →
      Step m (raiseErr (pop m rest) Boot.frozenErrorId
        s!"can't modify frozen {className (pop m rest).heap ((pop m rest).heap.get o).klass}: {r}")
  | ifKTrue {m v t e rest} :
      m.ctl = .value v → m.kont = .ifK t e :: rest → v.truthy = true →
      Step m (withCtl (pop m rest) (.eval t))
  | ifKFalseSome {m v t e rest} :
      m.ctl = .value v → m.kont = .ifK t (some e) :: rest → v.truthy = false →
      Step m (withCtl (pop m rest) (.eval e))
  | ifKFalseNone {m v t rest} :
      m.ctl = .value v → m.kont = .ifK t none :: rest → v.truthy = false →
      Step m (withCtl (pop m rest) (.value .nil))
  | whileCondKTrue {m v c body rest} :
      m.ctl = .value v → m.kont = .whileCondK c body :: rest → v.truthy = true →
      Step m (withKont (pop m rest) (.eval body) (.whileBodyK c body))
  | whileCondKFalse {m v c body rest} :
      m.ctl = .value v → m.kont = .whileCondK c body :: rest → v.truthy = false →
      Step m (withCtl (pop m rest) (.value .nil))
  | whileBodyK {m v c body rest} :
      m.ctl = .value v → m.kont = .whileBodyK c body :: rest →
      Step m (withKont (pop m rest) (.eval c) (.whileCondK c body))
  | jumpValKBrk {m v rest} :
      m.ctl = .value v → m.kont = .jumpValK .brkK :: rest →
      Step m (withCtl (pop m rest) (.jump (.brkJ v)))
  | jumpValKNxt {m v rest} :
      m.ctl = .value v → m.kont = .jumpValK .nxtK :: rest →
      Step m (withCtl (pop m rest) (.jump (.nxtJ v)))
  /- ── jump unwinding (break/next in flight) ── -/
  | unwindWhileCondBrk {m v c body rest} :
      m.ctl = .jump (.brkJ v) → m.kont = .whileCondK c body :: rest →
      Step m (withCtl (pop m rest) (.value v))
  | unwindWhileCondNxt {m v c body rest} :
      m.ctl = .jump (.nxtJ v) → m.kont = .whileCondK c body :: rest →
      Step m (withKont (pop m rest) (.eval c) (.whileCondK c body))
  | unwindWhileBodyBrk {m v c body rest} :
      m.ctl = .jump (.brkJ v) → m.kont = .whileBodyK c body :: rest →
      Step m (withCtl (pop m rest) (.value v))
  | unwindWhileBodyNxt {m v c body rest} :
      m.ctl = .jump (.nxtJ v) → m.kont = .whileBodyK c body :: rest →
      Step m (withKont (pop m rest) (.eval c) (.whileCondK c body))
  /- `redo` re-runs the loop body without re-testing the condition (artifact 04);
     both while markers route it to `eval body` under `whileBodyK` [V]. -/
  | unwindWhileCondRedo {m c body rest} :
      m.ctl = .jump .redoJ → m.kont = .whileCondK c body :: rest →
      Step m (withKont (pop m rest) (.eval body) (.whileBodyK c body))
  | unwindWhileBodyRedo {m c body rest} :
      m.ctl = .jump .redoJ → m.kont = .whileBodyK c body :: rest →
      Step m (withKont (pop m rest) (.eval body) (.whileBodyK c body))
  /- ── jump propagation past neutral konts (the `_` arm of `unwind`) ── -/
  | unwindPropSeqK {m j es rest} :
      m.ctl = .jump j → m.kont = .seqK es :: rest →
      Step m (withCtl (pop m rest) (.jump j))
  | unwindPropAsgnK {m j k x rest} :
      m.ctl = .jump j → m.kont = .asgnK k x :: rest →
      Step m (withCtl (pop m rest) (.jump j))
  | unwindPropIfK {m j t e rest} :
      m.ctl = .jump j → m.kont = .ifK t e :: rest →
      Step m (withCtl (pop m rest) (.jump j))
  | unwindPropJumpValK {m j kind rest} :
      m.ctl = .jump j → m.kont = .jumpValK kind :: rest →
      Step m (withCtl (pop m rest) (.jump j))

/-- **Soundness.** Every `Step` is exactly one `stepFn` transition. -/
theorem Step.sound {m m' : Machine} (h : Step m m') : stepFn m = .next m' := by
  cases h <;>
    simp_all [stepFn, evalExpr, applyKont, unwind, withCtl, withKont, pop,
              Machine.setLocal, Machine.setGlobal,
              Machine.currentFrame, bindIvar, Builtins.allocStr, Heap.alloc]

/-- **Determinism** — immediate from soundness + `.next` injectivity, because
    `stepFn` is a function. -/
theorem Step.deterministic {m a b : Machine} (ha : Step m a) (hb : Step m b) :
    a = b := by
  have h := hb.sound
  rw [ha.sound] at h
  exact (StepResult.next.injEq a b).mp h

end Proof
end RubyCore
