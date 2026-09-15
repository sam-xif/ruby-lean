import RubyCore.Proof.Static.Decls

/-!
# Wall 1's machine step — the native block iterator

`homebrew/HANDOFF.md` §Wall 1. Every block send in the Homebrew slice bottoms out
here: **measured** at L244 by tracing `[1,2].m { |x| x }` for each of the sixteen
block methods the slice uses, and `iterK` appears in fifteen of them. `select`,
`any?`, `find`, `filter_map`, `flat_map`, `partition`, `sort_by`, `reject`, `all?`,
`to_h` and `zip` are *prelude* Enumerable methods, and every one of them shows **two**
method frames — its own activation, and the `startIter` activation underneath the
block frames, because its Ruby body calls `each`. Only `tap` reaches a block frame
without an iterator.

> **That corrects `HANDOFF.md`'s split.** It priced Wall 1 as *the native-iterator
> rung (20 of the 30-odd sends) and the prelude-Enumerable rung behind it*, as two
> populations. They are not two populations: the native iterator is the **floor** of
> both, and the prelude rung sits on top of it. So this file is not one of two
> alternatives — it is the shared prerequisite, and nothing about a block send can
> be proved before it.

This file is the *machine* half and nothing else: what one step does, stated so that
`KontOk`'s block arms and the third `EntryOk` arm have something to be about. No
`infer` rule reads any of it, so it is inert by construction.
-/

namespace RubyCore
namespace Proof
namespace Static

open RubyCore.Types
open RubyCore.Interp

set_option maxHeartbeats 1000000

/-- The closure `reifyBlock` builds — named so that the statements below can refer
    to it instead of reproducing the literal, which is the discipline L212 recorded
    (`superFound`): *a definition the proof needs to name belongs in the code*. Here
    the definition is one field-for-field copy of a `let` inside `reifyBlock`, so it
    is named on the proof side and pinned by `reifyBlock_eq` below. -/
def blockClosure (m : Machine) (ps : List Param) (ls : List String) (body : Expr)
    (lam : Bool) : Closure :=
  { params := ps, locals := ls, body := body,
    captured := some (m.stack.headD 0), home := returnTarget m, lam := lam }

theorem reifyBlock_eq (m : Machine) (ps : List Param) (ls : List String) (body : Expr)
    (lam : Bool) :
    reifyBlock m ps ls body lam
      = (.ref m.heap.objs.size,
         { m with heap := ⟨m.heap.objs.push
             { klass := Boot.procId, payload := .proc (blockClosure m ps ls body lam) }⟩ }) := by
  rfl

/-- **A literal block reaches `invoke` as an allocated `Proc`, and nothing else about
    the send moves** — the first of the two reductions the block step needs.

    Every guard `finishSend` puts between the reification and the dispatch is a test on
    the *method name* (`lambda`, `proc`, `new`) or on the site, so at a name that is
    none of those the whole block is one `Proc` allocation followed by `invoke`. Stated
    at an abstract `mname` with those three ruled out, because the iterator table has
    sixteen entries and none of them should need its own copy of this. -/
theorem finishSend_lit {m : Machine} {recv : Value} {site : SendSite} {mname : String}
    {args : List Value} {ps : List Param} {ls : List String} {body : Expr}
    (hl : mname ≠ "lambda") (hp : mname ≠ "proc") (hn : mname ≠ "new") :
    finishSend m recv site mname args (.lit ps ls body)
      = invoke (reifyBlock m ps ls body false).2 recv site mname args
          (some (reifyBlock m ps ls body false).1) [] := by
  have hml : (site == SendSite.implicit && mname == "lambda") = false := by simp [hl]
  unfold finishSend
  simp only [hml, beq_iff_eq, hp, hn, Bool.and_false, Bool.false_eq_true, if_false,
    and_false]
  split <;> simp_all

/-- **…and the dispatch is the native iterator** — the second reduction, and the one
    that says which step a block row would be a claim about.

    Three hypotheses and each is a real side condition rather than bookkeeping:

    * `hlk` — **the name must miss.** `tryIterator` is reached from `dispatchMiss`, so a
      program that reopens `Array` and defines `each` takes a different step entirely.
      That is the clause a block row's `EntryOk` arm will have to carry, and it is the
      one a `defineMethod` has to preserve.
    * `hpay` — the receiver's payload is an `Array`. `plainRecv`'s sixth clause (L230)
      is the bridge from `.cls "Array"` to this, so a typed receiver supplies it.
    * `hproc` — the block value really is a `Proc` over `cl`, which `reifyBlock_eq`
      supplies at the allocation.

    Stated at `each` rather than at an abstract iterator name: `tryIterator`'s `match`
    on the name is a sixteen-way split with a different `IterKind`, element list and
    seed in each arm, so there is no shared statement — each row that is ever declared
    pays for its own copy of this lemma, and the shape of that copy is this one. -/
theorem invoke_iter_each {m : Machine} {o bo : ObjId} {xs : Array Value} {cl : Closure}
    {site : SendSite}
    (hpay : (m.heap.get o).payload = .arr xs)
    (hproc : (m.heap.get bo).payload = .proc cl)
    (hlk : lookup m.heap (.ref o) "each" = none) :
    invoke m (.ref o) site "each" [] (some (.ref bo)) []
      = startIter m (.ref o) "each" cl (xs.toList.map (fun e => [e])) .ignore []
          (.ref o) := by
  rw [invoke.eq_def]
  simp only [beq_iff_eq, reduceCtorEq, Bool.or_self, Bool.false_eq_true, if_false,
    hpay]
  rw [invoke.invokeDispatch.eq_def]
  simp only [hlk, appendKwHash, List.isEmpty_nil, if_true]
  unfold dispatchMiss
  simp only [tryIterator, hproc, hpay]
  split <;> rfl

/-- **`startIter` is a frame push and a `frameK`**, and nothing else — the activation
    a `break` returns from, under the continuation that pops it. `rfl`, and it is here
    so the shape has a name. -/
theorem startIter_eq (m : Machine) (recv : Value) (mname : String) (cl : Closure)
    (elemArgs : List (List Value)) (kind : IterKind) (initAcc : List Value)
    (retVal : Value) :
    startIter m recv mname cl elemArgs kind initAcc retVal
      = iterStep
          { m with
            frames := m.frames.push
              { self := recv, defmod := classOf m.heap recv, kind := .method, meth := mname,
                cref := m.currentFrame.cref },
            stack := m.frames.size :: m.stack,
            kont := .frameK m.frames.size :: m.kont }
          cl m.frames.size elemArgs kind initAcc retVal := rfl

/-- **One turn of the loop**: the `iterK` that remembers the rest, then the block call. -/
theorem iterStep_cons (m : Machine) (cl : Closure) (brk : FrameId)
    (a : List Value) (rest : List (List Value)) (acc : List Value) (retVal : Value) :
    iterStep m cl brk (a :: rest) .ignore acc retVal
      = callClosure { m with kont := .iterK cl brk rest .ignore acc retVal (a.headD .nil) :: m.kont }
          cl a (some brk) := rfl

/-- **And the empty loop**: the iterator's own answer, with the `frameK` still standing. -/
theorem iterStep_nil (m : Machine) (cl : Closure) (brk : FrameId)
    (acc : List Value) (retVal : Value) :
    iterStep m cl brk [] .ignore acc retVal = .next (withCtl m (.value retVal)) := rfl

/-- **The block call, for the one parameter shape the first rule will admit.**

    `|x|` and nothing else: a single required positional, no block-local names, not a
    lambda. Each of the three hypotheses turns off one branch of `callClosure` —
    `classifySimple` succeeds, the auto-splat test needs `required ≥ 2` (or a `rest`),
    and `arityOk` is vacuous off a lambda — and each is a **syntactic** condition on
    the `.block` node, so `infer`'s rule can check all three.

    The frame it builds is the one `FrameConforms` had to be generalized for (L243):
    `captured := cl.captured`, and the parameter is in its *own* `locals`, so the
    read of a parameter is one lookup and the read of an enclosing local is one hop. -/
theorem callClosure_req1 {m : Machine} {cl : Closure} {x : String} {v : Value}
    {brk : FrameId} (hps : cl.params = [.req x]) (hls : cl.locals = [])
    (hlam : cl.lam = false) :
    callClosure m cl [v] (some brk)
      = .next (withKont
          { m with
            frames := m.frames.push
              { self := (m.frames.getD (cl.captured.getD 0) default).self,
                defmod := (m.frames.getD (cl.captured.getD 0) default).defmod,
                blk := (m.frames.getD (cl.captured.getD 0) default).blk,
                locals := [(x, v)], kind := .block, captured := cl.captured,
                home := cl.home, lam := cl.lam,
                cref := (m.frames.getD (cl.captured.getD 0) default).cref },
            stack := m.frames.size :: m.stack }
          (.eval cl.body) (.blkFrameK m.frames.size cl.lam (some brk) cl [v])) := by
  unfold callClosure
  simp only [hps, hls, hlam, classifySimple]
  rfl

/-! ## The five compose, and this is the checked fact that says so

Kept in the build rather than as a comment, for the reason `Types/Decls.lean` keeps its
own: a capability nothing asserts is a capability nothing notices breaking. It is
deliberately weak — *the step lands in the block body* — because the strong form is the
consecution case, which needs `Inv`'s pieces in hand and belongs with them. What it pins
is the **shape of the chain**: five rewrites, no case split, no `Builtins.run`. -/
theorem get_push_self (a : Array Object) (ob : Object) :
    (Heap.get ⟨a.push ob⟩ a.size) = ob := by
  simp [Heap.get, Array.getD, Array.size_push]

example {m : Machine} {o : ObjId} {x : String} {body : Expr} {site : SendSite}
    {x₀ : Value} {rest : List Value}
    (hpay : ((reifyBlock m [.req x] [] body false).2.heap.get o).payload
      = .arr ⟨x₀ :: rest⟩)
    (hlk : lookup (reifyBlock m [.req x] [] body false).2.heap (.ref o) "each" = none) :
    ∃ m', finishSend m (.ref o) site "each" [] (.lit [.req x] [] body) = .next m'
      ∧ m'.ctl = .eval body := by
  rw [finishSend_lit (by simp) (by simp) (by simp)]
  rw [reifyBlock_eq] at hpay hlk ⊢
  rw [invoke_iter_each (cl := blockClosure m [.req x] [] body false) hpay
    (by simpa using congrArg Object.payload (get_push_self m.heap.objs _)) hlk]
  rw [startIter_eq]
  show ∃ m', iterStep _ _ _ (List.map (fun e => [e]) (x₀ :: rest)) _ _ _ = .next m'
    ∧ m'.ctl = .eval body
  rw [List.map_cons, iterStep_cons,
    callClosure_req1 (cl := blockClosure m [.req x] [] body false) rfl rfl rfl]
  exact ⟨_, rfl, rfl⟩

/-- **The lambda literal's whole step** (L261), and it is `finishSend`'s `mkLam` branch:
    `reifyBlock` and nothing else — no dispatch, no frame, no continuation. Written as a
    reduction here beside the five block-send ones because it is the same allocation, and
    L257's `_grow` transports are what the consecution case then spends.

    **Corrected: it needs the non-shadowing hypothesis, and used to be stated without one.**
    `lambda` is a `Kernel` method, so a user `def lambda` shadows it and the send is an
    ordinary dispatch carrying the block — the model was taught that in `finishSend`'s
    `shadowed` test (`found-issues.md` §A5), and this theorem's `rfl` silently stopped
    holding at that commit. It went unnoticed because `Proof/` is off the default build
    target, which is the same failure mode `scripts/check-proofs.sh` exists to catch.
    `hsh` says exactly what `mkLam` needs: whatever the ancestor walk finds for `lambda`
    on the receiver's class, it is not a user (non-builtin, defined) entry. -/
theorem startArgs_lambda (m : Machine) (ps : List Param) (ls : List String) (body : Expr)
    (hsh : ∀ own md, methodOn m.heap (classOf m.heap m.currentFrame.self) "lambda"
            = some (own, md) → (md.builtin.isNone && !md.undefined) = false) :
    startArgs m m.currentFrame.self SendSite.implicit "lambda" [] []
        (PendingBlk.lit ps ls body)
      = RubyCore.StepResult.next (withCtl (reifyBlock m ps ls body true).2
          (.value (reifyBlock m ps ls body true).1)) := by
  simp only [startArgs, finishSend]
  cases h : methodOn m.heap (classOf m.heap m.currentFrame.self) "lambda" with
  | none => simp
  | some p =>
    obtain ⟨own, md⟩ := p
    simp [hsh own md h]

end Static
end Proof
end RubyCore
