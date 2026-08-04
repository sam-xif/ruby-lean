/-
T5 (`class_hierarchy`) — the object-model dispatch invariant, calibration toy of
`type-safety-by-reachability.md` §9.1. The smallest setting where "prove
type-safe" *requires* an invariant over the object model (which receivers
respond to a method), i.e. a store-typing clause rather than a value shape.

This file lands the **core object-model progress lemma** `dispatch_progress`:
a configuration poised to dispatch a method that the *heap's method table
resolves* takes a step (to the method activation), and therefore is not one step
from a type-family `uncaught` (`¬ aboutToTypeStick`). This is exactly the clause
"the receiver responds to `m`" from the design doc §4.2 — the substantive
consecution obligation — proved once, reusably, over the real `stepFn`/`invoke`.

WHY THIS IS THE HARD PART, AND WHAT IT UNBLOCKS
- Dispatch bottoms out in `invoke`, which L52 turned from `partial` into a
  well-founded `def`; only then did it gain equational lemmas (`invoke.eq_def`)
  so a dispatch step can be *reasoned about* at all. `dispatch_progress` is the
  first proof to exercise that: `rw [invoke.eq_def]` then drive
  `invoke.invokeDispatch` with the resolution hypotheses.
- The lemma is **parameterized over the heap** via resolution hypotheses
  (`hlook`/`hbtw`/`hsing`/…) rather than a concrete heap — useful when the heap
  is abstract (mid-program loop entry). NOTE (L55): `Boot.initHeap` is now
  *kernel-reducible* (its `Array.qsort` + monadic build loop were replaced by a
  structural insertion sort + `List.foldl`), so concrete boot-heap resolution
  facts (`lookup Boot.initHeap … = some …`, `crubyShadow … = none`, …) are now
  dischargeable by **`decide`, axiom-clean** — no `native_decide`. What still
  needs `native_decide` is *running* the program (`invoke`'s well-founded
  recursion compiles to `Acc.rec`, which the kernel won't evaluate); that is
  Direction A, not the invariant reasoning.

RESULTING ARCHITECTURE for a full closed-program T5 (increment 3)
  A conditional `invariant_sound` assembly whose `cons` uses `dispatch_progress`
  at the dispatch shapes and `safe` reads off the "no type-family raise in
  flight" clause. Its resolution hypotheses are now discharged **axiom-clean by
  `decide`** over the (reducible) reachable heaps — so the whole Direction-B
  proof, including the concrete `Machine.init program` instantiation, can be
  axiom-clean. (A builtin-dispatch loop like `while true; 1.succ; end` is the
  simplest instance: heap stays `initHeap`, no frame growth, resolution by
  `decide`.) `native_decide` is reserved for the separate Direction-A execution
  certificates (`T5Concrete`/`QLearningTypeSafe`).
-/
import RubyCore.Proof.TypeSafety

namespace RubyCore
namespace Proof
namespace T5

open Interp

/-- **Object-model progress.** A config whose control is a receiver value and
    whose top continuation is a zero-arg explicit send `recv.m` (`recvK`) takes a
    step, provided the heap's method table *resolves* `m` on `recv` to a
    user-defined method (`hlook` + `hb`/`hu`) with none of the CRuby-fidelity
    dispatch gates firing (`hbtw`/`hsing`) and simple (here: empty) params
    (`hp`). The receiver is a plain instance (`hpay`/`heigen`), as produced by
    `Class#new`.

    The step lands in the method activation (`enterUserMethod` → `.eval body`),
    i.e. it does NOT take the `dispatchMiss` → `NoMethodError` branch. This is
    the "receiver responds to `m`" store-typing clause of
    `type-safety-by-reachability.md` §4.2, discharged over the real interpreter. -/
theorem dispatch_progress
    (m : Machine) (o owner : ObjId) (md : MethodDef) (rest : List Kont)
    (hctl : m.ctl = .value (.ref o))
    (hk : m.kont = .recvK "m" [] .none .explicit :: rest)
    (hpay : (m.heap.get o).payload = .none)
    (heigen : (m.heap.get o).eigen = none)
    (hlook : lookup m.heap (.ref o) "m" = some (owner, md))
    (hb : md.builtin = none) (hu : md.undefined = false) (hp : md.params = [])
    -- the method is public: an *explicit*-receiver send to a private/protected
    -- method raises instead of entering the activation (visibility, L71)
    (hvis : md.visibility = .pub)
    -- not a prelude method, so the between-chain shadow check is the plain one
    -- (a prelude method suppresses it for its own name, L62)
    (hpre : md.fromPrelude = false)
    (hbtw : crubyShadow m.heap
              ((ancestors m.heap ((m.heap.get o).klass)).takeWhile (· != owner)) "m" = none)
    (hsing : crubySingletonShadow m.heap (.ref o) "m" = none) :
    ∃ m', stepFn m = .next m' := by
  simp only [stepFn, hctl, applyKont, hk, startArgs, finishSend]
  rw [invoke.eq_def]
  simp only [invoke.invokeDispatch, classOf, heigen, hlook, hpay, hb, hu, hbtw, hsing,
    visError?, hvis, hpre, Option.isNone_some, Bool.and_false, reduceIte, reduceBEq,
    Bool.or_eq_true, Bool.false_or, or_self, Bool.false_eq_true, if_false, ite_false]
  simp only [enterUserMethod, hp]
  exact ⟨_, rfl⟩

/-- The same config is **not about to type-stick**: a resolvable dispatch steps
    (`.next`), and `aboutToTypeStick` requires a `.uncaught` step — the `safe`
    (progress) obligation of `invariant_sound` at a dispatch shape. -/
theorem dispatch_not_typestick
    (m : Machine) (o owner : ObjId) (md : MethodDef) (rest : List Kont)
    (hctl : m.ctl = .value (.ref o))
    (hk : m.kont = .recvK "m" [] .none .explicit :: rest)
    (hpay : (m.heap.get o).payload = .none)
    (heigen : (m.heap.get o).eigen = none)
    (hlook : lookup m.heap (.ref o) "m" = some (owner, md))
    (hb : md.builtin = none) (hu : md.undefined = false) (hp : md.params = [])
    -- the method is public: an *explicit*-receiver send to a private/protected
    -- method raises instead of entering the activation (visibility, L71)
    (hvis : md.visibility = .pub)
    -- not a prelude method, so the between-chain shadow check is the plain one
    -- (a prelude method suppresses it for its own name, L62)
    (hpre : md.fromPrelude = false)
    (hbtw : crubyShadow m.heap
              ((ancestors m.heap ((m.heap.get o).klass)).takeWhile (· != owner)) "m" = none)
    (hsing : crubySingletonShadow m.heap (.ref o) "m" = none) :
    ¬ aboutToTypeStick m := by
  obtain ⟨m', hnext⟩ :=
    dispatch_progress m o owner md rest hctl hk hpay heigen hlook hb hu hp hvis hpre hbtw hsing
  unfold aboutToTypeStick typeStuck
  rw [hnext]
  exact not_false

/- Boot-heap resolution facts are now **`decide`-able, axiom-clean** — since
   `initHeap` reduces (L55). The hypotheses `dispatch_progress` takes are of
   exactly this decidable shape, so a full Direction-B proof over concrete
   (reducible) reachable heaps needs no `native_decide`. Demonstration: the boot
   object model resolves `Integer#succ`. -/
set_option maxRecDepth 4000 in
example : (lookup Boot.initHeap (.int 1) "succ").isSome = true := by decide

end T5
end Proof
end RubyCore
