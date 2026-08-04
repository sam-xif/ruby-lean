/-
The actual T5 (`class_hierarchy`) Direction-B proof: a **user-defined method**
dispatched in an **unbounded loop** is type-safe, by an inductive object-model
invariant — axiom-clean, without running the program
(`type-safety-by-reachability.md` §4, §9.1).

Program (the loop, entered with class `A` defined and `x` an `A`-instance):

    while true do x.m end        # A#m returns 0

This is the user-class analogue of `DispatchLoop` (which dispatched a *builtin*).
The genuinely new ingredient is **frame-store growth**: every `x.m` call pushes
a method activation frame that is never reclaimed (`frameK` pops the activation
*stack*, not the frame *store*), so `frames` grows without bound across
iterations. The invariant therefore does NOT pin `frames`; it keeps only
`0 < frames.size ∧ frames[0] = F0` (frame 0 — holding `x` — is stable) and, in
the method-active shapes, an existential frame id. Frame-0 stability across a
push is `getD0_push`; the dispatch step (which resolves `A#m` in the class-bearing
heap `Hstar` and pushes the activation) is `dispatch_step`.

We start from a well-formed loop-entry config (via `invariant_sound_from`), which
isolates the object-model reasoning from the boot phase (class/`new` setup — that
is finite/Direction-A territory and orthogonal). `Hstar` is built by reducible
heap ops, so its resolution facts close by `decide` — **no `native_decide`**.
-/
import RubyCore.Proof.TypeSafety

namespace RubyCore
namespace Proof
namespace T5Loop

open Interp

set_option maxRecDepth 100000

/-! ### The class-bearing heap `Hstar` and the loop program -/

/-- Class `A` (id = `initHeap.size` = 37 — the boot heap grew with `Kernel`,
    `Numeric` and `UncaughtThrowError`, L65/L69) with one user method `m` ↦ `0`. -/
def clsA : ObjId := 37
/-- An instance of `A` (id 38). -/
def inst : ObjId := 38
def mMd : MethodDef := { params := [], body := .int 0, owner := clsA }
def clsAObj : Object :=
  { klass := Boot.classId,
    payload := .cls { superclass := some Boot.objectId, name := "A", methods := [("m", mMd)] } }
def instObj : Object := { klass := clsA }
/-- `initHeap` + class `A` (with method `m`) + one `A`-instance. Built by
    reducible `alloc`s, so lookups over it are `decide`-able. -/
def Hstar : Heap := ((Boot.initHeap.alloc clsAObj).2.alloc instObj).2

/-- `x.m` -/
abbrev bodyE : Expr := .send (some (.var .lvar "x")) "m" [] .none
/-- `while true do x.m end` -/
abbrev prog : Expr := .while' .tru bodyE

/-- The toplevel frame: `self = main`, local `x ↦ the A-instance`. -/
def F0 : Frame :=
  { self := .ref Boot.mainId, defmod := Boot.objectId, kind := .toplevel,
    cref := [Boot.objectId], locals := [("x", .ref inst)] }
/-- The method activation frame `x.m` pushes (its content is never read; only its
    presence + the frame id matter). -/
def mF : Frame :=
  { self := .ref inst, locals := [], defmod := clsA, cref := [], blk := none,
    kind := .method, meth := "m", captured := none, home := 0, lam := false }

/-- Continuation shapes. -/
abbrev kC : List Kont := [.whileCondK .tru bodyE]
abbrev kB : List Kont := [.whileBodyK .tru bodyE]
abbrev kR : List Kont := [.recvK "m" [] .none .explicit, .whileBodyK .tru bodyE]

/-! ### Frame / dispatch helper lemmas -/

/-- Frame 0 (`getD 0`) is preserved by a `push` (needs `frames` non-empty). -/
theorem getD0_push (a : Array Frame) (x : Frame) (hlt : 0 < a.size) :
    (a.push x).getD 0 default = a.getD 0 default := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push_lt hlt,
             Array.getElem?_eq_getElem hlt]

/-- `x` reads as the `A`-instance from frame 0 (over abstract/grown `frames`). -/
theorem getLocal_x (m : Machine) (hs : m.stack = [0])
    (hf : m.frames.getD 0 default = F0) : m.getLocal "x" = .ref inst := by
  unfold Machine.getLocal
  simp only [hs, List.headD_cons]
  rw [Machine.getLocal.go.eq_def]
  simp only [hf, F0]
  rfl

/-- The result config of the dispatch step (`x.m`): push the activation `mF`,
    run its body. -/
def mkNext (m : Machine) : Machine :=
  { m with ctl := .eval (.int 0), kont := [.frameK m.frames.size, .whileBodyK .tru bodyE], stack := m.frames.size :: m.stack, frames := m.frames.push mF }

set_option maxHeartbeats 2000000 in
/-- The dispatch step: `x.m` resolves `A#m` in `Hstar` and enters the activation.
    Reduces the well-founded `invoke` (`invoke.eq_def`); the `A#m` lookup closes
    by `rfl` over the reducible `Hstar` — axiom-clean, abstract `frames`. -/
theorem dispatch_step (m : Machine) (hctl : m.ctl = .value (.ref inst))
    (hkont : m.kont = kR) (hheap : m.heap = Hstar) :
    stepFn m = .next (mkNext m) := by
  simp only [stepFn, hctl, applyKont, hkont, kR, startArgs, finishSend, mkNext]
  rw [hheap, invoke.eq_def]
  rfl

/-! ### The inductive invariant -/

/-- Loop invariant: heap is the class-bearing `Hstar`, frame 0 is `F0`
    (`frames` may have grown), and `(ctl, kont, stack)` is one of nine shapes
    (seven with `stack = [0]`, two mid-method with `stack = [fid, 0]`). -/
def J (m : Machine) : Prop :=
  m.heap = Hstar ∧ 0 < m.frames.size ∧ m.frames.getD 0 default = F0 ∧
  ( (m.stack = [0] ∧
      ( (m.ctl = .eval prog ∧ m.kont = [])
      ∨ (m.ctl = .eval .tru ∧ m.kont = kC)
      ∨ (m.ctl = .value (.bool true) ∧ m.kont = kC)
      ∨ (m.ctl = .eval bodyE ∧ m.kont = kB)
      ∨ (m.ctl = .eval (.var .lvar "x") ∧ m.kont = kR)
      ∨ (m.ctl = .value (.ref inst) ∧ m.kont = kR)
      ∨ (m.ctl = .value (.int 0) ∧ m.kont = kB) ))
  ∨ (∃ fid, m.stack = [fid, 0] ∧
      ( (m.ctl = .eval (.int 0) ∧ m.kont = [.frameK fid, .whileBodyK .tru bodyE])
      ∨ (m.ctl = .value (.int 0) ∧ m.kont = [.frameK fid, .whileBodyK .tru bodyE]) )) )

/-- **Progress + preservation.** Every `J`-config steps to another `J`-config.
    (Both `cons` and `safe` fall out of this.) -/
theorem stepJ (m : Machine) (hJ : J m) : ∃ m', stepFn m = .next m' ∧ J m' := by
  obtain ⟨hheap, hsize, hgetD0, hd⟩ := hJ
  rcases hd with ⟨hstack, hc⟩ | ⟨fid, hstack, hc⟩
  · -- stack = [0]
    rcases hc with ⟨hctl, hkont⟩ | ⟨hctl, hkont⟩ | ⟨hctl, hkont⟩ | ⟨hctl, hkont⟩ |
                   ⟨hctl, hkont⟩ | ⟨hctl, hkont⟩ | ⟨hctl, hkont⟩
    · -- P0: eval prog → eval tru, kC
      refine ⟨_, by simp only [stepFn, hctl, prog, evalExpr, withKont, hkont]; rfl, ?_⟩
      exact ⟨hheap, hsize, hgetD0, Or.inl ⟨hstack, Or.inr (Or.inl ⟨rfl, by simp [kC]⟩)⟩⟩
    · -- P1: eval tru → value true, kC
      refine ⟨_, by simp only [stepFn, hctl, evalExpr, withCtl]; rfl, ?_⟩
      exact ⟨hheap, hsize, hgetD0, Or.inl ⟨hstack, Or.inr (Or.inr (Or.inl ⟨rfl, hkont⟩))⟩⟩
    · -- P2: value true, kC → eval bodyE, kB (whileCondK true)
      refine ⟨_, by simp only [stepFn, hctl, hkont, kC, applyKont, Value.truthy, withKont]; rfl, ?_⟩
      exact ⟨hheap, hsize, hgetD0, Or.inl ⟨hstack, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by simp [kB]⟩)))⟩⟩
    · -- P3: eval bodyE → eval (var x), kR (send)
      refine ⟨_, by simp only [stepFn, hctl, bodyE, hkont, kB, evalExpr, withKont]; rfl, ?_⟩
      exact ⟨hheap, hsize, hgetD0, Or.inl ⟨hstack, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by simp [kR]⟩))))⟩⟩
    · -- P4: eval (var x) → value (ref inst), kR (getLocal)
      refine ⟨_, by
        simp only [stepFn, hctl, evalExpr, withCtl]
        rw [getLocal_x m hstack hgetD0], ?_⟩
      exact ⟨hheap, hsize, hgetD0, Or.inl ⟨hstack, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hkont⟩)))))⟩⟩
    · -- P5: value (ref inst), kR → DISPATCH (push activation)
      refine ⟨_, dispatch_step m hctl hkont hheap, ?_⟩
      refine ⟨?_, ?_, ?_, Or.inr ⟨m.frames.size, ?_, Or.inl ⟨rfl, rfl⟩⟩⟩
      · simp [mkNext, hheap]
      · simp [mkNext, Array.size_push]
      · simp only [mkNext]; rw [getD0_push m.frames mF hsize]; exact hgetD0
      · simp [mkNext, hstack]
    · -- P8': value (int 0), kB → eval tru, kC (whileBodyK)
      refine ⟨_, by simp only [stepFn, hctl, hkont, kB, applyKont, withKont]; rfl, ?_⟩
      exact ⟨hheap, hsize, hgetD0, Or.inl ⟨hstack, Or.inr (Or.inl ⟨rfl, by simp [kC]⟩)⟩⟩
  · -- stack = [fid, 0] (mid-method)
    rcases hc with ⟨hctl, hkont⟩ | ⟨hctl, hkont⟩
    · -- P6: eval (int 0) → value (int 0), frameK still pending
      refine ⟨_, by simp only [stepFn, hctl, evalExpr, withCtl]; rfl, ?_⟩
      exact ⟨hheap, hsize, hgetD0, Or.inr ⟨fid, hstack, Or.inr ⟨rfl, hkont⟩⟩⟩
    · -- P7: value (int 0), frameK fid → pop activation stack → value (int 0), kB
      refine ⟨_, by simp only [stepFn, hctl, hkont, applyKont, withCtl]; rfl, ?_⟩
      refine ⟨hheap, hsize, hgetD0, Or.inl ⟨by simp [hstack], Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))⟩⟩

/-- Consecution. -/
theorem cons_J : ∀ m m', J m → SmallStep m m' → J m' := by
  intro m m' hJ hstep
  obtain ⟨m'', hstep'', hJ''⟩ := stepJ m hJ
  rw [SmallStep, hstep''] at hstep
  injection hstep with h; subst h; exact hJ''

/-- Safety (progress): a `J`-config steps, so it is not one step from a
    type-family `uncaught`. -/
theorem safe_J : ∀ m, J m → ¬ aboutToTypeStick m := by
  intro m hJ
  obtain ⟨m', hstep, _⟩ := stepJ m hJ
  unfold aboutToTypeStick typeStuck
  rw [hstep]; exact not_false

/-! ### The theorem -/

/-- The concrete loop-entry config: at the loop head, class `A` + instance in
    `Hstar`, `x` bound in the single toplevel frame `F0`. -/
def m0 : Machine :=
  { ctl := .eval prog, kont := [], stack := [0], frames := #[F0], heap := Hstar }

theorem init_J : J m0 := by
  refine ⟨rfl, by decide, rfl, Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩

/-- **The T5 loop is type-safe.** `while true do x.m end`, entered with `A`
    defined and `x` an `A`-instance, never reaches a type-family `uncaught` — for
    unbounded fuel — proved by an inductive object-model invariant (Direction B),
    NOT by running the program. Axiom-clean. -/
theorem t5_loop_type_safe :
    ∀ r, ReachableResult m0 r → ¬ typeStuck r :=
  invariant_sound_from J init_J cons_J safe_J

end T5Loop
end Proof
end RubyCore
