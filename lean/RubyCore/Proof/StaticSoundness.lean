import RubyCore.Proof.BuiltinConformance
import RubyCore.Proof.HeapFacts
import RubyCore.Types.Core

/-!
# P0 — static soundness on the fully-typed fragment

`docs/semantics/static-soundness-poc.md`. The claim:

    check P = .accept  →  no reachable outcome is `typeStuck`

proved by handing `Proof.invariant_sound_from` an invariant built from the
checker of `Types/Core.lean`. Nothing here re-derives reachability: the
metatheorem harness (`Proof/TypeSafety.lean:157`) is bad-state-agnostic and
already proved, and this is the first target to reuse `typeStuck`
*unmodified* — no bad-state swap at all.

Note the conclusion is `typeStuck`, not `sorbetStuck`: in a fully-typed
fragment a sig check cannot fire, so the blame carve-out of
`Proof/SorbetSafety.lean` is unnecessary and the *strong* property is what
gets proved (doc §2.1).

## Shape of the invariant

    Inv m  ≡  TableOk m.heap ∧ ∃ Γ Γs, FramesOk m.frames m.stack (Γ :: Γs) ∧
                                       CtlOk Γ Γs m

`CtlOk`/`KontOk` play the role the doc §4 assigns to `InFragment`: they simply
have **no constructor** for the machine shapes outside the fragment, so the
`stepFn` case analysis discharges those branches by contradiction rather than
by typing work. That is the whole tractability argument, and it is why this
file does not need a separate fragment predicate.
-/

namespace RubyCore
namespace Proof
namespace Static

open Interp
open RubyCore.Types

-- The boot-heap `rfl`s of `tableOk_initHeap` walk the whole method table.
set_option maxRecDepth 100000

/-! ## 1. Values and locals -/

/-- The type of a value, where P0 has one. `.ref`/`.flt`/`.sym` have none — the
    fragment allocates no objects, so they never arise. -/
def valueTy? : Value → Option Ty
  | .int _ => some .int
  | .bool _ => some .bool
  | .nil => some .nilT
  | _ => none

def ValueTy (v : Value) (τ : Ty) : Prop := valueTy? v = some τ

/-- The frame currently executing. -/
def curFid (m : Machine) : FrameId := m.stack.headD 0

/-- The frame currently executing. -/
def curFrame (m : Machine) : Frame := m.frames.getD (curFid m) default

/-- A frame's binding for `x`, or `nil` — the value `getLocal` reads once the
    `captured` chain is known empty. -/
def localOf (f : Frame) (x : String) : Value :=
  match f.locals.find? (·.1 == x) with
  | some (_, v) => v
  | none => .nil

/-- One activation conforms to one environment. `captured = none` is what makes
    the frame *self-contained*: `getLocal`/`setLocal` otherwise walk into
    enclosing scopes (`Machine.lean:322–352`) and nothing about them reduces. -/
def FrameConforms (Γ : Env) (f : Frame) : Prop :=
  f.captured = none ∧ ∀ x τ, envGet? Γ x = some τ → ValueTy (localOf f x) τ

/-- **Per-frame conformance down the activation stack**, innermost first.

    The `∀ g ∈ fids, g < fid` clause buys frame-id **distinctness**, which is
    what makes `setLocal` provably local: it writes to `curFid` only, so every
    other frame on the stack is untouched. Distinctness is true of the real
    machine — a pushed id is `frames.size`, hence strictly greater than every id
    already on the stack — but it has to be *carried*, not rediscovered, so it
    rides here rather than being a side theorem (L91 predicted this clause).

    Equal lengths are forced by the `_, _ => False` arm, which is why this
    subsumes P0a's `stack ≠ []`. -/
def FramesOk (frames : Array Frame) : List FrameId → List Env → Prop
  | [], [] => True
  | fid :: fids, Γ :: Γs =>
      fid < frames.size ∧ (∀ g ∈ fids, g < fid) ∧
      FrameConforms Γ (frames.getD fid default) ∧ FramesOk frames fids Γs
  | _, _ => False

/-- What `getLocal`/`setLocal` need, derived from the head of `FramesOk`. Kept as
    its own definition so the local-access lemmas stay readable. -/
def FrameOk (m : Machine) : Prop :=
  m.stack ≠ [] ∧ curFid m < m.frames.size ∧ (curFrame m).captured = none

/-- Every variable the environment types holds a value of that type. Stated
    against `m.getLocal` — what the interpreter actually reads. -/
def LocalsOk (Γ : Env) (m : Machine) : Prop :=
  ∀ x τ, envGet? Γ x = some τ → ValueTy (m.getLocal x) τ

/-! ### 1.1 Two array facts, and local access on the current frame -/

theorem getD_set!_ne (a : Array Frame) (i j : Nat) (f : Frame) (h : j ≠ i) :
    (a.set! i f).getD j default = a.getD j default := by
  have hsz : (a.set! i f).size = a.size := by simp [Array.set!]
  by_cases hj : j < a.size
  · simp only [Array.getD]
    rw [dif_pos (hsz ▸ hj), dif_pos hj]
    exact Array.getElem_setIfInBounds_ne hj (Ne.symm h)
  · simp only [Array.getD]
    rw [dif_neg (hsz ▸ hj), dif_neg hj]

theorem getD_set!_self (a : Array Frame) (i : Nat) (f : Frame) (h : i < a.size) :
    (a.set! i f).getD i default = f := by
  simp [Array.getD, h]

theorem getD_push_lt (a : Array Frame) (j : Nat) (f : Frame) (h : j < a.size) :
    (a.push f).getD j default = a.getD j default := by
  simp only [Array.getD]
  rw [dif_pos h, dif_pos (show j < (a.push f).size by simp [Array.size_push]; omega)]
  exact Array.getElem_push_lt h

theorem getLocal_cur {m : Machine} (hf : FrameOk m) (x : String) :
    m.getLocal x = localOf (curFrame m) x := by
  obtain ⟨_, _, hc⟩ := hf
  simp only [curFrame, curFid] at hc
  unfold Machine.getLocal
  unfold Machine.getLocal.go
  simp only [localOf, curFrame, curFid, hc]
  rfl

-- `find?_filter_ne` now lives in `Proof/HeapFacts.lean` — the `defineMethod`
-- chain needs it too, and one copy is better than two.
open RubyCore.Proof in

/-- With no captured chain, `setLocal`'s owner search returns the start frame on
    both branches, whichever frame that is. -/
theorem setLocal_owner_start {m : Machine} {start : FrameId}
    (hc : (m.frames.getD start default).captured = none) (x : String) (fuel : Nat) :
    Machine.setLocal.owner m x start start (fuel + 1) = start := by
  unfold Machine.setLocal.owner
  simp only [hc]
  split <;> rfl

/-- `setLocal` is a `set!` at `curFid`, and nothing else. -/
theorem setLocal_frames {m : Machine} (hf : FrameOk m) (x : String) (v : Value) :
    (m.setLocal x v).frames =
      m.frames.set! (curFid m)
        { curFrame m with locals := (x, v) :: (curFrame m).locals.filter (·.1 != x) } := by
  obtain ⟨_, _, hc⟩ := hf
  simp only [curFrame, curFid] at hc ⊢
  unfold Machine.setLocal
  simp only [setLocal_owner_start hc x m.frames.size]

theorem setLocal_stack {m : Machine} (x : String) (v : Value) :
    (m.setLocal x v).stack = m.stack := by simp [Machine.setLocal]

theorem curFid_setLocal {m : Machine} (x : String) (v : Value) :
    curFid (m.setLocal x v) = curFid m := by simp [Machine.setLocal, curFid]

theorem FrameOk.setLocal {m : Machine} (hf : FrameOk m) (x : String) (v : Value) :
    FrameOk (m.setLocal x v) := by
  have hfr := setLocal_frames hf x v
  obtain ⟨hne, hlt, hc⟩ := hf
  refine ⟨by rw [setLocal_stack]; exact hne, ?_, ?_⟩
  · rw [curFid_setLocal, hfr]; simpa [Array.set!] using hlt
  · rw [curFrame, curFid_setLocal, hfr, getD_set!_self _ _ _ (by simpa using hlt)]
    exact hc

/-- The one substantive fact about locals: assignment updates exactly `x`. -/
theorem localOf_setLocal {m : Machine} (hf : FrameOk m) (x y : String) (v : Value) :
    localOf (curFrame (m.setLocal x v)) y =
      if y = x then v else localOf (curFrame m) y := by
  have hlt := hf.2.1
  rw [curFrame, curFid_setLocal, setLocal_frames hf x v,
    getD_set!_self _ _ _ (by simpa using hlt)]
  by_cases hyx : y = x
  · subst hyx; simp [localOf, List.find?]
  · have hne : ((x, v).1 == y) = false := by
      simp only [beq_eq_false_iff_ne]; exact fun h => hyx h.symm
    simp only [localOf, List.find?, hne, if_neg hyx]
    rw [find?_filter_ne _ hyx]

theorem getLocal_setLocal {m : Machine} (hf : FrameOk m) (x y : String) (v : Value) :
    (m.setLocal x v).getLocal y = if y = x then v else m.getLocal y := by
  rw [getLocal_cur (FrameOk.setLocal hf x v) y, getLocal_cur hf y,
    localOf_setLocal hf x y v]

/-! ### 1.2 `FramesOk` implies what the old invariant asserted -/

theorem FramesOk.frameOk {m : Machine} {Γ : Env} {Γs : List Env}
    (h : FramesOk m.frames m.stack (Γ :: Γs)) : FrameOk m := by
  cases hst : m.stack with
  | nil => rw [hst] at h; exact absurd h (by simp [FramesOk])
  | cons fid fids =>
    rw [hst] at h
    obtain ⟨hlt, _, ⟨hc, _⟩, _⟩ := h
    refine ⟨by rw [hst]; simp, ?_, ?_⟩
    · simpa [curFid, hst] using hlt
    · simpa [curFrame, curFid, hst] using hc

/-- Popping the innermost activation: a suffix of a conforming stack conforms. -/
theorem FramesOk.tail {frames : Array Frame} {fids : List FrameId} {Γ : Env}
    {Γs : List Env} (h : FramesOk frames fids (Γ :: Γs)) :
    FramesOk frames fids.tail Γs := by
  cases fids with
  | nil => exact absurd h (by simp [FramesOk])
  | cons fid rest => exact h.2.2.2

theorem FramesOk.localsOk {m : Machine} {Γ : Env} {Γs : List Env}
    (h : FramesOk m.frames m.stack (Γ :: Γs)) : LocalsOk Γ m := by
  intro x τ hg
  rw [getLocal_cur h.frameOk x]
  cases hst : m.stack with
  | nil => rw [hst] at h; exact absurd h (by simp [FramesOk])
  | cons fid fids =>
    have hc : FrameConforms Γ (m.frames.getD fid default) := by
      rw [hst] at h; exact h.2.2.1
    have : curFrame m = m.frames.getD fid default := by
      simp [curFrame, curFid, hst]
    rw [this]
    exact hc.2 x τ hg

/-! ### 1.3 Environment update, and its agreement with `setLocal` -/

theorem envGet?_nil (y : String) : envGet? ([] : Env) y = none := rfl

theorem envGet?_cons (z : String) (σ : Ty) (Γ : Env) (y : String) :
    envGet? ((z, σ) :: Γ) y = if z = y then some σ else envGet? Γ y := by
  by_cases h : z = y
  · subst h; simp [envGet?, List.find?]
  · have hb : (z == y) = false := by simpa using h
    simp [envGet?, List.find?, hb, h]

theorem envSet_nil (x : String) (τ : Ty) : envSet [] x τ = [(x, τ)] := rfl

theorem envSet_cons (z : String) (σ : Ty) (Γ : Env) (x : String) (τ : Ty) :
    envSet ((z, σ) :: Γ) x τ =
      if z = x then (x, τ) :: Γ else (z, σ) :: envSet Γ x τ := by
  simp only [envSet, beq_iff_eq]

theorem envGet?_set (Γ : Env) (x y : String) (τ : Ty) :
    envGet? (envSet Γ x τ) y = if y = x then some τ else envGet? Γ y := by
  induction Γ with
  | nil =>
    rw [envSet_nil, envGet?_cons, envGet?_nil]
    by_cases h : y = x
    · subst h; simp
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]
  | cons a Γ ih =>
    obtain ⟨z, σ⟩ := a
    rw [envSet_cons]
    by_cases hzx : z = x
    · subst hzx
      rw [if_pos rfl, envGet?_cons, envGet?_cons]
      by_cases hyz : y = z
      · subst hyz; simp
      · rw [if_neg hyz, if_neg (fun hh => hyz hh.symm), if_neg (fun hh => hyz hh.symm)]
    · rw [if_neg hzx, envGet?_cons, envGet?_cons, ih]
      by_cases hzy : z = y
      · subst hzy
        rw [if_pos rfl, if_pos rfl, if_neg (fun hh => hzx hh)]
      · rw [if_neg hzy, if_neg hzy]

/-! ### 1.4 `FramesOk` under the fragment's updates -/

/-- Conformance only reads the frames the stack names, so an array change that
    leaves those alone transports it. -/
theorem FramesOk.frames_congr {a b : Array Frame} :
    ∀ {fids : List FrameId} {Γs : List Env}, FramesOk a fids Γs →
      (∀ g ∈ fids, g < b.size) → (∀ g ∈ fids, b.getD g default = a.getD g default) →
      FramesOk b fids Γs
  | [], [], h, _, _ => h
  | fid :: fids, Γ :: Γs, h, hb, heq => by
    obtain ⟨_, hlt2, hcf, hrest⟩ := h
    exact ⟨hb fid (by simp), hlt2,
      by rw [heq fid (by simp)]; exact hcf,
      FramesOk.frames_congr hrest (fun g hg => hb g (by simp [hg]))
        (fun g hg => heq g (by simp [hg]))⟩
  | [], _ :: _, h, _, _ => absurd h (by simp [FramesOk])
  | _ :: _, [], h, _, _ => absurd h (by simp [FramesOk])

theorem FramesOk.setLocal {m : Machine} {Γ : Env} {Γs : List Env} {x : String}
    {τ : Ty} {v : Value} (hfs : FramesOk m.frames m.stack (Γ :: Γs))
    (hv : ValueTy v τ) :
    FramesOk (m.setLocal x v).frames (m.setLocal x v).stack (envSet Γ x τ :: Γs) := by
  have hf := hfs.frameOk
  have hlt := hf.2.1
  rw [setLocal_stack]
  cases hst : m.stack with
  | nil => rw [hst] at hfs; exact absurd hfs (by simp [FramesOk])
  | cons fid fids =>
    have hcur : curFid m = fid := by simp [curFid, hst]
    rw [hst] at hfs
    obtain ⟨hfl, hgt, hcf, hrest⟩ := hfs
    have hsz : (m.setLocal x v).frames.size = m.frames.size := by
      rw [setLocal_frames hf x v]; simp [Array.set!]
    refine ⟨by rw [hsz]; exact hfl, hgt, ⟨?_, ?_⟩, ?_⟩
    -- the head frame: captured survives, and the binding is updated at `x` only
    · have := (FrameOk.setLocal hf x v).2.2
      simpa [curFrame, curFid_setLocal, hcur] using this
    · intro y σ hg
      have hy : localOf ((m.setLocal x v).frames.getD fid default) y
          = localOf (curFrame (m.setLocal x v)) y := by
        simp [curFrame, curFid_setLocal, hcur]
      rw [envGet?_set] at hg
      rw [hy, localOf_setLocal hf x y v]
      by_cases hyx : y = x
      · rw [if_pos hyx] at hg ⊢
        rw [Option.some.injEq] at hg; subst hg; exact hv
      · rw [if_neg hyx] at hg ⊢
        have := hcf.2 y σ hg
        simpa [curFrame, hcur] using this
    -- the frames below: every id there is `< fid = curFid`, so `set!` missed them
    · refine FramesOk.frames_congr hrest (fun g hg => by rw [hsz]; exact Nat.lt_trans (hgt g hg) hfl)
        (fun g hg => ?_)
      rw [setLocal_frames hf x v, hcur]
      exact getD_set!_ne _ _ _ _ (Nat.ne_of_lt (hgt g hg))

/-! ## 2. Typing the machine

`KontOk Γ τ k` reads: *the in-flight value has type `τ`, the environment is
`Γ`, and `k` is a well-typed continuation.* There is one constructor per
admitted `Kont` — five out of the machine's 48 (`Machine.lean:140`) — and the
absence of the other 43 is what makes preservation's case analysis collapse.
-/

/-- A `while` whose condition and body are both **environment-stable** at `Γ`.
    The loop re-enters the condition with whatever the body leaves, so without
    stability there is no single `Γ` to index the two loop konts by. -/
def LoopOk (Γ : Env) (c body : Expr) : Prop :=
  (∃ τc, infer Γ c = some (τc, Γ)) ∧ (∃ τb, infer Γ body = some (τb, Γ))

/-- `KontOk Γs τ k` reads: *the in-flight value has type `τ`, the environment
    **stack** is `Γs` (innermost first), and `k` is a well-typed continuation.*

    The stack replaces P0's single environment because a method activation has
    its own locals: `frameK` — the kont `enterUserMethod` pushes
    (`Interp.lean:573`) and `applyKont` pops (`Interp.lean:2206`) — is exactly
    the marker at which one environment goes out of scope. Every other
    constructor operates on the head and passes the tail through untouched. -/
inductive KontOk : List Env → Ty → List Kont → Prop where
  /-- Empty stack: the in-flight value is the program's result. -/
  | nil {Γs τ} : KontOk Γs τ []
  /-- `seqK []` yields the in-flight value unchanged (`Interp.lean:1957`). -/
  | seqNil {Γ Γs τ k} : KontOk (Γ :: Γs) τ k → KontOk (Γ :: Γs) τ (.seqK [] :: k)
  /-- `seqK (e :: es)` discards the in-flight value and runs the rest. -/
  | seqCons {Γ Γs τ e es τ' Γ' k} :
      inferSeq Γ (e :: es) = some (τ', Γ') → KontOk (Γ' :: Γs) τ' k →
      KontOk (Γ :: Γs) τ (.seqK (e :: es) :: k)
  /-- Assignment binds `x` at the in-flight type and re-yields the value. -/
  | asgn {Γ Γs τ x k} :
      KontOk (envSet Γ x τ :: Γs) τ k → KontOk (Γ :: Γs) τ (.asgnK .lvar x :: k)
  /-- The in-flight value is the condition; either branch may run next, so the
      join must be the one `inferIf` computed. -/
  | ifK {Γ Γs τ t els τ' Γ' k} :
      inferIf Γ t els = some (τ', Γ') → KontOk (Γ' :: Γs) τ' k →
      KontOk (Γ :: Γs) τ (.ifK t els :: k)
  | whileCond {Γ Γs τ c body k} :
      LoopOk Γ c body → KontOk (Γ :: Γs) .nilT k →
      KontOk (Γ :: Γs) τ (.whileCondK c body :: k)
  | whileBody {Γ Γs τ c body k} :
      LoopOk Γ c body → KontOk (Γ :: Γs) .nilT k →
      KontOk (Γ :: Γs) τ (.whileBodyK c body :: k)
  /-- The in-flight value is the **receiver** of a binary builtin send; the
      argument expression runs next. The site is `.explicit` because `evalExpr`
      picks it syntactically and `infer` rejects `self` in receiver position. -/
  | recvK {Γ Γs τ mname arg τp τret Γ₂ k} :
      builtinSig τ mname = some ([τp], τret) →
      infer Γ arg = some (τp, Γ₂) →
      KontOk (Γ₂ :: Γs) τret k →
      KontOk (Γ :: Γs) τ (.recvK mname [arg] .none .explicit :: k)
  /-- The in-flight value is the **argument**; the receiver is already a value
      carried by the kont, so its type is pinned by `ValueTy` rather than by
      `infer`. -/
  | argsK {Γ Γs τ mname recv τr τret k} :
      ValueTy recv τr →
      builtinSig τr mname = some ([τ], τret) →
      KontOk (Γ :: Γs) τret k →
      KontOk (Γ :: Γs) τ (.argsK recv .explicit mname [] [] .none :: k)
  /-- **Method return.** The in-flight value is the body's value; popping the
      activation (`Interp.lean:2206`) discards the callee's environment and
      resumes the caller's.

      Note the **two-deep** env stack `Γ :: Γ' :: Γs`. A one-deep version would
      be provable-looking and wrong: `KontOk.nil` accepts *any* stack including
      `[]`, so `KontOk (Γ :: []) τ (frameK :: [])` would be derivable, and
      popping it leaves a machine with no current environment for `CtlOk` to use.
      Requiring a caller environment to exist is what makes the pop total. -/
  | frameK {Γ Γ' Γs τ fid k} :
      KontOk (Γ' :: Γs) τ k → KontOk (Γ :: Γ' :: Γs) τ (.frameK fid :: k)

/-- The control component. `.jump` is excluded outright: `break`/`next`/`return`
    are not in the fragment, so no step can produce one. -/
def CtlOk (Γ : Env) (Γs : List Env) (m : Machine) : Prop :=
  match m.ctl with
  | .eval e => ∃ τ Γ', infer Γ e = some (τ, Γ') ∧ KontOk (Γ' :: Γs) τ m.kont
  | .value v => ∃ τ, ValueTy v τ ∧ KontOk (Γ :: Γs) τ m.kont
  | .jump _ => False

/-- Every `builtinSig` entry still resolves in this heap. A *heap* condition,
    so preservation must re-establish it — trivially here, since no step in the
    fragment writes the method table (the fragment has no `def` and no class
    reopening, `static-soundness-poc.md` §6). -/
def TableOk (h : Heap) : Prop :=
  IntBuiltinResolves h "+" "Integer#+" ∧
  IntBuiltinResolves h "-" "Integer#-" ∧
  IntBuiltinResolves h "*" "Integer#*"

/-- **`TableOk` survives a user `def`.** The obligation P1b's `def` case needs:
    `def` writes the method table (`Interp.lean:2615`), and `TableOk` is a heap
    condition, so it has to be re-established. The side condition is exactly what
    the fragment can check syntactically — a `def` may not shadow a tabulated
    builtin name. Note it holds for *any* target class `cls`, so reopening
    `Integer` itself is fine as long as the name differs. -/
theorem TableOk_defineMethod {h : Heap} {cls : ObjId} {name : String}
    {md : MethodDef} (ht : TableOk h)
    (h1 : ¬ (name = "+")) (h2 : ¬ (name = "-")) (h3 : ¬ (name = "*")) :
    TableOk (defineMethod h cls name md) :=
  ⟨IntBuiltinResolves_defineMethod ht.1 (fun hh => h1 hh.symm),
   IntBuiltinResolves_defineMethod ht.2.1 (fun hh => h2 hh.symm),
   IntBuiltinResolves_defineMethod ht.2.2 (fun hh => h3 hh.symm)⟩

/-- **The invariant** handed to `invariant_sound_from`. -/
def Inv (m : Machine) : Prop :=
  TableOk m.heap ∧ ∃ Γ Γs, FramesOk m.frames m.stack (Γ :: Γs) ∧ CtlOk Γ Γs m

/-! ### Inversions used by the send cases -/

theorem valueTy_int {v : Value} (h : ValueTy v .int) : ∃ a, v = .int a := by
  cases v <;> simp_all [ValueTy, valueTy?]

/-- The table is small and closed, so a successful lookup pins everything. -/
theorem builtinSig_inv {τr τp τret : Ty} {mname : String}
    (h : builtinSig τr mname = some ([τp], τret)) :
    τr = .int ∧ τp = .int ∧ τret = .int ∧
      (mname = "+" ∨ mname = "-" ∨ mname = "*") := by
  cases τr
  · simp only [builtinSig] at h
    split at h <;> simp_all <;> exact h.2.symm.trans h.1
  all_goals exact absurd h (by simp [builtinSig])

/-- `evalExpr` chooses the send site *syntactically* from the receiver
    expression (`Interp.lean:2582`); `infer` rejects `self`, so the site is
    always `.explicit` in the fragment. -/
theorem site_explicit {Γ : Env} {r : Expr} {x : Ty × Env} (h : infer Γ r = some x) :
    (match r with | .self' => SendSite.selfRecv | _ => SendSite.explicit) = .explicit := by
  cases r <;> try rfl
  exact absurd h (by simp [infer])

/-- Inversion for the send rule. Factored out of `step_ok` because the nested
    `split at` needs `next`-bound names that are unreadable inline. -/
theorem infer_send_inv {Γ : Env} {r arg : Expr} {mname : String} {τ : Ty} {Γ' : Env}
    (h : infer Γ (.send (some r) mname [arg] none) = some (τ, Γ')) :
    ∃ τr Γ₁ τp, infer Γ r = some (τr, Γ₁) ∧
      builtinSig τr mname = some ([τp], τ) ∧
      infer Γ₁ arg = some (τp, Γ') := by
  simp only [infer] at h
  split at h
  · next τr Γ₁ hr =>
    split at h
    · next τp τret hsg =>
      split at h
      · next τa Γ₂ ha =>
        split at h
        · next hτ =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨τr, Γ₁, τp, hr, hsg, hτ ▸ ha⟩
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)


/-! ### 2.2 `FramesOk` survives the fragment's frame-preserving updates

`ctl` and `kont` updates leave `frames` and `stack` alone, and `FramesOk` reads
nothing else — so it transports by `rfl` rather than by a congruence lemma. That
is the payoff of phrasing conformance over the array and the stack instead of
over the machine: P0a needed `FrameOk_congr` *and* `LocalsOk_congr`, and both are
now gone.
-/

/-! ### 2.3 Building `Inv` for the machines the fragment steps to -/

theorem inv_eval {m : Machine} {Γ : Env} {Γs : List Env} {e : Expr} {τ : Ty} {Γ' : Env}
    (hfs : FramesOk m.frames m.stack (Γ :: Γs)) (ht : TableOk m.heap)
    (hinf : infer Γ e = some (τ, Γ')) (hk : KontOk (Γ' :: Γs) τ m.kont) :
    Inv (withCtl m (.eval e)) :=
  ⟨ht, Γ, Γs, hfs, ⟨τ, Γ', hinf, hk⟩⟩

theorem inv_value {m : Machine} {Γ : Env} {Γs : List Env} {v : Value} {τ : Ty}
    (hfs : FramesOk m.frames m.stack (Γ :: Γs)) (ht : TableOk m.heap)
    (hv : ValueTy v τ) (hk : KontOk (Γ :: Γs) τ m.kont) :
    Inv (withCtl m (.value v)) :=
  ⟨ht, Γ, Γs, hfs, ⟨τ, hv, hk⟩⟩

theorem inv_push {m : Machine} {Γ : Env} {Γs : List Env} {e : Expr} {τ : Ty}
    {Γ' : Env} {k : Kont}
    (hfs : FramesOk m.frames m.stack (Γ :: Γs)) (ht : TableOk m.heap)
    (hinf : infer Γ e = some (τ, Γ')) (hk : KontOk (Γ' :: Γs) τ (k :: m.kont)) :
    Inv (withKont m (.eval e) k) :=
  ⟨ht, Γ, Γs, hfs, ⟨τ, Γ', hinf, hk⟩⟩

/-! ## 3. Progress and preservation, in one case analysis

`StepOk` bundles both obligations so the 48-way `Kont` split and the ~40-way
`Expr` split are each walked **once**: `.next` carries preservation, `.done` is
a legitimate halt, and every remaining `StepResult` — crucially `.uncaught` —
is `False`, which is exactly progress.
-/

def StepOk : StepResult → Prop
  | .next m' => Inv m'
  | .done _ _ => True
  | _ => False

theorem step_ok {m : Machine} (h : Inv m) : StepOk (stepFn m) := by
  obtain ⟨htab, Γ, Γs, hfs, hc⟩ := h
  have hf : FrameOk m := hfs.frameOk
  have hl : LocalsOk Γ m := hfs.localsOk
  unfold CtlOk at hc
  rcases hctl : m.ctl with e | v | j
  · -- ## control = eval e
    rw [hctl] at hc
    obtain ⟨τ, Γ', hinf, hk⟩ := hc
    simp only [stepFn, hctl]
    cases e <;> try (simp only [infer] at hinf; contradiction)
    case int n =>
      simp only [infer, Option.some.injEq, Prod.mk.injEq] at hinf
      obtain ⟨rfl, rfl⟩ := hinf
      exact inv_value hfs htab rfl hk
    case tru =>
      simp only [infer, Option.some.injEq, Prod.mk.injEq] at hinf
      obtain ⟨rfl, rfl⟩ := hinf
      exact inv_value hfs htab rfl hk
    case fls =>
      simp only [infer, Option.some.injEq, Prod.mk.injEq] at hinf
      obtain ⟨rfl, rfl⟩ := hinf
      exact inv_value hfs htab rfl hk
    case nil =>
      simp only [infer, Option.some.injEq, Prod.mk.injEq] at hinf
      obtain ⟨rfl, rfl⟩ := hinf
      exact inv_value hfs htab rfl hk
    case var k x =>
      cases k
      case lvar =>
        simp only [infer, Option.map_eq_some_iff] at hinf
        obtain ⟨σ, hg, heq⟩ := hinf
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact inv_value hfs htab (hl x _ hg) hk
      all_goals (simp only [infer] at hinf; contradiction)
    case vasgn k x rhs =>
      cases k
      case lvar =>
        simp only [infer] at hinf
        split at hinf
        · rename_i σ Γ₁ hrhs
          simp only [Option.some.injEq, Prod.mk.injEq] at hinf
          obtain ⟨rfl, rfl⟩ := hinf
          exact inv_push hfs htab hrhs (KontOk.asgn hk)
        · exact absurd hinf (by simp)
      all_goals (simp only [infer] at hinf; contradiction)
    case seq es =>
      simp only [infer] at hinf
      cases es with
      | nil =>
        simp only [inferSeq, Option.some.injEq, Prod.mk.injEq] at hinf
        obtain ⟨rfl, rfl⟩ := hinf
        exact inv_value hfs htab rfl hk
      | cons e₁ rest =>
        cases rest with
        | nil =>
          simp only [inferSeq] at hinf
          exact inv_eval hfs htab hinf hk
        | cons e₂ rest' =>
          simp only [inferSeq] at hinf
          split at hinf
          · rename_i σ Γ₁ h₁
            exact inv_push hfs htab h₁ (KontOk.seqCons hinf hk)
          · exact absurd hinf (by simp)
    case if' c t els =>
      simp only [infer] at hinf
      split at hinf
      · rename_i σ Γ₁ hcnd
        exact inv_push hfs htab hcnd (KontOk.ifK hinf hk)
      · exact absurd hinf (by simp)
    case while' c body =>
      simp only [infer] at hinf
      split at hinf
      · rename_i σ Γ₁ hcnd
        split at hinf
        · rename_i hΓ₁
          subst hΓ₁
          split at hinf
          · rename_i σb Γ₂ hbody
            split at hinf
            · rename_i hΓ₂
              subst hΓ₂
              simp only [Option.some.injEq, Prod.mk.injEq] at hinf
              obtain ⟨rfl, rfl⟩ := hinf
              exact inv_push hfs htab hcnd
                (KontOk.whileCond ⟨⟨σ, hcnd⟩, ⟨σb, hbody⟩⟩ hk)
            · exact absurd hinf (by simp)
          · exact absurd hinf (by simp)
        · exact absurd hinf (by simp)
      · exact absurd hinf (by simp)
    case send recv mname args blk =>
      cases recv with
      | none => exact absurd hinf (by simp [infer])
      | some r =>
        cases args with
        | nil => exact absurd hinf (by simp [infer])
        | cons arg extra =>
          cases extra with
          | cons _ _ => exact absurd hinf (by simp [infer])
          | nil =>
            cases blk with
            | some b => exact absurd hinf (by simp [infer])
            | none =>
              obtain ⟨τr, Γ₁, τp, hr, hsg, ha⟩ := infer_send_inv hinf
              -- `evalExpr` picks the send site by matching on the receiver
              -- *expression*, and that match will not rewrite under `rw`, so
              -- force it to compute. Every branch but `self` is `.explicit`,
              -- and `infer` rejects `self`.
              simp only [evalExpr]
              cases r <;>
                try exact inv_push hfs htab hr (KontOk.recvK hsg ha hk)
              exact absurd hr (by simp [infer])
  · -- ## control = value v
    rw [hctl] at hc
    obtain ⟨τ, hv, hk⟩ := hc
    simp only [stepFn, hctl]
    unfold applyKont
    generalize hK : m.kont = K at hk ⊢
    cases hk with
    | nil => trivial
    | @seqNil Γ Γs τ k hk' =>
      exact inv_value hfs htab hv hk'
    | @seqCons Γ Γs τ e₁ es τ' Γ' k hseq hk' =>
      cases es with
      | nil =>
        simp only [inferSeq] at hseq
        exact inv_push hfs htab hseq (KontOk.seqNil hk')
      | cons e₂ es' =>
        simp only [inferSeq] at hseq
        split at hseq
        · rename_i σ Γ₁ h₁
          exact inv_push hfs htab h₁ (KontOk.seqCons hseq hk')
        · exact absurd hseq (by simp)
    | @asgn Γ Γs τ x k hk' =>
      exact ⟨htab, envSet Γ x τ, Γs, FramesOk.setLocal hfs hv, ⟨τ, hv, hk'⟩⟩
    | @ifK Γ Γs τ t els τ' Γ' k hif hk' =>
      cases els with
      | some e₂ =>
        simp only [inferIf] at hif
        split at hif
        · rename_i τt Γt τe Γe ht he
          split at hif
          · rename_i hagree
            obtain ⟨rfl, rfl⟩ := hagree
            simp only [Option.some.injEq, Prod.mk.injEq] at hif
            obtain ⟨rfl, rfl⟩ := hif
            by_cases hb : v.truthy
            · simp only [hb, if_true]; exact inv_eval hfs htab ht hk'
            · simp only [hb]; exact inv_eval hfs htab he hk'
          · exact absurd hif (by simp)
        · exact absurd hif (by simp)
      | none =>
        simp only [inferIf] at hif
        split at hif
        · rename_i τt Γt ht
          split at hif
          · rename_i hnil
            obtain ⟨rfl, rfl⟩ := hnil
            simp only [Option.some.injEq, Prod.mk.injEq] at hif
            obtain ⟨rfl, rfl⟩ := hif
            by_cases hb : v.truthy
            · simp only [hb, if_true]; exact inv_eval hfs htab ht hk'
            · simp only [hb]; exact inv_value hfs htab rfl hk'
          · exact absurd hif (by simp)
        · exact absurd hif (by simp)
    | @whileCond Γ Γs τ c body k hloop hk' =>
      obtain ⟨⟨σc, hcnd⟩, ⟨σb, hbody⟩⟩ := hloop
      by_cases hb : v.truthy
      · simp only [hb, if_true]
        exact inv_push hfs htab hbody (KontOk.whileBody ⟨⟨σc, hcnd⟩, ⟨σb, hbody⟩⟩ hk')
      · simp only [hb]
        exact inv_value hfs htab rfl hk'
    | @whileBody Γ Γs τ c body k hloop hk' =>
      obtain ⟨⟨σc, hcnd⟩, ⟨σb, hbody⟩⟩ := hloop
      exact inv_push hfs htab hcnd (KontOk.whileCond ⟨⟨σc, hcnd⟩, ⟨σb, hbody⟩⟩ hk')
    | @frameK Γ Γ' Γs τ fid k hk' =>
      -- The activation pops: `frames` is untouched, `stack` loses its head, and
      -- the caller's environment — carried all along by `FramesOk` — becomes
      -- current again. This is the case L91 could not close.
      exact ⟨htab, Γ', Γs, hfs.tail, ⟨τ, hv, hk'⟩⟩
    | @recvK Γ Γs τ mname arg τp τret Γ₂ k hsg ha hk' =>
      have hsp : ∀ e, arg ≠ .splat e := by
        rintro e rfl; exact absurd ha (by simp [infer])
      have hkw : ∀ es, arg ≠ .kwargs es := by
        rintro es rfl; exact absurd ha (by simp [infer])
      have hfw : arg ≠ .fwd := by
        rintro rfl; exact absurd ha (by simp [infer])
      dsimp only
      rw [startArgs_plain hsp hkw hfw]
      exact inv_push hfs htab ha (KontOk.argsK hv hsg hk')
    | @argsK Γ Γs τ mname recv τr τret k hrv hsg hk' =>
      obtain ⟨rfl, rfl, rfl, hname⟩ := builtinSig_inv hsg
      obtain ⟨a, rfl⟩ := valueTy_int hrv
      obtain ⟨b, rfl⟩ := valueTy_int hv
      dsimp only
      simp only [List.nil_append]
      rcases hname with rfl | rfl | rfl
      · rw [int_add_dispatch (m := { m with kont := k }) htab.1]; exact inv_value hfs htab rfl hk'
      · rw [int_sub_dispatch (m := { m with kont := k }) htab.2.1]; exact inv_value hfs htab rfl hk'
      · rw [int_mul_dispatch (m := { m with kont := k }) htab.2.2]; exact inv_value hfs htab rfl hk'
  · -- ## control = jump: excluded by `CtlOk`
    rw [hctl] at hc
    exact hc.elim

/-! ## 4. The three obligations, and the theorem -/

/-- Preservation. -/
theorem consecution (m m' : Machine) (h : Inv m) (hs : SmallStep m m') : Inv m' := by
  have hok := step_ok h
  unfold SmallStep at hs
  rw [hs] at hok
  exact hok

/-- Progress: a machine satisfying `Inv` is never one step from a type error.
    Every `StepResult` other than `.next`/`.done` is `False` under `StepOk`, so
    `.uncaught` in particular is unreachable. -/
theorem safety (m : Machine) (h : Inv m) : ¬ aboutToTypeStick m := by
  intro hbad
  have hok := step_ok h
  unfold aboutToTypeStick typeStuck at hbad
  cases hr : stepFn m with
  | next m' => rw [hr] at hbad; exact hbad
  | done v m' => rw [hr] at hbad; exact hbad
  | uncaught exc m' => rw [hr] at hok; exact hok
  | unsupported r => rw [hr] at hbad; exact hbad
  | stuck msg => rw [hr] at hbad; exact hbad

/-- The boot heap satisfies the table condition — **by `rfl`**, which is what
    keeps `check_sound` unconditional. Were this only reachable by
    `native_decide` the headline theorem would inherit `ofReduceBool`; L73's
    reducibility discipline is what makes it come out this way. -/
theorem tableOk_initHeap : TableOk Boot.initHeap :=
  ⟨⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- Initiation, for the machine `Machine.init` builds. -/
theorem initiation {p : Expr} (h : check p = .accept) : Inv (Machine.init p) := by
  refine ⟨tableOk_initHeap, [], [], ?_, ?_⟩
  · show FramesOk (Machine.init p).frames (Machine.init p).stack ([] :: [])
    simp [Machine.init, Machine.initOn, FramesOk, FrameConforms, envGet?]
  · unfold check at h
    show CtlOk [] [] (Machine.init p)
    unfold CtlOk
    split at h
    · rename_i r hr
      obtain ⟨τ, Γ'⟩ := r
      exact ⟨τ, Γ', hr, KontOk.nil⟩
    · exact absurd h (by split <;> simp)

/-- **Static soundness, from any machine satisfying the invariant.** Stated this
    way so that P1's prelude-booted start (`Prelude.initWithPrelude`, the
    starting configuration `SorbetSafety.lean:100` insists on) is an instance
    rather than a restatement. -/
theorem sound_from {m₀ : Machine} (h : Inv m₀) :
    ∀ r, ReachableResult m₀ r → ¬ typeStuck r :=
  invariant_sound_from Inv h consecution safety

/-- **The POC theorem.** `check` accepts ⇒ no reachable outcome is a type
    error. Unconditional: no rely condition, no assumed hypothesis. -/
theorem check_sound {p : Expr} (h : check p = .accept) :
    ∀ r, ReachableResult (Machine.init p) r → ¬ typeStuck r :=
  sound_from (initiation h)

/-! ## 5. Worked examples

`decide` runs the checker; the theorem then applies to the program. -/

/-- `x = 1; if true then x else 0 end` -/
def egIf : Expr :=
  .seq [ .vasgn .lvar "x" (.int 1),
         .if' .tru (.var .lvar "x") (some (.int 0)) ]

example : check egIf = .accept := by
  simp [check, egIf, infer, inferSeq, inferIf, envSet, envGet?]

theorem egIf_safe : ∀ r, ReachableResult (Machine.init egIf) r → ¬ typeStuck r :=
  check_sound (by simp [check, egIf, infer, inferSeq, inferIf, envSet, envGet?])

/-- `x = 0; while true do x = 1 end` — diverges, which safety permits: the
    property is *never type-stuck*, not *terminates*. -/
def egLoop : Expr :=
  .seq [ .vasgn .lvar "x" (.int 0),
         .while' .tru (.vasgn .lvar "x" (.int 1)) ]

example : check egLoop = .accept := by
  simp [check, egLoop, infer, inferSeq, envSet]

theorem egLoop_safe : ∀ r, ReachableResult (Machine.init egLoop) r → ¬ typeStuck r :=
  check_sound (by simp [check, egLoop, infer, inferSeq, envSet])

/-- `(x + 1) * 2` with `x` a local — the P0b program shape. -/
def egArith : Expr :=
  .seq [ .vasgn .lvar "x" (.int 3),
         .send (some (.send (some (.var .lvar "x")) "+" [.int 1] none))
               "*" [.int 2] none ]

example : check egArith = .accept := by
  simp [check, egArith, infer, inferSeq, builtinSig, envSet, envGet?]

theorem egArith_safe :
    ∀ r, ReachableResult (Machine.init egArith) r → ¬ typeStuck r :=
  check_sound (by simp [check, egArith, infer, inferSeq, builtinSig, envSet, envGet?])

/-- A branch-type disagreement the fragment cannot join: `unknown`, not
    `reject`. `illTyped` has no opinion about `if` arms — it only refutes calls
    the builtin table refutes — so the absence of a union type shows up as
    incompleteness rather than as a claim about the program.

    The verdict examples that *do* exercise `reject` live next to the checker
    in `Types/Core.lean`; only the safety-bearing ones belong here. -/
example : check (.if' .tru (.int 1) (some .nil)) = .unknown := by
  simp [check, infer, inferIf, illTyped]

/-! ## 6. Axiom hygiene

The P0 exit criterion. Only the three standard Lean axioms — no `sorry`, and in
particular no `native_decide`/`ofReduceBool`, which is why §5's examples are
discharged by `simp` over the equation lemmas rather than by kernel reduction
(`infer` is well-founded-recursive, so `decide` does not reduce it). Same
baseline as `Proof/SorbetSafety.lean` [V]. -/

/-- info: 'RubyCore.Proof.Static.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms check_sound

end Static
end Proof
end RubyCore
