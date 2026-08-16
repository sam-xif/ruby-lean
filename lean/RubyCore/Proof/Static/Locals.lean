import RubyCore.Proof.BuiltinConformance
import RubyCore.Proof.HeapFacts
import RubyCore.Types.Core

/-!
# P0 static soundness, part 1 — values, frames and environments

Split out of `Proof/StaticSoundness.lean` (L136), which had reached 971 lines
against `PLAN.md` §4 norm 3's 1,000-line ceiling with F1 about to add to it. No
statement changed; the cut follows the file's own section numbering, and
`StaticSoundness.lean` still holds the theorem, so nothing downstream moved.

This part is §1: what it means for a *value* to have a type, for one activation
to conform to one environment, and for the whole activation stack to conform to a
stack of environments — plus the array and environment algebra those need.
-/

namespace RubyCore
namespace Proof
namespace Static

open Interp
open RubyCore.Types

-- The boot-heap `rfl`s of `tableOk_initHeap` walk the whole method table.
set_option maxRecDepth 100000

/-! ## 1. Values and locals -/

/-- **A receiver `invoke` dispatches uniformly.** The three receiver *shapes*
    `invoke` special-cases before it ever consults the resolved builtin
    (`Interp/Send.lean:33–92`) are all `.ref`s, and each is recognised by the
    object's payload: a `.proc` answers `call`/`()`/`[]`/`yield` by running its
    closure, a `.hsh` with a `prc` default answers `[]` by running that, and a
    `.cls` reaches `invokeMaybeNew` (or the `Math`/`Regexp` singleton arms, both of
    which are class objects). Everything else falls through to `invokeDispatch`,
    which is the path `ResolvesTo` describes.

    `eigen = none` is here for a different reason: dispatch resolves through
    `classOf`, which *is* the eigenclass when there is one, so an object with a
    singleton method would have its declarations read off a class other than the
    one the type names. Excluding it keeps the key and the dispatch class the same
    object — the same hypothesis `Proof/T5.lean`'s `dispatch_progress` carries as
    `heigen`.

    **This is a refusal, not an approximation.** A Proc, a Hash and a class object
    simply have no type in this rung; nothing unsound follows from a value having
    no type, only that no call on it can be checked.

    **`o < h.objs.size` is the producer rung's clause, and it repairs a latent
    defect rather than merely preparing for one.** `Heap.get` answers an
    out-of-bounds id with `default`, whose `klass` is `0`, whose `eigen` is `none`
    and whose payload is `.none` — so without this bound *every unallocated id is
    a plain receiver*, and L141's `.ref` arm gave it the type
    `.cls "BasicObject"`. Measured, not reasoned: at the boot heap
    `valueTy? h (.ref 40) = some (.cls "BasicObject")` with `h.objs.size = 40`.

    Nothing observes that today, because nothing constructs a class-typed value
    and every `baseDecls` row is at a ground type. What it *blocks* is the
    producer: `alloc` turns id `n` from `.cls "BasicObject"` into `.cls C`, which
    refutes `TypeAgree`'s first clause at the fresh id — so the transport
    condition is **false for any allocating step**, before any question of
    `ancestors_congr`'s fuel arises. With the bound, `ValueTy` implies the value
    is in bounds (`valueTy_ref_lt`), which is what lets the transport be
    relativized to ids the old heap actually had, and `alloc` satisfies *that*
    definitionally.

    The move is L141's own: a side condition the use site would have to derive
    goes into the judgement instead. -/
def plainRecv (h : Heap) (o : ObjId) : Bool :=
  o < h.objs.size && (h.get o).eigen.isNone &&
    (match (h.get o).payload with
     | .proc _ => false
     | .hsh _ => false
     | .cls _ => false
     | _ => true)

/-- The type of a value **in a heap**, where P0 has one. `.flt` has none — the
    fragment has no Float type — and a `.ref` has one exactly when it is a
    receiver `invoke` dispatches uniformly (`plainRecv`).

    **Heap-indexed since L137, and the `.ref` arm is the first arm to use it**
    (F1b/T2). L137's note said a nominal class type "can only say what class a
    `.ref` belongs to by consulting `classOf`/`className`, so the *judgement* has
    to be heap-relative before the *type language* can grow", and this is that
    prediction cashed: the arm is `className ∘ classOf`, and the cost of the
    threading lands in §1.5's congruence lemmas exactly where it was predicted to.

    `classOf` rather than `realClassOf` because dispatch uses `classOf`, and
    `plainRecv` makes them equal anyway — the type must name the class the method
    table is actually walked from, not the one `Object#class` reports. -/
def valueTy? (h : Heap) : Value → Option Ty
  | .int _ => some .int
  | .bool _ => some .bool
  | .nil => some .nilT
  -- `def` evaluates to the method name (`Interp.lean:2624`).
  | .sym _ => some .sym
  | .ref o => if plainRecv h o then some (.cls (className h (classOf h (.ref o)))) else none
  | _ => none

def ValueTy (h : Heap) (v : Value) (τ : Ty) : Prop := valueTy? h v = some τ

/-- Inversion at the `int` arm. Moved here from `Proof/Static/Konts.lean` in F1a:
    it is a fact about `ValueTy`, and `Proof/Static/Decls.lean` — which sits
    *below* `Konts.lean` now — needs it to build the base table's entries. -/
theorem valueTy_int {hp : Heap} {v : Value} (h : ValueTy hp v .int) : ∃ a, v = .int a := by
  cases v <;> simp_all [ValueTy, valueTy?]

/-- **Every value with a type is an immediate or a plain ref.** F1a's version of
    this said *immediate*, full stop, and that was what let
    `Proof/Static/Decls.lean`'s `entry_dispatch` discharge `invoke`'s
    receiver-shape special cases for free — the fragment's own poverty doing the
    work of a proof (`HANDOFF.md` §F1b).

    **F1b pays that bill, and it turns out to be a case rather than an argument.**
    The `.ref` case is admitted with `plainRecv`, which is precisely the negation
    of the three special shapes, so the special cases are still closed — but now
    by a *hypothesis the type judgement carries* rather than by there being no
    inhabitant. That is the difference between the two rungs, and it is why
    `plainRecv` had to go into `valueTy?` rather than being assumed at the use
    site: an inversion principle is only as strong as the definition it inverts.

    **What did *not* come due, against expectation.** `HANDOFF.md` §F1b predicted
    this would want `crubySingletonShadow` back as a `ResolvesTo` clause. It does
    not: `invoke` consults that gate only on the `md.builtin = none` branch
    (`Interp/Send.lean:246`) and `ResolvesTo` pins `md.builtin = some bid`, so the
    F1a measurement survives an abstract `.ref` receiver unchanged. -/
theorem valueTy_shapes {h : Heap} {v : Value} {τ : Ty} (hv : ValueTy h v τ) :
    (∃ a, v = .int a) ∨ (∃ b, v = .bool b) ∨ v = .nil ∨ (∃ s, v = .sym s) ∨
      (∃ o, v = .ref o ∧ plainRecv h o = true) := by
  cases v with
  | ref o =>
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨o, Eq.refl _, ?_⟩)))
    by_cases hp : plainRecv h o
    · exact hp
    · simp [ValueTy, valueTy?, hp] at hv
  | _ => simp_all [ValueTy, valueTy?]

/-- **A typed `.ref` is an id the heap actually has.** The point of `plainRecv`'s
    bound, isolated so that the transport lemmas can consume it without unfolding
    `valueTy?`: it is what will let `TypeAgree` be relativized to `< h.objs.size`
    and therefore hold across an `alloc`. -/
theorem valueTy_ref_lt {h : Heap} {o : ObjId} {τ : Ty} (hv : ValueTy h (.ref o) τ) :
    o < h.objs.size := by
  by_cases hb : o < h.objs.size
  · exact hb
  · simp [ValueTy, valueTy?, plainRecv, hb] at hv

/-- Every value in the list has the corresponding declared type. Pointwise, and
    length-forcing by the `_, _ => False` arm — the same shape as `FramesOk`, for
    the same reason: an arity mismatch must not be silently admissible. -/
def ValuesTy (h : Heap) : List Value → List Ty → Prop
  | [], [] => True
  | v :: vs, τ :: τs => ValueTy h v τ ∧ ValuesTy h vs τs
  | _, _ => False

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
def FrameConforms (h : Heap) (Γ : Env) (f : Frame) : Prop :=
  f.captured = none ∧
  -- The definee is `Object` for every frame in the fragment (no `class`, no
  -- `module`). Carried per-frame rather than for the current one only, because
  -- `frameK` resumes a *caller's* frame and `NoHook` has to survive that.
  f.defmod = Boot.objectId ∧
  ∀ x τ, envGet? Γ x = some τ → ValueTy h (localOf f x) τ

/-- **Per-frame conformance down the activation stack**, innermost first.

    The `∀ g ∈ fids, g < fid` clause buys frame-id **distinctness**, which is
    what makes `setLocal` provably local: it writes to `curFid` only, so every
    other frame on the stack is untouched. Distinctness is true of the real
    machine — a pushed id is `frames.size`, hence strictly greater than every id
    already on the stack — but it has to be *carried*, not rediscovered, so it
    rides here rather than being a side theorem (L91 predicted this clause).

    Equal lengths are forced by the `_, _ => False` arm, which is why this
    subsumes P0a's `stack ≠ []`. -/
def FramesOk (h : Heap) (frames : Array Frame) : List FrameId → List Env → Prop
  | [], [] => True
  | fid :: fids, Γ :: Γs =>
      fid < frames.size ∧ (∀ g ∈ fids, g < fid) ∧
      FrameConforms h Γ (frames.getD fid default) ∧ FramesOk h frames fids Γs
  | _, _ => False

/-- What `getLocal`/`setLocal` need, derived from the head of `FramesOk`. Kept as
    its own definition so the local-access lemmas stay readable. -/
def FrameOk (m : Machine) : Prop :=
  m.stack ≠ [] ∧ curFid m < m.frames.size ∧ (curFrame m).captured = none

/-- Every variable the environment types holds a value of that type. Stated
    against `m.getLocal` — what the interpreter actually reads. -/
def LocalsOk (Γ : Env) (m : Machine) : Prop :=
  ∀ x τ, envGet? Γ x = some τ → ValueTy m.heap (m.getLocal x) τ

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
    (h : FramesOk m.heap m.frames m.stack (Γ :: Γs)) : FrameOk m := by
  cases hst : m.stack with
  | nil => rw [hst] at h; exact absurd h (by simp [FramesOk])
  | cons fid fids =>
    rw [hst] at h
    obtain ⟨hlt, _, ⟨hc, _, _⟩, _⟩ := h
    refine ⟨by rw [hst]; simp, ?_, ?_⟩
    · simpa [curFid, hst] using hlt
    · simpa [curFrame, curFid, hst] using hc

/-- Popping the innermost activation: a suffix of a conforming stack conforms. -/
theorem FramesOk.tail {hp : Heap} {frames : Array Frame} {fids : List FrameId} {Γ : Env}
    {Γs : List Env} (h : FramesOk hp frames fids (Γ :: Γs)) :
    FramesOk hp frames fids.tail Γs := by
  cases fids with
  | nil => exact absurd h (by simp [FramesOk])
  | cons fid rest => exact h.2.2.2

theorem FramesOk.localsOk {m : Machine} {Γ : Env} {Γs : List Env}
    (h : FramesOk m.heap m.frames m.stack (Γ :: Γs)) : LocalsOk Γ m := by
  intro x τ hg
  rw [getLocal_cur h.frameOk x]
  cases hst : m.stack with
  | nil => rw [hst] at h; exact absurd h (by simp [FramesOk])
  | cons fid fids =>
    have hc : FrameConforms m.heap Γ (m.frames.getD fid default) := by
      rw [hst] at h; exact h.2.2.1
    have : curFrame m = m.frames.getD fid default := by
      simp [curFrame, curFid, hst]
    rw [this]
    exact hc.2.2 x τ hg

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
theorem FramesOk.frames_congr {hp : Heap} {a b : Array Frame} :
    ∀ {fids : List FrameId} {Γs : List Env}, FramesOk hp a fids Γs →
      (∀ g ∈ fids, g < b.size) → (∀ g ∈ fids, b.getD g default = a.getD g default) →
      FramesOk hp b fids Γs
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
    {τ : Ty} {v : Value} (hfs : FramesOk m.heap m.frames m.stack (Γ :: Γs))
    (hv : ValueTy m.heap v τ) :
    FramesOk m.heap (m.setLocal x v).frames (m.setLocal x v).stack
      (envSet Γ x τ :: Γs) := by
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
    refine ⟨by rw [hsz]; exact hfl, hgt, ⟨?_, ?_, ?_⟩, ?_⟩
    -- the head frame: captured survives, and the binding is updated at `x` only
    · have := (FrameOk.setLocal hf x v).2.2
      simpa [curFrame, curFid_setLocal, hcur] using this
    · -- `defmod` rides through `setLocal`, which only rewrites `locals`
      have := setLocal_frames hf x v
      rw [this, hcur, getD_set!_self _ _ _ hfl]
      show (curFrame m).defmod = Boot.objectId
      have : curFrame m = m.frames.getD fid default := by simp [curFrame, hcur]
      rw [this]; exact hcf.2.1
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
        have := hcf.2.2 y σ hg
        simpa [curFrame, hcur] using this
    -- the frames below: every id there is `< fid = curFid`, so `set!` missed them
    · refine FramesOk.frames_congr hrest (fun g hg => by rw [hsz]; exact Nat.lt_trans (hgt g hg) hfl)
        (fun g hg => ?_)
      rw [setLocal_frames hf x v, hcur]
      exact getD_set!_ne _ _ _ _ (Nat.ne_of_lt (hgt g hg))
/-! ### 1.5 Heap congruence — what the threading costs

Once the typing judgement is indexed by a heap, every heap-writing step owes a
*transport*: the `ValueTy` facts already stored in frames and continuations must
still hold in the new heap. `TypeAgree` is the condition that discharges it, and
it is deliberately stated as **exactly what a nominal `Ty` will read** rather than
as what today's four ground types read (which is nothing):

* `classOf` — the dispatch class of a value, what `T.instance C` must consult;
* `className` — the name a nominal type is written with (`Sub` as the `ancestors`
  walk, `PLAN.md` W5 T2, will need `ancestors` here too);
* `classPayload?`-ness — whether an id is a class at all, what `T.class_of C`
  needs.

`defineMethod` satisfies all three (`Proof/HeapFacts.lean`), which is why the
`def` case of preservation can discharge the transport today; a step that
`alloc`s or splices `includes` will not, and that is F1's real cost showing up
here rather than being discovered inside a 300-line case analysis.
-/

/-- The heap facts a nominal type language reads. Reflexive, and `defineMethod`
    is an instance.

    **The fourth clause is F1b's**, and it is the one place the class arm cost
    something that was not already written down: `valueTy?`'s `.ref` arm reads
    `plainRecv`, which reads the object's `eigen` and `payload`, and neither is
    determined by the first three. It is stated per-object rather than per-value
    for the same reason `className`'s clause is stated per-id — the transport is
    needed for values the *heap* holds, not only for the one in hand. -/
def TypeAgree (h h' : Heap) : Prop :=
  (∀ v, classOf h' v = classOf h v) ∧ (∀ k, className h' k = className h k) ∧
    (∀ k, (h'.classPayload? k).isSome = (h.classPayload? k).isSome) ∧
    (∀ o, plainRecv h' o = plainRecv h o)

theorem TypeAgree.rfl' (h : Heap) : TypeAgree h h :=
  ⟨fun _ => Eq.refl _, fun _ => Eq.refl _, fun _ => Eq.refl _, fun _ => Eq.refl _⟩

/-- Symmetric, because it is an equality of four functions. Needed by F1a: a
    conformance fact whose *hypotheses* mention the old heap has to read them in
    the new one, which is the transport running backwards. -/
theorem TypeAgree.symm {h h' : Heap} (ha : TypeAgree h h') : TypeAgree h' h :=
  ⟨fun v => (ha.1 v).symm, fun k => (ha.2.1 k).symm, fun k => (ha.2.2.1 k).symm,
    fun o => (ha.2.2.2 o).symm⟩

/-- A `setClassPayload` leaves a `.cls` payload at the written id — which is the
    only thing `plainRecv` reads there. Stated about the payload rather than about
    the whole `Object` so that the record literal `defineMethod` builds never has to
    be written out. -/
theorem payload_setClassPayload (h : Heap) (o : ObjId) (c : ClassPayload)
    (hb : o < h.objs.size) : ((h.setClassPayload o c).get o).payload = .cls c := by
  simp only [Heap.setClassPayload, Heap.get, Heap.set]
  rw [objs_getD_set!_self _ _ _ hb]

/-- **`defineMethod` cannot change whether an object is dispatched uniformly.**
    The fourth clause of `TypeAgree`, and the F1b analogue of
    `classPayload?_isSome_defineMethod`. It is *not* the statement that the payload
    is unchanged — at `o = cls` the payload really does change, since that is what
    `defineMethod` is for — only that it stays a `.cls`, which is all `plainRecv`
    asks. `eigen` is untouched because `setClassPayload` is a `with` on the payload
    field alone.

    Kept here rather than in `Proof/HeapFacts.lean` (where the rest of the
    `defineMethod` chain lives) because `plainRecv` is part of the *type
    judgement's* vocabulary — it exists to say which receivers `valueTy?` admits —
    and separating a definition from its only consumer costs more than the
    symmetry buys. -/
theorem plainRecv_defineMethod (h : Heap) (cls o : ObjId) (name : String)
    (md : MethodDef) : plainRecv (defineMethod h cls name md) o = plainRecv h o := by
  unfold defineMethod
  split
  · rename_i c hc
    by_cases hk : o = cls
    · subst hk
      -- Both sides are `false`, and for the same reason: `o` is a class object
      -- before the write (`hc`) and still one after it. Neither side reads `eigen`.
      have hb : o < h.objs.size := by
        by_cases hb : o < h.objs.size
        · exact hb
        · rw [classPayload?_oob h o hb] at hc; exact absurd hc (by simp)
      have hpay : (h.get o).payload = .cls c := by
        unfold Heap.classPayload? at hc
        split at hc <;> simp_all
      unfold plainRecv
      rw [payload_setClassPayload h o _ hb, hpay]
      simp
    · -- `set!` preserves `objs.size`, so the new bound clause is untouched too.
      have hsz : ∀ (a : Array Object) (i : Nat) (x : Object), (a.set! i x).size = a.size :=
        fun a i x => by simp [Array.set!]
      unfold plainRecv
      simp only [Heap.setClassPayload, Heap.get, Heap.set, hsz]
      rw [objs_getD_set!_ne _ _ _ _ hk]
  · rfl

theorem typeAgree_defineMethod (h : Heap) (cls : ObjId) (name : String)
    (md : MethodDef) : TypeAgree h (defineMethod h cls name md) := by
  -- The third clause was inline here and is now `classPayload?_isSome_defineMethod`
  -- in `Proof/HeapFacts.lean`, beside the rest of the `defineMethod` chain — it is
  -- a fact about the heap, not about the type judgement (F1a). The fourth is F1b's
  -- and is directly above, for the reason recorded there.
  exact ⟨fun v => classOf_defineMethod h cls name md v,
    fun k => className_defineMethod h cls k name md,
    fun k => classPayload?_isSome_defineMethod h cls k name md,
    fun o => plainRecv_defineMethod h cls o name md⟩

/-- Transport of the value judgement. **No longer `id`** (F1b): the `.ref` arm
    reads three of `TypeAgree`'s four clauses, which is what L137 threaded the
    heap in for and what it predicted would happen here rather than at the use
    sites. The immediate arms are still `id`, and that asymmetry is the whole
    reason the class arm could land as one commit. -/
theorem ValueTy.congr {h h' : Heap} {v : Value} {τ : Ty} (ha : TypeAgree h h')
    (hv : ValueTy h v τ) : ValueTy h' v τ := by
  cases v with
  | ref o => simpa [ValueTy, valueTy?, ha.2.2.2 o, ha.1, ha.2.1] using hv
  | _ => simp_all [ValueTy, valueTy?]

theorem ValuesTy.congr {h h' : Heap} (ha : TypeAgree h h') :
    ∀ {vs : List Value} {τs : List Ty}, ValuesTy h vs τs → ValuesTy h' vs τs
  | [], [], hv => hv
  | _ :: _, _ :: _, hv => ⟨ValueTy.congr ha hv.1, ValuesTy.congr ha hv.2⟩
  | [], _ :: _, hv => absurd hv (by simp [ValuesTy])
  | _ :: _, [], hv => absurd hv (by simp [ValuesTy])

theorem FrameConforms.congr {h h' : Heap} {Γ : Env} {f : Frame}
    (ha : TypeAgree h h') (hc : FrameConforms h Γ f) : FrameConforms h' Γ f :=
  ⟨hc.1, hc.2.1, fun x τ hg => ValueTy.congr ha (hc.2.2 x τ hg)⟩

theorem FramesOk.heap_congr {h h' : Heap} {frames : Array Frame}
    (ha : TypeAgree h h') :
    ∀ {fids : List FrameId} {Γs : List Env}, FramesOk h frames fids Γs →
      FramesOk h' frames fids Γs
  | [], [], hf => hf
  | _ :: fids, _ :: Γs, hf =>
      ⟨hf.1, hf.2.1, FrameConforms.congr ha hf.2.2.1, FramesOk.heap_congr ha hf.2.2.2⟩
  | [], _ :: _, hf => absurd hf (by simp [FramesOk])
  | _ :: _, [], hf => absurd hf (by simp [FramesOk])

/-- `setLocal` writes `locals`, so the heap rides through — needed wherever
    `FramesOk` is re-established at a machine `setLocal` produced. -/
theorem setLocal_heap {m : Machine} (x : String) (v : Value) :
    (m.setLocal x v).heap = m.heap := by simp [Machine.setLocal]


end Static
end Proof
end RubyCore
