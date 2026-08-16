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

/-- The type of a value **in a heap**, where P0 has one. `.ref`/`.flt` have none
    — the fragment allocates no objects, so they never arise.

    **Heap-indexed as of L137, and today no arm reads the heap.** That is
    deliberate and it is the F1 prerequisite: a nominal class type
    (`widening-the-fragment.md` §6 F1, `PLAN.md` W5 T2) can only say what class a
    `.ref` belongs to by consulting `classOf`/`className`, so the *judgement* has
    to be heap-relative before the *type language* can grow. Threading it while
    every arm is still heap-independent is what makes the two changes separable,
    and §1.5's congruence lemmas are where the cost of the threading shows up. -/
def valueTy? (_h : Heap) : Value → Option Ty
  | .int _ => some .int
  | .bool _ => some .bool
  | .nil => some .nilT
  -- `def` evaluates to the method name (`Interp.lean:2624`).
  | .sym _ => some .sym
  | _ => none

def ValueTy (h : Heap) (v : Value) (τ : Ty) : Prop := valueTy? h v = some τ

/-- Inversion at the `int` arm. Moved here from `Proof/Static/Konts.lean` in F1a:
    it is a fact about `ValueTy`, and `Proof/Static/Decls.lean` — which sits
    *below* `Konts.lean` now — needs it to build the base table's entries. -/
theorem valueTy_int {hp : Heap} {v : Value} (h : ValueTy hp v .int) : ∃ a, v = .int a := by
  cases v <;> simp_all [ValueTy, valueTy?]

/-- **Every value with a type is an immediate.** `valueTy?` has no `.ref` arm, so
    the fragment's judgement itself rules out an object receiver — which is what
    lets `Proof/Static/Decls.lean`'s `entry_dispatch` discharge `invoke`'s
    class-receiver special cases (F1a). The first place F1b will have to change
    something rather than extend it. -/
theorem valueTy_immediate {h : Heap} {v : Value} {τ : Ty} (hv : ValueTy h v τ) :
    (∃ a, v = .int a) ∨ (∃ b, v = .bool b) ∨ v = .nil ∨ (∃ s, v = .sym s) := by
  cases v <;> simp_all [ValueTy, valueTy?]

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
    is an instance. -/
def TypeAgree (h h' : Heap) : Prop :=
  (∀ v, classOf h' v = classOf h v) ∧ (∀ k, className h' k = className h k) ∧
    (∀ k, (h'.classPayload? k).isSome = (h.classPayload? k).isSome)

theorem TypeAgree.rfl' (h : Heap) : TypeAgree h h :=
  ⟨fun _ => Eq.refl _, fun _ => Eq.refl _, fun _ => Eq.refl _⟩

/-- Symmetric, because it is an equality of three functions. Needed by F1a: a
    conformance fact whose *hypotheses* mention the old heap has to read them in
    the new one, which is the transport running backwards. -/
theorem TypeAgree.symm {h h' : Heap} (ha : TypeAgree h h') : TypeAgree h' h :=
  ⟨fun v => (ha.1 v).symm, fun k => (ha.2.1 k).symm, fun k => (ha.2.2 k).symm⟩

theorem typeAgree_defineMethod (h : Heap) (cls : ObjId) (name : String)
    (md : MethodDef) : TypeAgree h (defineMethod h cls name md) := by
  -- The third clause was inline here and is now `classPayload?_isSome_defineMethod`
  -- in `Proof/HeapFacts.lean`, beside the rest of the `defineMethod` chain — it is
  -- a fact about the heap, not about the type judgement (F1a).
  exact ⟨fun v => classOf_defineMethod h cls name md v,
    fun k => className_defineMethod h cls k name md,
    fun k => classPayload?_isSome_defineMethod h cls k name md⟩

/-- Transport of the value judgement. **No arm reads the heap today**, so this is
    `id` — and it is stated with the hypothesis anyway, because the point of L137
    is that the hypothesis is where a nominal arm will land, and a lemma that has
    to grow a hypothesis later is a lemma every caller has to be revisited for. -/
theorem ValueTy.congr {h h' : Heap} {v : Value} {τ : Ty} (_ha : TypeAgree h h')
    (hv : ValueTy h v τ) : ValueTy h' v τ := by
  cases v <;> simp_all [ValueTy, valueTy?]

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
