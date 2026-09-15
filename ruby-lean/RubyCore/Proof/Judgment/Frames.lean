import RubyCore.Proof.Judgment.Values

/-!
# Frames conformance over `VTy` (J19 cont.)

`FrameConforms`/`FramesOk` (Proof/Static/Locals.lean), transliterated with the value
judgment widened from `ValueTy` to `VTy` — the `Judge`-side environments bind locals
at unions, which `ValueTy` cannot inhabit. Every proof is the old one with
`ValueTy.congr`/`.weaken` swapped for the `VTy` composition; the frames/array layer
(`localOfIn`, `ShallowChain`, `getD` lemmas, `setLocal` facts) is consumed by import,
unchanged, per the §7 interaction rule.
-/

namespace RubyCore
namespace Proof
namespace Judgment

open Interp
open RubyCore.Types
open RubyCore.Judgment
open RubyCore.Proof.Static

/-- One activation conforms to one environment — `FrameConforms` over `VTy`. -/
def FrameConformsJ (h : Heap) (frames : Array Frame) (Γ : Env) (fid : FrameId) : Prop :=
  ShallowChain frames fid ∧
  (h.classPayload? (frames.getD fid default).defmod).isSome ∧
  ∀ x τ, envGet? Γ x = some τ → VTy h (localOfIn frames (frames.getD fid default) x) τ

/-- Per-frame conformance down the activation stack, innermost first —
    `FramesOk`'s recursion, unchanged but for the conformance layer. -/
def FramesOkJ (h : Heap) (frames : Array Frame) : List FrameId → List Env → Prop
  | [], [] => True
  | fid :: fids, Γ :: Γs =>
      fid < frames.size ∧ (∀ g ∈ fids, g < fid) ∧
      FrameConformsJ h frames Γ fid ∧ FramesOkJ h frames fids Γs
  | _, _ => False

/-- Every variable the environment types holds a value of that type, at the machine's
    own read. -/
def LocalsOkJ (Γ : Env) (m : Machine) : Prop :=
  ∀ x τ, envGet? Γ x = some τ → VTy m.heap (m.getLocal x) τ

/-- An old-spine conformance is a new-spine one — `VTy.ofValueTy` pointwise. What
    `initiation` uses: the boot machine's frames conform in the old vocabulary. -/
theorem FrameConformsJ.ofStatic {h : Heap} {frames : Array Frame} {Γ : Env}
    {fid : FrameId} (hc : FrameConforms h frames Γ fid) : FrameConformsJ h frames Γ fid :=
  ⟨hc.1, hc.2.1, fun x τ hx => VTy.ofValueTy (hc.2.2 x τ hx)⟩

theorem FramesOkJ.ofStatic {h : Heap} {frames : Array Frame} :
    ∀ {fids : List FrameId} {Γs : List Env},
      FramesOk h frames fids Γs → FramesOkJ h frames fids Γs
  | [], [], h' => h'
  | _ :: _, _ :: _, h' =>
      ⟨h'.1, h'.2.1, FrameConformsJ.ofStatic h'.2.2.1, FramesOkJ.ofStatic h'.2.2.2⟩
  | [], _ :: _, h' => absurd h' (by simp [FramesOk])
  | _ :: _, [], h' => absurd h' (by simp [FramesOk])

theorem FrameConformsJ.mk' {h : Heap} {frames : Array Frame} {Γ : Env} {fid : FrameId}
    (hsc : ShallowChain frames fid)
    (hpay : (h.classPayload? (frames.getD fid default).defmod).isSome)
    (hv : ∀ x τ, envGet? Γ x = some τ →
      VTy h (localOfIn frames (frames.getD fid default) x) τ) :
    FrameConformsJ h frames Γ fid := ⟨hsc, hpay, hv⟩

theorem FramesOkJ.cons {hp : Heap} {frames : Array Frame} {fid : FrameId}
    {fids : List FrameId} {Γ : Env} {Γs : List Env} (hlt : fid < frames.size)
    (hgt : ∀ g ∈ fids, g < fid) (hc : FrameConformsJ hp frames Γ fid)
    (ht : FramesOkJ hp frames fids Γs) : FramesOkJ hp frames (fid :: fids) (Γ :: Γs) :=
  ⟨hlt, hgt, hc, ht⟩

/-! ## The `FramesOk` lemma set, transliterated -/

theorem FramesOkJ.frameShallow {m : Machine} {Γ : Env} {Γs : List Env}
    (h : FramesOkJ m.heap m.frames m.stack (Γ :: Γs)) : FrameShallow m := by
  cases hst : m.stack with
  | nil => rw [hst] at h; exact absurd h (by simp [FramesOkJ])
  | cons fid fids =>
    rw [hst] at h
    obtain ⟨hlt, _, ⟨hc, _, _⟩, _⟩ := h
    refine ⟨by rw [hst]; simp, ?_, ?_⟩
    · simpa [curFid, hst] using hlt
    · simpa [curFrame, curFid, hst] using hc

theorem FramesOkJ.frameOk {m : Machine} {Γ : Env} {Γs : List Env}
    (h : FramesOkJ m.heap m.frames m.stack (Γ :: Γs))
    (hc : (curFrame m).captured = none) : FrameOk m :=
  ⟨h.frameShallow.1, h.frameShallow.2.1, hc⟩

/-- Conformance narrows with the environment — one composition, as before. -/
theorem FrameConformsJ.narrow {h : Heap} {frames : Array Frame} {Γ Γ' : Env}
    {fid : FrameId} (hs : SubEnv Γ Γ') (hc : FrameConformsJ h frames Γ' fid) :
    FrameConformsJ h frames Γ fid :=
  ⟨hc.1, hc.2.1, fun x τ hx => hc.2.2 x τ (hs x τ hx)⟩

theorem FramesOkJ.narrowHead {hp : Heap} {frames : Array Frame} :
    ∀ {st : List FrameId} {Γ Γ' : Env} {Γs : List Env}, SubEnv Γ Γ' →
      FramesOkJ hp frames st (Γ' :: Γs) → FramesOkJ hp frames st (Γ :: Γs)
  | [], _, _, _, _, hf => absurd hf (by simp [FramesOkJ])
  | _ :: _, _, _, _, hs, hf =>
      ⟨hf.1, hf.2.1, FrameConformsJ.narrow hs hf.2.2.1, hf.2.2.2⟩

theorem FramesOkJ.tail {hp : Heap} {frames : Array Frame} {fids : List FrameId} {Γ : Env}
    {Γs : List Env} (h : FramesOkJ hp frames fids (Γ :: Γs)) :
    FramesOkJ hp frames fids.tail Γs := by
  cases fids with
  | nil => exact absurd h (by simp [FramesOkJ])
  | cons fid rest => exact h.2.2.2

theorem FramesOkJ.mem_lt {hp : Heap} {frames : Array Frame} :
    ∀ {fids : List FrameId} {Γs : List Env}, FramesOkJ hp frames fids Γs →
      ∀ g ∈ fids, g < frames.size := by
  intro fids
  induction fids with
  | nil => intro _ _ g hg; exact absurd hg (by simp)
  | cons fid rest ih =>
    intro Γs h g hg
    cases Γs with
    | nil => exact absurd h (by simp [FramesOkJ])
    | cons Γ Γs' =>
      rcases List.mem_cons.mp hg with rfl | hm
      · exact h.1
      · exact ih h.2.2.2 g hm

theorem FrameConformsJ.push {h : Heap} {frames : Array Frame} {f : Frame} {Γ : Env}
    {fid : FrameId} (hlt : fid < frames.size) (hc : FrameConformsJ h frames Γ fid) :
    FrameConformsJ h (frames.push f) Γ fid := by
  have hb : (frames.push f).getD fid default = frames.getD fid default :=
    getD_push_lt _ _ _ hlt
  refine ⟨fun p hp => ?_, by rw [hb]; exact hc.2.1, fun x τ hx => ?_⟩
  · rw [hb] at hp
    obtain ⟨hplt, hcp⟩ := hc.1 p hp
    exact ⟨hplt, by rw [getD_push_lt _ _ _ (Nat.lt_trans hplt hlt)]; exact hcp⟩
  · rw [hb, localOfIn_push hlt rfl hc.1]
    exact hc.2.2 x τ hx

theorem FramesOkJ.push {hp : Heap} {frames : Array Frame} {f : Frame} :
    ∀ {fids : List FrameId} {Γs : List Env}, FramesOkJ hp frames fids Γs →
      FramesOkJ hp (frames.push f) fids Γs := by
  intro fids
  induction fids with
  | nil => intro Γs h; cases Γs with
    | nil => exact trivial
    | cons _ _ => exact absurd h (by simp [FramesOkJ])
  | cons fid rest ih =>
    intro Γs h
    cases Γs with
    | nil => exact absurd h (by simp [FramesOkJ])
    | cons Γ Γs' =>
      obtain ⟨hlt, hgt, hfc, htl⟩ := h
      exact ⟨by rw [Array.size_push]; exact Nat.lt_succ_of_lt hlt, hgt,
        FrameConformsJ.push hlt hfc, ih htl⟩

theorem FramesOkJ.stack_singleton {hp : Heap} {frames : Array Frame}
    {fids : List FrameId} {Γ : Env} (h : FramesOkJ hp frames fids [Γ]) :
    ∃ fid, fids = [fid] := by
  cases fids with
  | nil => exact absurd h (by simp [FramesOkJ])
  | cons fid rest =>
    cases rest with
    | nil => exact ⟨fid, rfl⟩
    | cons a b => exact absurd h.2.2.2 (by simp [FramesOkJ])

theorem FramesOkJ.localsOk {m : Machine} {Γ : Env} {Γs : List Env}
    (h : FramesOkJ m.heap m.frames m.stack (Γ :: Γs)) : LocalsOkJ Γ m := by
  intro x τ hg
  rw [getLocal_curIn h.frameShallow x]
  cases hst : m.stack with
  | nil => rw [hst] at h; exact absurd h (by simp [FramesOkJ])
  | cons fid fids =>
    have hc : FrameConformsJ m.heap m.frames Γ fid := by
      rw [hst] at h; exact h.2.2.1
    have hcf : curFrame m = m.frames.getD fid default := by
      simp [curFrame, curFid, hst]
    rw [hcf]
    exact hc.2.2 x τ hg

theorem FramesOkJ.frames_congr {hp : Heap} {a b : Array Frame} {bound : Nat}
    (hbs : bound ≤ b.size) (heq : ∀ g, g < bound → b.getD g default = a.getD g default) :
    ∀ {fids : List FrameId} {Γs : List Env}, FramesOkJ hp a fids Γs →
      (∀ g ∈ fids, g < bound) → FramesOkJ hp b fids Γs
  | [], [], h, _ => h
  | fid :: fids, Γ :: Γs, h, hlt => by
    obtain ⟨_, hlt2, hcf, hrest⟩ := h
    have hfb : fid < bound := hlt fid (by simp)
    refine ⟨Nat.lt_of_lt_of_le hfb hbs, hlt2, ?_,
      FramesOkJ.frames_congr hbs heq hrest (fun g hg => hlt g (by simp [hg]))⟩
    have hbf := heq fid hfb
    refine ⟨fun q hq => ?_, by rw [hbf]; exact hcf.2.1, fun x τ hx => ?_⟩
    · rw [hbf] at hq
      obtain ⟨hqf, hqc⟩ := hcf.1 q hq
      exact ⟨hqf, by rw [heq q (Nat.lt_trans hqf hfb)]; exact hqc⟩
    · have hread : localOfIn b (b.getD fid default) x
          = localOfIn a (a.getD fid default) x := by
        rw [hbf]
        unfold localOfIn
        cases hf : (a.getD fid default).locals.find? (fun r => r.1 == x) with
        | some _ => rfl
        | none =>
          cases hcap : (a.getD fid default).captured with
          | none => rfl
          | some q => simp only [heq q (Nat.lt_trans (hcf.1 q hcap).1 hfb)]
      rw [hread]
      exact hcf.2.2 x τ hx
  | [], _ :: _, h, _ => absurd h (by simp [FramesOkJ])
  | _ :: _, [], h, _ => absurd h (by simp [FramesOkJ])

theorem FramesOkJ.setLocal {m : Machine} {Γ : Env} {Γs : List Env} {x : String}
    {τ : Ty} {v : Value} (hfs : FramesOkJ m.heap m.frames m.stack (Γ :: Γs))
    (hcap : (curFrame m).captured = none) (hv : VTy m.heap v τ) :
    FramesOkJ m.heap (m.setLocal x v).frames (m.setLocal x v).stack
      (envSet Γ x τ :: Γs) := by
  have hf : FrameOk m := hfs.frameOk hcap
  have hlt := hf.2.1
  rw [setLocal_stack]
  cases hst : m.stack with
  | nil => rw [hst] at hfs; exact absurd hfs (by simp [FramesOkJ])
  | cons fid fids =>
    have hcur : curFid m = fid := by simp [curFid, hst]
    rw [hst] at hfs
    obtain ⟨hfl, hgt, hcf, hrest⟩ := hfs
    have hsz : (m.setLocal x v).frames.size = m.frames.size := by
      rw [setLocal_frames hf x v]; simp [Array.set!]
    have hhead : (m.setLocal x v).frames.getD fid default
        = { curFrame m with locals := (x, v) :: (curFrame m).locals.filter (·.1 != x) } := by
      rw [setLocal_frames hf x v, hcur, getD_set!_self _ _ _ hfl]
    have hcapn : ((m.setLocal x v).frames.getD fid default).captured = none := by
      rw [hhead]
      simpa [curFrame, hcur] using hcap
    refine ⟨by rw [hsz]; exact hfl, hgt, ⟨ShallowChain.of_none hcapn, ?_, ?_⟩, ?_⟩
    · rw [hhead]
      have hcf' : curFrame m = m.frames.getD fid default := by simp [curFrame, hcur]
      have := hcf.2.1
      rw [← hcf'] at this
      exact this
    · intro y σ hg
      rw [localOfIn_of_captured_none _ hcapn]
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
        rw [localOfIn_of_captured_none _ (by simpa [curFrame, hcur] using hcap)] at this
        simpa [curFrame, hcur] using this
    · refine FramesOkJ.frames_congr (b := (m.setLocal x v).frames) (bound := fid)
        (by rw [hsz]; exact Nat.le_of_lt hfl) (fun g hg => ?_) hrest hgt
      rw [setLocal_frames hf x v, hcur]
      exact getD_set!_ne _ _ _ _ (Nat.ne_of_lt hg)

theorem FrameConformsJ.congr {h h' : Heap} {frames : Array Frame} {Γ : Env}
    {fid : FrameId} (ha : TypeAgree h h') (hc : FrameConformsJ h frames Γ fid) :
    FrameConformsJ h' frames Γ fid :=
  ⟨hc.1, by
    rw [ha.2.2.1 (frames.getD fid default).defmod (classPayload?_isSome_lt hc.2.1)]
    exact hc.2.1,
   fun x τ hg => VTy.congr ha (hc.2.2 x τ hg)⟩

theorem FramesOkJ.heap_congr {h h' : Heap} {frames : Array Frame}
    (ha : TypeAgree h h') :
    ∀ {fids : List FrameId} {Γs : List Env}, FramesOkJ h frames fids Γs →
      FramesOkJ h' frames fids Γs
  | [], [], hf => hf
  | _ :: fids, _ :: Γs, hf =>
      ⟨hf.1, hf.2.1, FrameConformsJ.congr ha hf.2.2.1, FramesOkJ.heap_congr ha hf.2.2.2⟩
  | [], _ :: _, hf => absurd hf (by simp [FramesOkJ])
  | _ :: _, [], hf => absurd hf (by simp [FramesOkJ])

/-! ## Pointwise-`SubJ` environment weakening (J27) -/

/-- Every lookup of the first environment resolves in the second, at a subtype —
    `SubEnv`'s pointwise-widened cousin (J13's exact-type ceiling lifted, on the
    invariant side only). -/
def SubEnvJ (Γ Γ' : Env) : Prop :=
  ∀ x τ, envGet? Γ x = some τ → ∃ σ, envGet? Γ' x = some σ ∧ SubJ σ τ

theorem FrameConformsJ.narrowJ {h : Heap} {frames : Array Frame} {Γ Γ' : Env}
    {fid : FrameId} (hs : SubEnvJ Γ Γ') (hc : FrameConformsJ h frames Γ' fid) :
    FrameConformsJ h frames Γ fid :=
  ⟨hc.1, hc.2.1, fun x τ hx =>
    let ⟨σ, hσ, hsj⟩ := hs x τ hx
    (hc.2.2 x σ hσ).weaken hsj⟩

theorem FramesOkJ.narrowHeadJ {hp : Heap} {frames : Array Frame} :
    ∀ {st : List FrameId} {Γ Γ' : Env} {Γs : List Env}, SubEnvJ Γ Γ' →
      FramesOkJ hp frames st (Γ' :: Γs) → FramesOkJ hp frames st (Γ :: Γs)
  | [], _, _, _, _, hf => absurd hf (by simp [FramesOkJ])
  | _ :: _, _, _, _, hs, hf =>
      ⟨hf.1, hf.2.1, FrameConformsJ.narrowJ hs hf.2.2.1, hf.2.2.2⟩

/-- Rebinding one variable at a subtype of its declared type. -/
theorem subEnvJ_set {Γ : Env} {x : String} {σ τ' : Ty} (h : SubJ σ τ') :
    SubEnvJ (envSet Γ x τ') (envSet Γ x σ) := by
  intro y τ hy
  rw [envGet?_set] at hy ⊢
  by_cases hq : y = x
  · rw [if_pos hq] at hy ⊢
    simp only [Option.some.injEq] at hy
    subst hy
    exact ⟨σ, rfl, h⟩
  · rw [if_neg hq] at hy ⊢
    exact ⟨τ, hy, SubJ.refl _⟩

/-- …and the un-narrowing direction: the original environment reads through the
    sharpened binding. -/
theorem subEnvJ_unset {Γ : Env} {x : String} {a τ₀ : Ty}
    (hget : envGet? Γ x = some τ₀) (h : SubJ a τ₀) :
    SubEnvJ Γ (envSet Γ x a) := by
  intro y τ hy
  rw [envGet?_set]
  by_cases hq : y = x
  · subst hq
    rw [hget] at hy
    simp only [Option.some.injEq] at hy
    subst hy
    exact ⟨a, by simp, h⟩
  · rw [if_neg hq]
    exact ⟨τ, hy, SubJ.refl _⟩

/-- **Sharpening the head binding at the stored value's own type** — the
    narrowing push's frame move: no write happens, so conformance at the new
    binding is the stored value's `VTy`, read where the machine reads it. -/
theorem FramesOkJ.setHead {m : Machine} {Γ : Env} {Γs : List Env} {x : String}
    {τ' : Ty} (hfs : FramesOkJ m.heap m.frames m.stack (Γ :: Γs))
    (hv : VTy m.heap (m.getLocal x) τ') :
    FramesOkJ m.heap m.frames m.stack (envSet Γ x τ' :: Γs) := by
  have hsh := hfs.frameShallow
  cases hst : m.stack with
  | nil => rw [hst] at hfs; exact absurd hfs (by simp [FramesOkJ])
  | cons fid fids =>
    rw [hst] at hfs
    obtain ⟨hlt, hgt, hcf, hrest⟩ := hfs
    refine ⟨hlt, hgt, ⟨hcf.1, hcf.2.1, ?_⟩, hrest⟩
    intro y σ hy
    rw [envGet?_set] at hy
    by_cases hq : y = x
    · rw [if_pos hq] at hy
      simp only [Option.some.injEq] at hy
      subst hy
      subst hq
      have := getLocal_curIn hsh y
      rw [show curFrame m = m.frames.getD fid default by
        simp [curFrame, curFid, hst]] at this
      rw [← this]
      exact hv
    · rw [if_neg hq] at hy
      exact hcf.2.2 y σ hy

end Judgment
end Proof
end RubyCore
