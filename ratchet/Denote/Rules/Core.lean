import Denote.Sem.Judge

/-!
# `Denote/Rules/Core.lean` — the two lemmas every leaf rung needs

A rung is "invert the run" (`Denote/Sem/notes.md`), and inverting even the shortest run
produces a machine that is **not** the one the obligation started from: `evalFrom` rewrites
`ctl` and `kont`, and the value step rewrites `ctl` again. So before any rule can be
discharged, two facts have to exist.

* **`ctl`/`kont` are invisible to conformance.** `StateOk` is a claim about the heap, the
  frames and the threaded tables; none of its eleven components reads the control word or the
  continuation stack. That is *almost* true by inspection — the exception is the two
  components that quantify over **runs** (`denM`'s arrow arms, through `Returns`, and
  `AsmsOk`, through `SendReturns`), and those survive for a sharper reason: `applyIn` and
  `sendIn` *overwrite* `ctl` and `kont` on the way in, so the run a call denotes is literally
  the same run from both machines. `denM_ctl` is the induction that says so; it needs the
  arrow, `denApp` and `denSpine` statements simultaneously because the three are mutually
  recursive.

* **A two-step run is its two steps.** `evals_pure` inverts `Evals` for any expression whose
  evaluation is a single `.next (withCtl … (.value w))` — the seven literals and a local
  read. `fuel = 0` and `fuel = 1` land on `.outOfFuel`, which is not a `.value`; `fuel ≥ 2`
  delivers `w` to the empty continuation, which is `.done`. The result is the *only* thing a
  leaf rung ever learns from its hypothesis: the value is `w`, and the machine is the starting
  one with its control word moved.

Neither lemma is about a rule, which is why they are here rather than in a rule file.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## `ctl`/`kont` are invisible to the denotation -/

/-- `m` with its control word and continuation stack replaced — the only kind of difference
between the machines a leaf rung has in hand. -/
abbrev reCtl (m : Machine) (c : Ctl) (k : List Kont) : Machine :=
  { m with ctl := c, kont := k }

/-- Calling a value does not see `ctl`/`kont`: `applyIn` sets both itself. -/
theorem applyIn_reCtl (m : Machine) (c : Ctl) (k : List Kont) (f : Value) (args : List Value) :
    applyIn (reCtl m c k) f args = applyIn m f args := rfl

theorem Returns_reCtl {m : Machine} {c : Ctl} {k : List Kont} {f : Value} {args : List Value}
    {v : Value} {m' : Machine} : Returns (reCtl m c k) f args v m' ↔ Returns m f args v m' :=
  Iff.rfl

/-- Same for an implicit-self send: `sendIn` sets `ctl` and `kont` itself. -/
theorem SendReturns_reCtl {m : Machine} {c : Ctl} {k : List Kont} {name : String}
    {args : List Value} {v : Value} {m' : Machine} :
    SendReturns (reCtl m c k) name args v m' ↔ SendReturns m name args v m' :=
  Iff.rfl

/-- The frame array is untouched, so every frame-indexed reader agrees. -/
@[simp] theorem heap_reCtl (m : Machine) (c : Ctl) (k : List Kont) :
    (reCtl m c k).heap = m.heap := rfl

@[simp] theorem frames_reCtl (m : Machine) (c : Ctl) (k : List Kont) :
    (reCtl m c k).frames = m.frames := rfl

@[simp] theorem stack_reCtl (m : Machine) (c : Ctl) (k : List Kont) :
    (reCtl m c k).stack = m.stack := rfl

@[simp] theorem currentFrame_reCtl (m : Machine) (c : Ctl) (k : List Kont) :
    (reCtl m c k).currentFrame = m.currentFrame := rfl

/-- Both local readers walk the frame array under an explicit fuel, carrying the machine as
an argument, so their agreement is an induction rather than a projection. -/
theorem getLocal_go_reCtl (m : Machine) (c : Ctl) (k : List Kont) (x : String) :
    ∀ (fuel : Nat) (fid : FrameId),
      Machine.getLocal.go (reCtl m c k) x fid fuel = Machine.getLocal.go m x fid fuel := by
  intro fuel
  induction fuel with
  | zero => intro fid; rfl
  | succ n ih =>
    intro fid
    simp only [Machine.getLocal.go]
    split
    · rfl
    · split
      · exact ih _
      · rfl

@[simp] theorem getLocal_reCtl (m : Machine) (c : Ctl) (k : List Kont) (x : String) :
    (reCtl m c k).getLocal x = m.getLocal x :=
  getLocal_go_reCtl m c k x _ _

theorem frameLocal_go_reCtl (m : Machine) (c : Ctl) (k : List Kont) (x : String) :
    ∀ (fuel : Nat) (fid : FrameId),
      frameLocal.go (reCtl m c k) x fid fuel = frameLocal.go m x fid fuel := by
  intro fuel
  induction fuel with
  | zero => intro fid; rfl
  | succ n ih =>
    intro fid
    simp only [frameLocal.go]
    split
    · rfl
    · split
      · exact ih _
      · rfl

@[simp] theorem frameLocal_reCtl (m : Machine) (c : Ctl) (k : List Kont) (fid : FrameId)
    (x : String) : frameLocal (reCtl m c k) fid x = frameLocal m fid x :=
  frameLocal_go_reCtl m c k x _ _

@[simp] theorem closLocal_reCtl (m : Machine) (c : Ctl) (k : List Kont) (cl : Closure) :
    closLocal (reCtl m c k) cl = closLocal m cl := by
  funext x; exact frameLocal_reCtl m c k cl.captured x

@[simp] theorem closSelf_reCtl (m : Machine) (c : Ctl) (k : List Kont) (cl : Closure) :
    closSelf (reCtl m c k) cl = closSelf m cl := rfl

/-- **The denotation does not read the control word.** All three mutually recursive relations
at once, by structural induction on the type. -/
theorem denM_ctl (m : Machine) (c : Ctl) (k : List Kont) : ∀ τ : Ty,
    (∀ v, denM τ (reCtl m c k) v ↔ denM τ m v) ∧
    (∀ acc f, denApp acc τ (reCtl m c k) f ↔ denApp acc τ m f) ∧
    (∀ g, denSpine τ (reCtl m c k) g ↔ denSpine τ m g) := by
  intro τ
  induction τ with
  | int | bool | nilT | sym | float | any | never | ivar0 =>
    exact ⟨fun _ => by simp [denM], fun _ _ => by simp [denApp], fun _ => by simp [denSpine]⟩
  | cls n | clsOf n =>
    exact ⟨fun _ => by simp [denM], fun _ _ => by simp [denApp], fun _ => by simp [denSpine]⟩
  | nilable τ ih =>
    exact ⟨fun v => by simp [denM, ih.1], fun _ _ => by simp [denApp], fun _ => by simp [denSpine]⟩
  | arrayOf e ih =>
    exact ⟨fun v => by simp [denM, ih.1], fun _ _ => by simp [denApp], fun _ => by simp [denSpine]⟩
  | hashOf a b iha ihb =>
    exact ⟨fun v => by simp [denM, iha.1, ihb.1], fun _ _ => by simp [denApp],
           fun _ => by simp [denSpine]⟩
  | union σ τ ihσ ihτ =>
    exact ⟨fun v => by simp [denM, ihσ.1, ihτ.1], fun _ _ => by simp [denApp],
           fun _ => by simp [denSpine]⟩
  | arrow0 r ihr =>
    exact ⟨fun f => by simp [denM, Returns_reCtl], fun _ _ => by simp [denApp, Returns_reCtl],
           fun _ => by simp [denSpine]⟩
  | arrowCons p rest ihp ihrest =>
    exact ⟨fun f => by simp [denM, ihp.1, ihrest.2.1], fun _ _ => by simp [denApp, ihp.1, ihrest.2.1],
           fun _ => by simp [denSpine]⟩
  | inst n I ihI =>
    exact ⟨fun v => by simp [denM, ihI.2.2], fun _ _ => by simp [denApp], fun _ => by simp [denSpine]⟩
  | ivarCons x σ rest ihσ ihrest =>
    exact ⟨fun _ => by simp [denM], fun _ _ => by simp [denApp],
           fun g => by simp [denSpine, ihσ.1, ihrest.2.2]⟩
  | clos idx cap selfT ihcap ihself =>
    exact ⟨fun f => by simp [denM, ihcap.2.2, ihself.1], fun _ _ => by simp [denApp],
           fun _ => by simp [denSpine]⟩
  | sameAs y τ ih =>
    exact ⟨fun v => by simp [denM, ih.1], fun _ _ => by simp [denApp], fun _ => by simp [denSpine]⟩

theorem denM_reCtl {τ : Ty} {m : Machine} {c : Ctl} {k : List Kont} {v : Value} :
    denM τ (reCtl m c k) v ↔ denM τ m v := (denM_ctl m c k τ).1 v

theorem denSpine_reCtl {τ : Ty} {m : Machine} {c : Ctl} {k : List Kont} {g : String → Value} :
    denSpine τ (reCtl m c k) g ↔ denSpine τ m g := (denM_ctl m c k τ).2.2 g

theorem denAll_reCtl {τs : List Ty} {m : Machine} {c : Ctl} {k : List Kont} {vs : List Value} :
    DenAll τs (reCtl m c k) vs ↔ DenAll τs m vs := by
  induction τs generalizing vs with
  | nil => cases vs <;> simp [DenAll]
  | cons τ τs ih =>
    cases vs with
    | nil => simp [DenAll]
    | cons v vs => simp only [DenAll]; exact and_congr denM_reCtl (ih)

/-- **Conformance does not read the control word.** One line per component; each is either a
heap/frame fact (unchanged by construction) or a run fact (`applyIn`/`sendIn` overwrite
`ctl`/`kont`, so the run is the same run). -/
theorem StateOk_reCtl {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} (h : StateOk κ Γ I m)
    (c : Ctl) (k : List Kont) : StateOk κ Γ I (reCtl m c k) where
  env := by
    intro x τ hx
    have := h.env x τ hx
    exact ⟨by simpa using denM_reCtl.mpr this.1, by simpa using this.2⟩
  selfSpine := by
    have := h.selfSpine
    simpa [SelfSpineOk] using denSpine_reCtl.mpr this
  classes := by simpa [ClassesOk] using h.classes
  defs := by simpa [DefsOk] using h.defs
  asms := by
    intro a ha args hargs v m' hs
    exact h.asms a ha args (denAll_reCtl.mp hargs) v m' (SendReturns_reCtl.mp hs)
  frame := by
    have h2 := h.frame
    unfold FrameOk at h2 ⊢
    cases hf : κ.frame with
    | none => rw [hf] at h2; simpa using h2
    | some f => rw [hf] at h2; simpa using h2
  closures := h.closures
  blockTy := by
    have h2 := h.blockTy
    unfold BlockTyOk at h2 ⊢
    cases hb : κ.blockTy with
    | none => rw [hb] at h2; simpa using h2
    | some β =>
      rw [hb] at h2
      obtain ⟨b, hb1, hb2⟩ := h2
      exact ⟨b, by simpa using hb1, denM_reCtl.mpr hb2⟩
  selfTy := by
    have h2 := h.selfTy
    unfold SelfTyOk at h2 ⊢
    cases hσ : κ.selfTy with
    | none => trivial
    | some σ => rw [hσ] at h2; simpa using denM_reCtl.mpr h2
  consts := by
    intro p τ hp
    obtain ⟨v, hv1, hv2⟩ := h.consts p τ hp
    exact ⟨v, by simpa using hv1, denM_reCtl.mpr hv2⟩
  privConsts := h.privConsts

/-! ## Inverting a two-step run -/

/-- `Interp.run`'s two equations, as rewrite rules. -/
theorem run_zero (m : Machine) : Interp.run 0 m = .outOfFuel m := rfl

theorem run_succ (fuel : Nat) (m : Machine) :
    Interp.run (fuel + 1) m =
      (match Interp.stepFn m with
       | .next m' => Interp.run fuel m'
       | .done v m' => .value v m'
       | .uncaught exc m' => .uncaught exc m'
       | .unsupported r => .unsupported r m
       | .stuck msg => .stuck msg m) := rfl

/-- Delivering a value to the empty continuation is `.done`. -/
theorem stepFn_value_nil (m : Machine) (w : Value) :
    Interp.stepFn (reCtl m (.value w) []) = .done w (reCtl m (.value w) []) := rfl

/-- **The leaf-rung inversion.** If evaluating `e` from `m` is one step to `.value w`, then a
run that returned, returned `w`, and left `m` with only its control word moved.

`fuel = 0` and `fuel = 1` cannot have produced a `.value` (`Interp.run` reports `.outOfFuel`
before the empty continuation is reached); at `fuel ≥ 2` the second step is `applyKont` on
`[]`, which is `.done`. -/
theorem evals_pure {m : Machine} {e : Ratchet.Expr} {w v : Value} {m' : Machine}
    (hstep : Interp.stepFn (evalFrom m e) = .next (reCtl m (.value w) []))
    (h : Evals m e v m') :
    v = w ∧ m' = reCtl m (.value w) [] := by
  obtain ⟨fuel, hrun⟩ := h
  match fuel with
  | 0 => rw [run_zero] at hrun; exact absurd hrun (by simp)
  | 1 => simp only [run_succ, hstep, run_zero] at hrun; exact absurd hrun (by simp)
  | fuel + 2 =>
    simp only [run_succ, hstep, stepFn_value_nil] at hrun
    cases hrun
    exact ⟨rfl, rfl⟩

#print axioms evals_pure
#print axioms StateOk_reCtl

end Ratchet.Denote
