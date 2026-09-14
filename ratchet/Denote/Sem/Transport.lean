import Denote.Sem.Framed

/-!
# `Denote/Sem/Transport.lean` — the two lemmas every leaf rung needs

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

@[simp] theorem frameLocal?_reCtl (m : Machine) (c : Ctl) (k : List Kont)
    (fid? : Option FrameId) (x : String) :
    frameLocal? (reCtl m c k) fid? x = frameLocal? m fid? x := by
  cases fid? with
  | none => rfl
  | some fid => exact frameLocal_reCtl m c k fid x

@[simp] theorem closLocal_reCtl (m : Machine) (c : Ctl) (k : List Kont) (cl : Closure) :
    closLocal (reCtl m c k) cl = closLocal m cl := by
  funext x; exact frameLocal?_reCtl m c k cl.captured x

@[simp] theorem closSelf_reCtl (m : Machine) (c : Ctl) (k : List Kont) (cl : Closure) :
    closSelf (reCtl m c k) cl = closSelf m cl := rfl

/-- **`Ext` does not read the control word either**, and this is the clause that keeps the
future-quantified arrow (`Denote/Den.lean` §The arrow arm point 5) compatible with the rest
of this file. `Ext` constrains the heap, the frame array and the frame stack — all three of
which `reCtl` preserves definitionally — which is exactly the property `Denote/Sem/notes.md`
observed a `Reaches`-seeded arrow would *not* have had. -/
theorem Ext_reCtl {m m₂ : Machine} {c : Ctl} {k : List Kont} :
    Ext (reCtl m c k) m₂ ↔ Ext m m₂ :=
  ⟨fun h => ⟨h.frames, h.stack, h.size, h.get, h.payload, h.ancestors, h.freshIvars,
              h.freshBasic⟩,
   fun h => ⟨h.frames, h.stack, h.size, h.get, h.payload, h.ancestors, h.freshIvars,
              h.freshBasic⟩⟩

theorem Later_reCtl {m m₂ : Machine} {c : Ctl} {k : List Kont} :
    Later (reCtl m c k) m₂ ↔ Later m m₂ :=
  ⟨fun h => ⟨h.stack, h.frameCount, h.size, h.klass, h.eigen, h.payloadObj, h.frozen,
              h.payload, h.ancestors⟩,
   fun h => ⟨h.stack, h.frameCount, h.size, h.klass, h.eigen, h.payloadObj, h.frozen,
              h.payload, h.ancestors⟩⟩

/-- **The denotation does not read the control word.** All three mutually recursive relations
at once, by structural induction on the type. -/
theorem denM_ctl (m : Machine) (c : Ctl) (k : List Kont) : ∀ τ : Ty,
    (∀ v, denM τ (reCtl m c k) v ↔ denM τ m v) ∧
    (∀ acc f, denApp acc τ (reCtl m c k) f ↔ denApp acc τ m f) ∧
    (∀ seen g, denSpineFrom seen τ (reCtl m c k) g ↔ denSpineFrom seen τ m g) := by
  intro τ
  induction τ with
  | int | bool | nilT | sym | float | any | never | ivar0 =>
    exact ⟨fun _ => by simp [denM], fun _ _ => by simp [denApp], fun _ _ => by simp [denSpineFrom]⟩
  | cls n | clsOf n =>
    exact ⟨fun _ => by simp [denM], fun _ _ => by simp [denApp], fun _ _ => by simp [denSpineFrom]⟩
  | nilable τ ih =>
    exact ⟨fun v => by simp [denM, ih.1], fun _ _ => by simp [denApp], fun _ _ => by simp [denSpineFrom]⟩
  | arrayOf e ih =>
    exact ⟨fun v => by simp [denM, ih.1], fun _ _ => by simp [denApp], fun _ _ => by simp [denSpineFrom]⟩
  | hashOf a b iha ihb =>
    exact ⟨fun v => by simp [denM, iha.1, ihb.1], fun _ _ => by simp [denApp],
           fun _ _ => by simp [denSpineFrom]⟩
  | union σ τ ihσ ihτ =>
    exact ⟨fun v => by simp [denM, ihσ.1, ihτ.1], fun _ _ => by simp [denApp],
           fun _ _ => by simp [denSpineFrom]⟩
  | arrow0 r ihr =>
    exact ⟨fun f => by simp [denM, Later_reCtl], fun _ _ => by simp [denApp, Returns_reCtl],
           fun _ _ => by simp [denSpineFrom]⟩
  | arrowCons p rest ihp ihrest =>
    exact ⟨fun f => by simp [denM, Later_reCtl], fun _ _ => by simp [denApp, ihp.1, ihrest.2.1],
           fun _ _ => by simp [denSpineFrom]⟩
  | inst n I ihI =>
    exact ⟨fun v => by simp [denM, ihI.2.2], fun _ _ => by simp [denApp], fun _ _ => by simp [denSpineFrom]⟩
  | ivarCons x σ rest ihσ ihrest =>
    exact ⟨fun _ => by simp [denM], fun _ _ => by simp [denApp],
           fun seen g => by simp [denSpineFrom, ihσ.1, ihrest.2.2]⟩
  | clos idx cap selfT ihcap ihself =>
    exact ⟨fun f => by simp [denM, ihcap.2.2, ihself.1], fun _ _ => by simp [denApp],
           fun _ _ => by simp [denSpineFrom]⟩
  | sameAs y τ ih =>
    exact ⟨fun v => by simp [denM, ih.1], fun _ _ => by simp [denApp], fun _ _ => by simp [denSpineFrom]⟩

theorem denM_reCtl {τ : Ty} {m : Machine} {c : Ctl} {k : List Kont} {v : Value} :
    denM τ (reCtl m c k) v ↔ denM τ m v := (denM_ctl m c k τ).1 v

theorem denSpine_reCtl {τ : Ty} {m : Machine} {c : Ctl} {k : List Kont} {g : String → Value} :
    denSpine τ (reCtl m c k) g ↔ denSpine τ m g := (denM_ctl m c k τ).2.2 [] g

theorem denAll_reCtl {τs : List Ty} {m : Machine} {c : Ctl} {k : List Kont} {vs : List Value} :
    DenAll τs (reCtl m c k) vs ↔ DenAll τs m vs := by
  induction τs generalizing vs with
  | nil => cases vs <;> simp [DenAll]
  | cons τ τs ih =>
    cases vs with
    | nil => simp [DenAll]
    | cons v vs => simp only [DenAll]; exact and_congr denM_reCtl (ih)

/-- **Rewriting the control word is an allocation that allocates nothing.** Every clause of
`Ext` reads the heap, the frame array or the frame stack, and `reCtl` preserves all three
definitionally — so this is `Ext.refl` with the fields retyped, and the two fresh-id clauses
discharge exactly as they do there. -/
theorem Ext_toReCtl (m : Machine) (c : Ctl) (k : List Kont) : Ext m (reCtl m c k) where
  frames := rfl
  stack := rfl
  size := Nat.le_refl _
  get := fun _ _ => rfl
  payload := fun _ => rfl
  ancestors := fun _ => rfl
  freshIvars := fun o ho => by rw [get_oob m.heap ho]; rfl
  freshBasic := fun o ho k hk => by rw [classOf_oob m.heap ho]; exact hk

/-- **`Framed` at a leaf rung**: `reCtl` touches neither the heap nor the frame stack, so both
fields are `rfl`. This is the first conjunct of every rule whose value is produced in one step
without allocating. -/
theorem Framed_reCtl (m : Machine) (c : Ctl) (k : List Kont) : Framed m (reCtl m c k) :=
  Framed.of_heap_stack rfl rfl (.of_eq rfl rfl)

/-- An `Ext` is a `Framed`: it pins the frame stack and every object's class-ness outright.
Every allocating leaf rung already builds one for `StateOk_ext`, so this is where those rungs
get their first conjunct. -/
theorem Framed.of_ext {m m' : Machine} (he : Ext m m') : Framed m m' :=
  ⟨he.stack, fun k h => by rw [he.payload]; exact h,
    fun v n h => by
      simpa only [denM] using
        (denM_ext (τ := .cls n) (v := v) he (by simpa only [denM] using h)),
    fun _ _ _ h => denM_ext he h, .of_eq he.stack he.frames⟩

theorem Framed_withCtl (m : Machine) (c : Ctl) : Framed m (Interp.withCtl m c) :=
  Framed.of_heap_stack rfl rfl (.of_eq rfl rfl)

theorem Framed_setLocal (m : Machine) (x : String) (w : Value) :
    Framed m (m.setLocal x w) :=
  Framed.of_heap_stack (setLocal_heap m x w) (setLocal_stack m x w) (.setLocal m x w)

/-- **Conformance does not read the control word.** A corollary of `StateOk_ext`
(`Denote/Sem/State.lean`) rather than a second component-by-component induction: rewriting
`ctl`/`kont` is a degenerate `Ext`, so the transport that was built for allocation covers it.
The eleven-line proof this replaces is recorded in `../../implementation-notes.md`; the point
of collapsing it is that there is now exactly one place where "component `X` survives a
change to the machine" is proved. -/
theorem StateOk_reCtl {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} (h : StateOk κ Γ I m)
    (c : Ctl) (k : List Kont) : StateOk κ Γ I (reCtl m c k) :=
  StateOk_ext h (Ext_toReCtl m c k) h.stringPayload h.arrayPayload h.hashPayload rfl

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

/-- **The leaf-rung inversion.** If evaluating `e` from `m` is one step to a machine `m₁`
holding `.value w` under an empty continuation, then a run that returned, returned `w`, and
left exactly that machine.

`m₁` is a *separate* machine variable rather than `m` itself, and that is the whole
generalisation the allocating literals needed: `Judge.strLit`'s one step pushes an object, so
its `m₁` is `m` with a longer heap (`Denote/Rules/Alloc.lean`). The pure literals instantiate
`m₁ := m` and read exactly as before.

`fuel = 0` and `fuel = 1` cannot have produced a `.value` (`Interp.run` reports `.outOfFuel`
before the empty continuation is reached); at `fuel ≥ 2` the second step is `applyKont` on
`[]`, which is `.done`. -/
theorem evals_pure {m : Machine} {e : Ratchet.Expr} {m₁ : Machine} {w v : Value}
    {m' : Machine}
    (hstep : Interp.stepFn (evalFrom m e) = .next (reCtl m₁ (.value w) []))
    (h : Evals m e v m') :
    v = w ∧ m' = reCtl m₁ (.value w) [] := by
  obtain ⟨fuel, hrun⟩ := h
  match fuel with
  | 0 => rw [run_zero] at hrun; exact absurd hrun (by simp)
  | 1 => simp only [run_succ, hstep, run_zero] at hrun; exact absurd hrun (by simp)
  | fuel + 2 =>
    simp only [run_succ, hstep, stepFn_value_nil] at hrun
    cases hrun
    exact ⟨rfl, rfl⟩

/-- **The four-step inversion**, for a rule whose evaluation pushes a continuation and pops
it: `Judge.vasgnAlias` is `eval (vasgn …)` → `eval (var …)` → deliver → `asgnK` → deliver.
Same argument as `evals_pure`, one fuel case per step. -/
theorem evals_four {m : Machine} {e : Ratchet.Expr} {m₁ m₂ m₃ : Machine} {w v : Value}
    {m' : Machine}
    (h1 : Interp.stepFn (evalFrom m e) = .next m₁)
    (h2 : Interp.stepFn m₁ = .next m₂)
    (h3 : Interp.stepFn m₂ = .next (reCtl m₃ (.value w) []))
    (h : Evals m e v m') : v = w ∧ m' = reCtl m₃ (.value w) [] := by
  obtain ⟨fuel, hrun⟩ := h
  match fuel with
  | 0 => rw [run_zero] at hrun; exact absurd hrun (by simp)
  | 1 => simp only [run_succ, h1, run_zero] at hrun; exact absurd hrun (by simp)
  | 2 => simp only [run_succ, h1, h2, run_zero] at hrun; exact absurd hrun (by simp)
  | 3 => simp only [run_succ, h1, h2, h3, run_zero] at hrun; exact absurd hrun (by simp)
  | fuel + 4 =>
    simp only [run_succ, h1, h2, h3, stepFn_value_nil] at hrun
    cases hrun
    exact ⟨rfl, rfl⟩

#print axioms evals_pure
#print axioms evals_four
#print axioms StateOk_reCtl

end Ratchet.Denote
