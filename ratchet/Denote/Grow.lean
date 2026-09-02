import Denote.Arrow

/-!
# `Denote/Grow.lean` — a type's meaning survives an allocation

One theorem, `denM_ext`: if `m₂` is `m` after an allocation (`Ext`, `Denote/Ext.lean`), then
every value in `τ`'s denotation at `m` is in `τ`'s denotation at `m₂`.

**This is what a rung for an allocating rule needs, and it is why `Ext` exists.** The
semantic ratchet stalled at `Judge.strLit` (`Denote/Sem/notes.md` §The fourth stall point)
because a string literal allocates: its post-machine's heap is its pre-machine's with one
object pushed, and re-establishing `StateOk` there means re-proving `EnvOk Γ m'` — i.e.
transporting `denM τ` across the push for an **arbitrary** `τ` drawn from `Γ`, including
types no rule ever produces.

Four shapes of case, and the interesting thing is how few of them are hard:

* **Immediate** (`int`, `bool`, …) — the machine does not appear.
* **In-range reads** (`arrayOf`, `hashOf`, `clos`) — the projection *succeeding* is what
  pins the reference in range (`lt_of_arrElems?` and friends), so `Ext.get` applies and the
  payload is literally the same one. No side condition on the value is needed anywhere in
  this file, and that is the pay-off from `Ext` carrying its two fresh-id clauses instead.
* **Nominal** (`cls`, `inst`) — one-directional, via `Ext.isA_mono`. The direction is the
  content: a dangling `.ref` reads as a bare `BasicObject` before the push and as the pushed
  object after it, so the nominal arm can only *gain* inhabitants.
* **The arrow** — free, by `Ext.later` then `Later.trans`, because `denM`'s arrow arm was
  rewritten to quantify over `Later`-futures for exactly this purpose (`Denote/Den.lean` §The
  arrow arm point 5).
  Nothing about runs is re-derived here; the definition absorbed the problem.

`denSpine` rides along in the same induction (the two are mutually recursive through `inst`
and `clos`), and it needs one extra move the value case does not: the spine is read through
a *function* — `ivarOf m.heap v`, `closLocal m cl` — and that function changes with the
machine. `Ext.ivarOf_eq` and `Ext.closLocal_eq` say it does not change *pointwise*, and
`funext` turns that into the rewrite. `ivarOf` agreeing at a dangling reference is precisely
what `Ext.freshIvars` is for.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-- **The denotation is monotone along allocation.** Value and spine together, because
`denM` and `denSpine` are mutually recursive. -/
theorem denM_ext_aux {m m₂ : Machine} (he : Ext m m₂) : ∀ τ : Ty,
    (∀ v, denM τ m v → denM τ m₂ v) ∧ (∀ g, denSpine τ m g → denSpine τ m₂ g) := by
  intro τ
  induction τ with
  | int | bool | nilT | sym | float | any | never =>
    exact ⟨fun _ h => by rwa [denM] at h ⊢, fun _ h => absurd h (by simp [denSpine])⟩
  | ivar0 => exact ⟨fun _ h => absurd h (by simp [denM]), fun _ _ => by simp [denSpine]⟩
  | cls n =>
    exact ⟨fun _ h => by rw [denM] at h ⊢; exact he.isAName_mono h,
           fun _ h => by simpa only [denSpine] using h⟩
  | clsOf n =>
    exact ⟨fun _ h => by rw [denM] at h ⊢; rwa [he.isClassRefNamed_eq],
           fun _ h => by simpa only [denSpine] using h⟩
  | nilable τ ih =>
    exact ⟨fun _ h => by rw [denM] at h ⊢; exact h.imp id (ih.1 _),
           fun _ h => by simpa only [denSpine] using h⟩
  | union σ τ ihσ ihτ =>
    exact ⟨fun _ h => by rw [denM] at h ⊢; exact h.imp (ihσ.1 _) (ihτ.1 _),
           fun _ h => by simpa only [denSpine] using h⟩
  | sameAs y τ ih =>
    exact ⟨fun _ h => by rw [denM] at h ⊢; exact ih.1 _ h,
           fun _ h => by simpa only [denSpine] using h⟩
  | arrayOf e ih =>
    refine ⟨fun v h => ?_, fun _ h => by simpa only [denSpine] using h⟩
    rw [denM] at h ⊢
    obtain ⟨xs, hx, hall⟩ := h
    exact ⟨xs, he.arrElems?_eq hx, fun x hxs => ih.1 x (hall x hxs)⟩
  | hashOf a b iha ihb =>
    refine ⟨fun v h => ?_, fun _ h => by simpa only [denSpine] using h⟩
    rw [denM] at h ⊢
    obtain ⟨es, hx, hall⟩ := h
    exact ⟨es, he.hshEntries?_eq hx, fun p hp => ⟨iha.1 _ (hall p hp).1, ihb.1 _ (hall p hp).2⟩⟩
  | arrow0 r ihr =>
    refine ⟨fun f h => ?_, fun _ h => by simpa only [denSpine] using h⟩
    rw [denM] at h ⊢
    exact ⟨he.isProcV_mono h.1, fun m₃ he₃ => h.2 m₃ (he.later.trans he₃)⟩
  | arrowCons p rest ihp ihrest =>
    refine ⟨fun f h => ?_, fun _ h => by simpa only [denSpine] using h⟩
    rw [denM] at h ⊢
    exact ⟨he.isProcV_mono h.1, fun m₃ he₃ => h.2 m₃ (he.later.trans he₃)⟩
  | inst n I ihI =>
    refine ⟨fun v h => ?_, fun _ h => by simpa only [denSpine] using h⟩
    rw [denM] at h ⊢
    refine ⟨he.isAName_mono h.1, ?_⟩
    have hfun : ivarOf m₂.heap v = ivarOf m.heap v := funext (he.ivarOf_eq v)
    rw [hfun]
    exact ihI.2 _ h.2
  | ivarCons x σ rest ihσ ihrest =>
    refine ⟨fun _ h => by rwa [denM] at h ⊢, fun g h => ?_⟩
    rw [denSpine] at h ⊢
    exact ⟨ihσ.1 _ h.1, ihrest.2 g h.2⟩
  | clos idx cap selfT ihcap ihself =>
    refine ⟨fun f h => ?_, fun _ h => by simpa only [denSpine] using h⟩
    rw [denM] at h ⊢
    obtain ⟨cl, hpc, hspine, hself⟩ := h
    refine ⟨cl, he.procClosure?_eq hpc, ?_, ?_⟩
    · rw [he.closLocal_eq cl]; exact ihcap.2 _ hspine
    · rcases hself with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [he.closSelf_eq cl]; exact ihself.1 _ h)

theorem denM_ext {τ : Ty} {m m₂ : Machine} (he : Ext m m₂) {v : Value}
    (h : denM τ m v) : denM τ m₂ v := (denM_ext_aux he τ).1 v h

theorem denSpine_ext {τ : Ty} {m m₂ : Machine} (he : Ext m m₂) {g : String → Value}
    (h : denSpine τ m g) : denSpine τ m₂ g := (denM_ext_aux he τ).2 g h

theorem denAll_ext {τs : List Ty} {m m₂ : Machine} (he : Ext m m₂) :
    ∀ {vs : List Value}, DenAll τs m vs → DenAll τs m₂ vs := by
  induction τs with
  | nil => intro vs h; cases vs <;> simp_all [DenAll]
  | cons τ τs ih =>
    intro vs h
    cases vs with
    | nil => exact absurd h (by simp)
    | cons v vs => exact ⟨denM_ext he h.1, ih h.2⟩

#print axioms denM_ext
#print axioms denAll_ext

end Ratchet.Denote
