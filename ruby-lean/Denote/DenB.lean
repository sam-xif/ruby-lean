import Denote.Den

/-!
# `Denote/DenB.lean` — the computable core

`Ty → Heap → Value → Bool`, the literal shape the design note asked for, and the shape that
can be `#eval`'d against a real booted heap (`Denote/Examples.lean`) or dropped into a
`decide`.

**It is the first-order fragment and nothing else.** The three constructors whose denotation
quantifies over machine states — both arrow arms and `clos` — answer `false` here, and that is
not a stub to be filled in later: an arrow denotes a universally quantified statement about
*every* argument in the domain and *every* fuel, which no `Bool` can decide. The split is
therefore permanent, and it is the same split `FirstOrder` (`Denote/Den.lean`) names.

Because of that, `denB` is **one-sided**: `denB τ h v = true` always means `v` really is in
`τ`'s denotation (`denB_sound`), while `denB τ h v = false` means "not in it, *or* the type is
higher-order". On the `FirstOrder` fragment the one-sidedness disappears and the two agree
exactly (`denB_iff`) — so `denB` is a genuine decision procedure there, and the honest
statement of its limit is a hypothesis rather than a caveat in prose.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

mutual

/-- The computable denotation on the first-order fragment; `false` on the three
machine-quantifying constructors. -/
def denB : Ty → Heap → Value → Bool
  | .int, _, v => isIntV v
  | .bool, _, v => isBoolV v
  | .nilT, _, v => isNilV v
  | .sym, _, v => isSymV v
  | .float, _, v => isFltV v
  | .any, _, _ => true
  | .never, _, _ => false
  | .cls n, h, v => isAName h v n
  | .clsOf n, h, v => isClassRefNamed h v n
  | .nilable τ, h, v => isNilV v || denB τ h v
  | .union σ τ, h, v => denB σ h v || denB τ h v
  | .arrayOf e, h, v =>
      match arrElems? h v with
      | some xs => xs.all (fun x => denB e h x)
      | none => false
  | .hashOf k w, h, v =>
      match hshEntries? h v with
      | some es => es.all (fun p => denB k h p.1 && denB w h p.2)
      | none => false
  | .inst n I, h, v => isExactInst h v n && denSpineBFrom [] I h (fun x => ivarOf h v x)
  | .sameAs _ τ, h, v => denB τ h v
  | .ivar0, _, _ => false
  | .ivarCons .., _, _ => false
  -- Higher-order: not decidable, and not a gap to be closed. See the module docstring.
  | .arrow0 _, _, _ => false
  | .arrowCons .., _, _ => false
  | .clos .., _, _ => false
termination_by τ _ _ => sizeOf τ

/-- The `Bool` twin of `denSpineFrom`, accumulator and all — see that definition for why the
accumulator exists (`Denote/Sem/notes.md` §The tenth stall point). A shadowed entry is
**skipped**, i.e. answers `true`, which is the decidable reading of "the spine says nothing
about a key an earlier entry already bound". -/
def denSpineBFrom : List String → Ty → Heap → (String → Value) → Bool
  | _, .ivar0, _, _ => true
  | seen, .ivarCons x σ rest, h, get =>
      (seen.contains x || denB σ h (get x)) && denSpineBFrom (x :: seen) rest h get
  | _, _, _, _ => false
termination_by _ τ _ _ => sizeOf τ

end

def denSpineB (τ : Ty) (h : Heap) (get : String → Value) : Bool := denSpineBFrom [] τ h get

/-- **Agreement on the first-order fragment**, proved simultaneously with the spine statement.
Stated against an arbitrary machine over the heap, so it composes with `denM_heap_only`. -/
theorem denB_iff_aux : ∀ (τ : Ty), FirstOrder τ = true →
    (∀ (h : Heap) (m : Machine) (v : Value), m.heap = h →
      (denB τ h v = true ↔ denM τ m v)) ∧
    (∀ (h : Heap) (m : Machine) (g : String → Value) (seen : List String), m.heap = h →
      (denSpineBFrom seen τ h g = true ↔ denSpineFrom seen τ m g)) := by
  intro τ
  induction τ with
  | int | bool | nilT | sym | float | any | never | ivar0 =>
    intro _
    exact ⟨fun _ _ _ _ => by simp [denB, denM], fun _ _ _ _ _ => by simp [denSpineBFrom, denSpineFrom]⟩
  | cls n =>
    intro _
    exact ⟨fun h m v hh => by subst hh; simp [denB, denM],
           fun _ _ _ _ _ => by simp [denSpineBFrom, denSpineFrom]⟩
  | clsOf n =>
    intro _
    exact ⟨fun h m v hh => by subst hh; simp [denB, denM],
           fun _ _ _ _ _ => by simp [denSpineBFrom, denSpineFrom]⟩
  | nilable τ ih =>
    intro hf
    simp only [FirstOrder] at hf
    refine ⟨fun h m v hh => ?_, fun _ _ _ _ _ => by simp [denSpineBFrom, denSpineFrom]⟩
    simp only [denB, denM, Bool.or_eq_true]
    exact or_congr Iff.rfl ((ih hf).1 h m v hh)
  | union σ τ ihσ ihτ =>
    intro hf
    simp only [FirstOrder, Bool.and_eq_true] at hf
    refine ⟨fun h m v hh => ?_, fun _ _ _ _ _ => by simp [denSpineBFrom, denSpineFrom]⟩
    simp only [denB, denM, Bool.or_eq_true]
    exact or_congr ((ihσ hf.1).1 h m v hh) ((ihτ hf.2).1 h m v hh)
  | sameAs n τ ih =>
    intro hf
    simp only [FirstOrder] at hf
    refine ⟨fun h m v hh => ?_, fun _ _ _ _ _ => by simp [denSpineBFrom, denSpineFrom]⟩
    simp only [denB, denM]
    exact (ih hf).1 h m v hh
  | arrayOf e ih =>
    intro hf
    simp only [FirstOrder] at hf
    refine ⟨fun h m v hh => ?_, fun _ _ _ _ _ => by simp [denSpineBFrom, denSpineFrom]⟩
    subst hh
    simp only [denB, denM]
    cases hx : arrElems? m.heap v with
    | none => simp
    | some xs =>
      simp only [Array.all_eq_true', exists_eq_left', Option.some.injEq]
      constructor
      · intro h₁ x hxm; exact ((ih hf).1 m.heap m x rfl).mp (h₁ x hxm)
      · intro h₁ x hxm; exact ((ih hf).1 m.heap m x rfl).mpr (h₁ x hxm)
  | hashOf k w ihk ihw =>
    intro hf
    simp only [FirstOrder, Bool.and_eq_true] at hf
    refine ⟨fun h m v hh => ?_, fun _ _ _ _ _ => by simp [denSpineBFrom, denSpineFrom]⟩
    subst hh
    simp only [denB, denM]
    cases hx : hshEntries? m.heap v with
    | none => simp
    | some es =>
      simp only [Array.all_eq_true', exists_eq_left', Option.some.injEq,
        Bool.and_eq_true]
      constructor
      · intro h₁ p hpm
        exact ⟨((ihk hf.1).1 m.heap m p.1 rfl).mp (h₁ p hpm).1,
               ((ihw hf.2).1 m.heap m p.2 rfl).mp (h₁ p hpm).2⟩
      · intro h₁ p hpm
        exact ⟨((ihk hf.1).1 m.heap m p.1 rfl).mpr (h₁ p hpm).1,
               ((ihw hf.2).1 m.heap m p.2 rfl).mpr (h₁ p hpm).2⟩
  | inst n I ih =>
    intro hf
    simp only [FirstOrder] at hf
    refine ⟨fun h m v hh => ?_, fun _ _ _ _ _ => by simp [denSpineBFrom, denSpineFrom]⟩
    subst hh
    simp only [denB, denM, Bool.and_eq_true]
    exact and_congr Iff.rfl ((ih hf).2 m.heap m (fun x => ivarOf m.heap v x) [] rfl)
  | ivarCons x σ rest ihσ ihrest =>
    intro hf
    simp only [FirstOrder, Bool.and_eq_true] at hf
    refine ⟨fun _ _ _ _ => by simp [denB, denM], fun h m g seen hh => ?_⟩
    simp only [denSpineBFrom, denSpineFrom, Bool.and_eq_true, Bool.or_eq_true,
      List.contains_iff_mem]
    exact and_congr (or_congr Iff.rfl ((ihσ hf.1).1 h m (g x) hh))
      ((ihrest hf.2).2 h m g (x :: seen) hh)
  | arrow0 r _ => intro hf; simp [FirstOrder] at hf
  | arrowCons p rest _ _ => intro hf; simp [FirstOrder] at hf
  | clos i cap st _ _ => intro hf; simp [FirstOrder] at hf

/-- `denB` decides `den` on the first-order fragment. -/
theorem denB_iff {τ : Ty} (hf : FirstOrder τ = true) (h : Heap) (v : Value) :
    denB τ h v = true ↔ den τ h v :=
  (denB_iff_aux τ hf).1 h (Machine.initOn h .nil) v rfl

/-- **`denB` is sound at every type**, higher-order ones included: a `true` from the
computable core is a real membership fact about the real machine.

Proved by its own induction rather than as a corollary of `denB_iff`, because
`FirstOrder τ = false` does not localise: `nilable (arrow0 int)` is higher-order without
*being* an arrow, so there is no leaf-case argument to make. The induction, on the other hand,
needs no hypothesis at all — every arm where `denB` answers `false` discharges itself. -/
theorem denB_sound_aux : ∀ (τ : Ty),
    (∀ (h : Heap) (m : Machine) (v : Value), m.heap = h → denB τ h v = true → denM τ m v) ∧
    (∀ (h : Heap) (m : Machine) (g : String → Value) (seen : List String), m.heap = h →
      denSpineBFrom seen τ h g = true → denSpineFrom seen τ m g) := by
  intro τ
  induction τ with
  | int | bool | nilT | sym | float =>
    exact ⟨fun _ _ _ _ hb => by simpa [denB, denM] using hb,
           fun _ _ _ _ _ hb => by simp [denSpineBFrom] at hb⟩
  | any =>
    exact ⟨fun _ _ _ _ _ => by simp [denM], fun _ _ _ _ _ hb => by simp [denSpineBFrom] at hb⟩
  | never =>
    exact ⟨fun _ _ _ _ hb => by simp [denB] at hb,
           fun _ _ _ _ _ hb => by simp [denSpineBFrom] at hb⟩
  | ivar0 =>
    exact ⟨fun _ _ _ _ hb => by simp [denB] at hb, fun _ _ _ _ _ _ => by simp [denSpineFrom]⟩
  | cls n =>
    exact ⟨fun h m v hh hb => by subst hh; simpa [denB, denM] using hb,
           fun _ _ _ _ _ hb => by simp [denSpineBFrom] at hb⟩
  | clsOf n =>
    exact ⟨fun h m v hh hb => by subst hh; simpa [denB, denM] using hb,
           fun _ _ _ _ _ hb => by simp [denSpineBFrom] at hb⟩
  | nilable τ ih =>
    refine ⟨fun h m v hh hb => ?_, fun _ _ _ _ _ hb => by simp [denSpineBFrom] at hb⟩
    simp only [denB, Bool.or_eq_true] at hb
    simp only [denM]
    exact hb.imp id (ih.1 h m v hh)
  | union σ τ ihσ ihτ =>
    refine ⟨fun h m v hh hb => ?_, fun _ _ _ _ _ hb => by simp [denSpineBFrom] at hb⟩
    simp only [denB, Bool.or_eq_true] at hb
    simp only [denM]
    exact hb.imp (ihσ.1 h m v hh) (ihτ.1 h m v hh)
  | sameAs n τ ih =>
    refine ⟨fun h m v hh hb => ?_, fun _ _ _ _ _ hb => by simp [denSpineBFrom] at hb⟩
    simp only [denB] at hb
    simp only [denM]
    exact ih.1 h m v hh hb
  | arrayOf e ih =>
    refine ⟨fun h m v hh hb => ?_, fun _ _ _ _ _ hb => by simp [denSpineBFrom] at hb⟩
    subst hh
    simp only [denB] at hb
    cases hx : arrElems? m.heap v with
    | none => rw [hx] at hb; simp at hb
    | some xs =>
      rw [hx] at hb
      simp only [Array.all_eq_true'] at hb
      show denM (.arrayOf e) m v
      rw [denM]
      exact ⟨xs, hx, fun x hxm => ih.1 m.heap m x rfl (hb x hxm)⟩
  | hashOf k w ihk ihw =>
    refine ⟨fun h m v hh hb => ?_, fun _ _ _ _ _ hb => by simp [denSpineBFrom] at hb⟩
    subst hh
    simp only [denB] at hb
    cases hx : hshEntries? m.heap v with
    | none => rw [hx] at hb; simp at hb
    | some es =>
      rw [hx] at hb
      simp only [Array.all_eq_true', Bool.and_eq_true] at hb
      show denM (.hashOf k w) m v
      rw [denM]
      exact ⟨es, hx, fun p hpm =>
        ⟨ihk.1 m.heap m p.1 rfl (hb p hpm).1, ihw.1 m.heap m p.2 rfl (hb p hpm).2⟩⟩
  | inst n I ih =>
    refine ⟨fun h m v hh hb => ?_, fun _ _ _ _ _ hb => by simp [denSpineBFrom] at hb⟩
    subst hh
    simp only [denB, Bool.and_eq_true] at hb
    show denM (.inst n I) m v
    rw [denM]
    exact ⟨hb.1, ih.2 m.heap m (fun x => ivarOf m.heap v x) [] rfl hb.2⟩
  | ivarCons x σ rest ihσ ihrest =>
    refine ⟨fun _ _ _ _ hb => by simp [denB] at hb, fun h m g seen hh hb => ?_⟩
    simp only [denSpineBFrom, Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem] at hb
    rw [denSpineFrom]
    exact ⟨hb.1.imp id (ihσ.1 h m (g x) hh), ihrest.2 h m g (x :: seen) hh hb.2⟩
  -- The three machine-quantifying arms: `denB` answers `false`, so there is nothing to prove.
  | arrow0 r _ =>
    exact ⟨fun _ _ _ _ hb => by simp [denB] at hb, fun _ _ _ _ _ hb => by simp [denSpineBFrom] at hb⟩
  | arrowCons p rest _ _ =>
    exact ⟨fun _ _ _ _ hb => by simp [denB] at hb, fun _ _ _ _ _ hb => by simp [denSpineBFrom] at hb⟩
  | clos i cap st _ _ =>
    exact ⟨fun _ _ _ _ hb => by simp [denB] at hb, fun _ _ _ _ _ hb => by simp [denSpineBFrom] at hb⟩

theorem denB_sound {τ : Ty} (h : Heap) (v : Value) (hb : denB τ h v = true) : den τ h v :=
  (denB_sound_aux τ).1 h (Machine.initOn h .nil) v rfl hb

/-- The same, at an arbitrary machine over the heap — what a proof about a running program
wants, since it has a machine in hand and not a bare heap. -/
theorem denB_soundM {τ : Ty} (m : Machine) (v : Value) (hb : denB τ m.heap v = true) :
    denM τ m v :=
  (denB_sound_aux τ).1 m.heap m v rfl hb

/-! ## The `clos` arm, which *is* decidable once you have a machine

`denB` answers `false` on `Ty.clos` because it is handed only a heap, and a closure's captured
scope lives in `Machine.frames` (`Denote/Apply.lean`). Given a machine there is nothing
undecidable about it: the captured spine and the creation `self` are lookups. So the arrow is
the *only* genuinely undecidable arm, and `closB` says so by deciding the other one.

Note the reuse: `denSpineB` already takes an arbitrary `String → Value`, so the closure's
captured-scope reader drops straight in where an object's `ivarOf` went. That is what the
spine abstraction was for. -/

/-- The computable `Ty.clos` denotation, at a machine. `false` on any other type — this is a
one-arm supplement to `denB`, not a replacement for it. -/
def closB (κ : Ty) (m : Machine) (f : Value) : Bool :=
  match κ with
  | .clos _ cap selfT =>
      match procClosure? m.heap f with
      | some cl =>
          denSpineB cap m.heap (closLocal m cl) &&
            (if selfT = .never then true else denB selfT m.heap (closSelf m cl))
      | none => false
  | _ => false

theorem closB_sound {κ : Ty} {m : Machine} {f : Value} (hb : closB κ m f = true) :
    denM κ m f := by
  match κ with
  | .clos i cap selfT =>
    simp only [closB] at hb
    cases hc : procClosure? m.heap f with
    | none => rw [hc] at hb; simp at hb
    | some cl =>
      rw [hc] at hb
      simp only [Bool.and_eq_true] at hb
      show denM (.clos i cap selfT) m f
      rw [denM]
      refine ⟨cl, hc, (denB_sound_aux cap).2 m.heap m (closLocal m cl) [] rfl hb.1, ?_⟩
      by_cases hs : selfT = .never
      · exact Or.inl hs
      · rw [if_neg hs] at hb
        exact Or.inr ((denB_sound_aux selfT).1 m.heap m _ rfl hb.2)
  | .int | .bool | .nilT | .sym | .float | .any | .never | .cls _ | .clsOf _
  | .nilable _ | .union _ _ | .arrayOf _ | .hashOf _ _ | .inst _ _ | .sameAs _ _
  | .ivar0 | .ivarCons .. | .arrow0 _ | .arrowCons .. => simp [closB] at hb

/-! House rule, as in `Ratchet/Proof/ChkSound.lean`: the file states its own axiom bill. -/

#print axioms denB_iff
#print axioms denB_sound
#print axioms denB_soundM
#print axioms closB_sound

end Ratchet.Denote
