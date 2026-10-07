import Books.TypeSoundness.Conformance.Closure.Capture
import Books.TypeSoundness.Denotation.CaptureFuel
import Books.TypeSoundness.Denotation.Grow

/-! A closure literal reserves a frame-store slot that no activation uses. Pushing such a
dead frame changes no heap object and no live capture chain; only lookup fuel grows. -/
set_option autoImplicit false
namespace Checker.Soundness
open RubyCore

def pushDead (m : Machine) (f : RubyCore.Frame) : Machine := { m with frames := m.frames.push f }

theorem pushDead_getD {m : Machine} {f : RubyCore.Frame} {i : FrameId} (h : i < m.frames.size) :
    (pushDead m f).frames.getD i default = m.frames.getD i default := by
  simp [pushDead, Array.getD, h, Nat.lt_succ_of_lt h, Array.getElem_push_lt]

theorem CaptureLive.pushDead {m : Machine} {c : Option FrameId} (h : CaptureLive m c)
    (f : RubyCore.Frame) : CaptureLive (Soundness.pushDead m f) c :=
  h.frames_preserved (by simp [Soundness.pushDead]) (fun _ hi => pushDead_getD hi)

theorem frameLocal_pushDead {m : Machine} {fid : FrameId} (hl : CaptureLive m (some fid))
    (f : RubyCore.Frame) (x : String) :
    frameLocal (pushDead m f) fid x = frameLocal m fid x := by
  simp only [frameLocal]
  rw [frameLocal_go_preserved (n := pushDead m f) (fun _ hi => pushDead_getD hi) x _ fid hl,
    frameLocal_go_fuel hl x _ (by simp [pushDead]; omega),
    frameLocal_go_fuel hl x (m.frames.size + 1) (by omega)]

theorem closLocal_pushDead {m : Machine} {cl : Closure} (hl : CaptureLive m cl.captured)
    (f : RubyCore.Frame) : closLocal (pushDead m f) cl = closLocal m cl := by
  funext x
  simp only [closLocal]
  cases hc : cl.captured with
  | none => rfl
  | some p => rw [hc] at hl; exact frameLocal_pushDead hl f x

theorem closSelf_pushDead {m : Machine} {cl : Closure} (hl : CaptureLive m cl.captured)
    (h0 : 0 < m.frames.size) (f : RubyCore.Frame) : closSelf (pushDead m f) cl = closSelf m cl := by
  simp only [closSelf]
  cases hc : cl.captured with
  | none => exact congrArg RubyCore.Frame.self (pushDead_getD h0)
  | some p => rw [hc] at hl; exact congrArg RubyCore.Frame.self (pushDead_getD hl.lt)

theorem later_pushDead (m : Machine) (f : RubyCore.Frame) : Later m (pushDead m f) where
  stack := rfl
  frameCount := by simp [pushDead]
  size := Nat.le_refl _
  klass := fun _ _ => rfl
  eigen := fun _ _ => rfl
  payloadObj := fun _ _ => rfl
  frozen := fun _ _ => rfl
  payload := fun _ => rfl
  ancestors := fun _ => rfl

theorem denM_pushDead_aux {m : Machine} (f : RubyCore.Frame) (h0 : 0 < m.frames.size) :
    ∀ τ : Ty, (∀ v, denM τ m v → denM τ (pushDead m f) v) ∧
      (∀ seen g, denSpineFrom seen τ m g → denSpineFrom seen τ (pushDead m f) g) := by
  intro τ
  induction τ with
  | int | bool | nilT | sym | float | any | never | cls _ | clsOf _ =>
    exact ⟨fun _ h => by rw [denM] at h ⊢; exact h, fun _ _ h => absurd h (by simp [denSpineFrom])⟩
  | ivar0 => exact ⟨fun _ h => absurd h (by simp [denM]), fun _ _ _ => by simp [denSpineFrom]⟩
  | nilable τ ih =>
    exact ⟨fun _ h => by rw [denM] at h ⊢; exact h.imp id (ih.1 _),
           fun _ _ h => absurd h (by simp [denSpineFrom])⟩
  | union σ τ ihσ ihτ =>
    exact ⟨fun _ h => by rw [denM] at h ⊢; exact h.imp (ihσ.1 _) (ihτ.1 _),
           fun _ _ h => absurd h (by simp [denSpineFrom])⟩
  | sameAs y τ ih =>
    exact ⟨fun _ h => by rw [denM] at h ⊢; exact ih.1 _ h,
           fun _ _ h => absurd h (by simp [denSpineFrom])⟩
  | arrayOf e ih =>
    refine ⟨fun v h => ?_, fun _ _ h => absurd h (by simp [denSpineFrom])⟩
    rw [denM] at h ⊢
    obtain ⟨xs, hx, hall⟩ := h
    exact ⟨xs, hx, fun x hxs => ih.1 x (hall x hxs)⟩
  | hashOf a b iha ihb =>
    refine ⟨fun v h => ?_, fun _ _ h => absurd h (by simp [denSpineFrom])⟩
    rw [denM] at h ⊢
    obtain ⟨es, hx, hall⟩ := h
    exact ⟨es, hx, fun p hp => ⟨iha.1 _ (hall p hp).1, ihb.1 _ (hall p hp).2⟩⟩
  | arrow0 r _ =>
    refine ⟨fun f' h => ?_, fun _ _ h => absurd h (by simp [denSpineFrom])⟩
    rw [denM] at h ⊢
    exact ⟨h.1, fun m₃ he₃ => h.2 m₃ ((later_pushDead m f).trans he₃)⟩
  | arrowCons p rest _ _ =>
    refine ⟨fun f' h => ?_, fun _ _ h => absurd h (by simp [denSpineFrom])⟩
    rw [denM] at h ⊢
    exact ⟨h.1, fun m₃ he₃ => h.2 m₃ ((later_pushDead m f).trans he₃)⟩
  | inst n I ihI =>
    refine ⟨fun v h => ?_, fun _ _ h => absurd h (by simp [denSpineFrom])⟩
    rw [denM] at h ⊢
    exact ⟨h.1, ihI.2 _ _ h.2⟩
  | ivarCons x σ rest ihσ ihrest =>
    refine ⟨fun _ h => by rwa [denM] at h ⊢, fun seen g h => ?_⟩
    rw [denSpineFrom] at h ⊢
    exact ⟨h.1.imp id (ihσ.1 _), ihrest.2 _ g h.2⟩
  | clos idx cap selfT ihcap ihself =>
    refine ⟨fun f' h => ?_, fun _ _ h => absurd h (by simp [denSpineFrom])⟩
    rw [denM] at h ⊢
    obtain ⟨cl, hpc, hcode, hspine, hself, hlive⟩ := h
    rcases hlive with ⟨rfl, rfl⟩ | hlive
    · exact ⟨cl, hpc, hcode, by simp [denSpineFrom], Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩
    refine ⟨cl, hpc, hcode, ?_, ?_, Or.inr (hlive.pushDead f)⟩
    · rw [closLocal_pushDead hlive f]; exact ihcap.2 _ _ hspine
    · rcases hself with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [closSelf_pushDead hlive h0 f]; exact ihself.1 _ h)

theorem denM_pushDead {τ : Ty} {m : Machine} (f : RubyCore.Frame) (h0 : 0 < m.frames.size)
    {v : Value} (h : denM τ m v) : denM τ (pushDead m f) v := (denM_pushDead_aux f h0 τ).1 v h

theorem denSpine_pushDead {τ : Ty} {m : Machine} (f : RubyCore.Frame) (h0 : 0 < m.frames.size)
    {g : String → Value} (h : denSpine τ m g) : denSpine τ (pushDead m f) g :=
  (denM_pushDead_aux f h0 τ).2 [] g h

#print axioms denM_pushDead
end Checker.Soundness
