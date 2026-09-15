import Denote.Typed.MethodState
import Denote.Typed.MainReturn
import RubyCore.Proof.Judgment.ClsFresh

/-! Class-frame restoration is independent of the superclass and allocation strategy.
The heap producer supplies Framed at publication; a checked body supplies it thereafter. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.ClassActivation
open RubyCore Ratchet Ratchet.Denote
open RubyCore.Proof.Judgment (freshModFrame)

variable {κ κb : Ctx} {Γ Γb : Env} {I Ib : Ty} {m n : Machine} {h : Heap} {k : ObjId}
def publishHeap (m : Machine) (h : Heap) : Machine := { m with heap := h }
local notation "published" => publishHeap m h
local notation "entry" => pushMethodFrame published (freshModFrame k m.currentFrame.cref)

theorem pop_framed (hl : m.stack.headD 0 < m.frames.size)
    (hp : Framed m published) (hb : Framed entry n) : Framed m (popMethodFrame n) :=
  hp.trans (method_pop_framed hl rfl hb)

theorem pop_getLocal (hl : m.stack.headD 0 < m.frames.size) (hu : RootUncaptured m)
    (hb : Framed entry n) (x : String) : (popMethodFrame n).getLocal x = m.getLocal x := by
  have hp := method_pop_getLocal (m := published) (f := freshModFrame k m.currentFrame.cref) hl hu rfl hb x
  rw [getLocal_uncaptured (m := published) hu] at hp
  rw [getLocal_uncaptured hu]
  exact hp

theorem pop_currentFrame (hl : FrameInRange m) (hb : Framed entry n) :
    (popMethodFrame n).currentFrame = m.currentFrame := method_pop_currentFrame (m := published) hl rfl hb

theorem pop_envOk (hm : StateOk κ Γ I m) (hp : Framed m published) (hu : RootUncaptured m)
    (hb : Framed entry n) (ht : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) :
    EnvOk Γ (popMethodFrame n) := by
  have framed := pop_framed hm.frameInRange.2 hp hb
  have hv := pop_getLocal hm.frameInRange.2 hu hb
  refine ⟨?_, ?_⟩
  · intro x τ hx
    obtain ⟨z, hz⟩ := envGet?_mem hx
    obtain ⟨hd, ha⟩ := hm.env.1 x τ hx
    refine ⟨?_, ?_⟩
    · rw [hv]; exact framed.firstOrder _ (ht (z, τ) hz) _ hd
    · intro y ρ hy; rw [hv, hv]; exact ha y ρ hy
  · intro x hx; rw [hv]; exact hm.env.2 x hx

theorem pop_main_state {name : String} (hm : StateOk κ Γ I m) (hp : Framed m published)
    (ht : ReframeFO (returnScopeCtx κ κb) I) (ha : κ.asms = [])
    (hr : κ.scope.runtimeMain = true) (hw : κb.pos.mainWorld = true)
    (hcl : κ.scope.runtimeClass = none) (hu : RootUncaptured m)
    (hq : κb.scope.runtimeClass = some name)
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ κb) x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hb : Framed entry n) (hs : StateOk κb Γb Ib n) :
    StateOk (returnScopeCtx κ κb) Γ I (popMethodFrame n) := by
  obtain ⟨_, scope⟩ := hs.classRuntime name hq
  exact restore_main_state hm ht ha hr hw hcl hk (pop_framed hm.frameInRange.2 hp hb)
    (pop_currentFrame hm.frameInRange hb) (pop_envOk hm hp hu hb hΓ) scope.phase hs

theorem runSpec {name : String} {body : Ratchet.Expr} {τ : Ty}
    (hm : StateOk κ Γ I m) (hp : Framed m published)
    (ht : ReframeFO (returnScopeCtx κ κb) I) (ha : κ.asms = [])
    (hr : κ.scope.runtimeMain = true) (hw : κb.pos.mainWorld = true)
    (hcl : κ.scope.runtimeClass = none) (hq : κb.scope.runtimeClass = some name)
    (hk : ∀ x, constGet? κb x = constGet? (returnScopeCtx κ κb) x)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) (hτ : FirstOrder τ = true)
    (hb : RunSpec entry (evalFrom entry body) Γb τ κb Ib) :
    RunSpec m (pushK [.frameK m.frames.size] (evalFrom entry body)) Γ τ (returnScopeCtx κ κb) I := by
  have hu : RootUncaptured m := by
    unfold RootUncaptured
    rw [rootFrame_eq_currentFrame hm.frameInRange.1]
    exact (hm.runtime hr).captured
  exact (methodFrame_runSpec (m := published) hm.frameInRange.2 rfl hτ hb
    (fun n v result => pop_main_state hm hp ht ha hr hw hcl hu hq hk hΓ result.1
      (result.2.2 v rfl))).rebase hp

#print axioms pop_framed
#print axioms pop_envOk
#print axioms pop_main_state
#print axioms runSpec
end Ratchet.Denote.Typed.ClassActivation
