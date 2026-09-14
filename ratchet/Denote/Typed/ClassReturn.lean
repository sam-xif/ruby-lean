import Denote.Sem.ClassFrame
import Denote.Typed.MethodReturn

/-! Class-body return reuses uncaptured-frame restoration. Heap publication is anchored
before class allocation; the body's framing contract starts after entry. Both are needed. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote
open RubyCore.Proof.Judgment (freshClsHeap freshClsMachine freshModFrame)

variable {κ : Ctx} {Γ : Env} {I : Ty} {m n : Machine}
  {name : String} {e : ObjId} {body : RubyCore.Expr}
private def publishedClass (m : Machine) (name : String) (e : ObjId) : Machine :=
  { m with heap := freshClsHeap m.heap Boot.objectId name name e }
local notation "published" => publishedClass m name e
local notation "frame" => freshModFrame m.heap.objs.size m.currentFrame.cref
local notation "entry" => freshClsMachine m Boot.objectId m.currentFrame.cref name name e body

private theorem pushed_framed : Framed (pushMethodFrame published frame) entry :=
  .of_heap_stack rfl rfl (.of_eq rfl rfl)

theorem class_pop_framed (hm : StateOk κ Γ I m)
    (hn : constOwn m.heap Boot.objectId name = none)
    (he : (m.heap.get Boot.objectId).eigen = some e) (hb : Framed entry n) :
    Framed m (popMethodFrame n) := by
  have hp : Framed m published := .of_freshClass hm hn he rfl rfl (.of_eq rfl rfl)
  exact hp.trans (method_pop_framed hm.frameInRange.2 rfl (pushed_framed.trans hb))

theorem class_pop_getLocal (hl : m.stack.headD 0 < m.frames.size) (hu : RootUncaptured m)
    (hb : Framed entry n) (x : String) : (popMethodFrame n).getLocal x = m.getLocal x := by
  have hp := method_pop_getLocal (m := published) (f := frame) hl hu rfl (pushed_framed.trans hb) x
  rw [getLocal_uncaptured (m := published) hu] at hp
  rw [getLocal_uncaptured hu]
  exact hp

theorem class_pop_envOk (hm : StateOk κ Γ I m) (hu : RootUncaptured m)
    (hn : constOwn m.heap Boot.objectId name = none)
    (he : (m.heap.get Boot.objectId).eigen = some e) (hb : Framed entry n)
    (ht : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true) : EnvOk Γ (popMethodFrame n) := by
  have hp := class_pop_framed hm hn he hb
  have hv := class_pop_getLocal hm.frameInRange.2 hu hb
  refine ⟨?_, ?_⟩
  · intro x τ hx
    obtain ⟨z, hz⟩ := envGet?_mem hx
    obtain ⟨hd, ha⟩ := hm.env.1 x τ hx
    refine ⟨?_, ?_⟩
    · rw [hv]; exact hp.firstOrder _ (ht (z, τ) hz) _ hd
    · intro y ρ hy; rw [hv, hv]; exact ha y ρ hy
  · intro x hx
    rw [hv]; exact hm.env.2 x hx

#print axioms class_pop_framed
#print axioms class_pop_getLocal
#print axioms class_pop_envOk
end Ratchet.Denote.Typed
