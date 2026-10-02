import Denote.Rules.Iterator.ReadReturn
import Denote.Rules.Closure.ReturnEnv

/-! Merge body and caller types after both iterator activations are popped.
Physical capture ownership and parameter shadowing are the same as for direct calls. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem iterator_return_env {m n : Machine} {f : RubyCore.Frame}
    {shadow names : List String} {Γ Γb : Env}
    (hl : FrameInRange (popMethodFrame m)) (hu : RootUncaptured (popMethodFrame m))
    (hc : f.captured = some ((popMethodFrame m).stack.headD 0))
    (hd : CaptureSlots names (withoutNames shadow Γb) (popMethodFrame m))
    (hf : ∀ x, f.locals.any (·.1 == x) = shadow.contains x)
    (h : Framed (pushMethodFrame m f) n) (he : EnvOk Γ (popMethodFrame m)) (hb : EnvOk Γb n)
    (hal : (m.frames.getD ((popMethodFrame m).stack.headD 0) default).localAlias = none)
    (hfa : f.localAlias = none)
    (hbefore : ∀ x τ, envGet? Γ x = some τ → ∀ v, denM (stripAlias τ) (popMethodFrame m) v →
      denM (stripAlias τ) (popMethodFrame (popMethodFrame n)) v)
    (hafter : ∀ x τ, envGet? Γb x = some τ → names.contains x = true → ∀ v,
      denM (stripAlias τ) n v → denM (stripAlias τ) (popMethodFrame (popMethodFrame n)) v) :
    EnvOk (closureReturnEnv shadow names Γ Γb) (popMethodFrame (popMethodFrame n)) :=
  closure_return_env_of_reads hd
    (fun x hs => iterator_shadowed_read hl hu hc h x ((hf x).trans hs) hal hfa)
    (fun x hs hx => iterator_bound_read hl hu hc h x ((hf x).trans hs) hx hal hfa)
    (fun x hx => iterator_absent_read hl hu h x hx hal) he hb hbefore hafter

#print axioms iterator_return_env
end Ratchet.Denote.Typed
