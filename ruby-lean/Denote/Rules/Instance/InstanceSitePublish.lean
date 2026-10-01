import Denote.Rules.Instance.InstancePublish
import Denote.Sem.Instance.InstanceSiteWrite

/-! Keep instance entry facts in conformance across actual definition/table publication.
No signature certifies a body, and no outgoing site is assumed as a premise. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem instance_site_install {κ : Ctx} {cn : String} {k : ObjId} {m : Machine}
    {c : Cls} {d : Defn} (site : InstanceSite κ cn k m.heap)
    (hq : "method_added" ≠ d.name) :
    InstanceSite (instanceDeclCtx κ c d) cn k
      (installMethod m d.name (toRubyParams d.params) (toRuby d.body)).heap := by
  have hs := (site.reserveName d.name).methodWrite
    (cls := m.currentFrame.defmod) (md := definedMethod m d.name (toRubyParams d.params) (toRuby d.body))
    (by simp [nameFreeN, reserveNameCtx, Ctx.declared]) hq
  exact hs.recontext (fun _ hn => hn)

#print axioms instance_site_install
end Ratchet.Denote.Typed
