import Denote.Typed.InstancePublish
import Denote.Sem.InstanceSiteWrite

/-! Keep instance entry facts alongside the actual definition/table publication.
The site is still explicit; this is not an admission from a signature or an outgoing
site assumed as a premise. -/
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

/-- Publish full state and the derived site in one real step. The class-body proof must
still supply constructor/nested contracts and check the annotated method body. -/
theorem step_scoped_instance_world {κ : Ctx} {Γ : Env} {I : Ty} {c : Cls} {d : Defn}
    {m : Machine} (hm : StateOk κ Γ I m) (hr : κ.scope.runtimeClass = some c.name)
    (site : InstanceSite κ c.name m.currentFrame.defmod m.heap)
    (ht : ReframeFO κ I) (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (ha : κ.asms = []) (hc : ClassesOk [c] m)
    (hobj : m.currentFrame.defmod ≠ Boot.objectId)
    (hf : ∀ old ∈ c.methods, old.name ≠ d.name)
    (hs : ∀ old ∈ κ.classes, classNamed? m.heap old.name = some m.currentFrame.defmod →
      ∀ method ∈ old.methods, method.name ≠ d.name)
    (hmiss : "method_missing" ≠ d.name) (hquiet : "method_added" ≠ d.name)
    (hnested : NestedClassesOk (classWithMethod c d :: κ.classes)
      (installMethod m d.name (toRubyParams d.params) (toRuby d.body)))
    (hdecl : DeclClassOk (instanceDeclCtx κ c d)
      (installMethod m d.name (toRubyParams d.params) (toRuby d.body)))
    (hctl : m.ctl = .eval (.def' d.name (toRubyParams d.params) (toRuby d.body))) :
    ∃ n, Interp.stepFn m = .next n ∧ StateOk (instanceDeclCtx κ c d) Γ I n ∧
      InstanceSite (instanceDeclCtx κ c d) c.name m.currentFrame.defmod n.heap := by
  obtain ⟨n, hn, hstate⟩ := step_scoped_instance_state hm hr ht hΓ ha hc hobj hf hs
    hmiss hquiet hnested hdecl hctl
  obtain ⟨k, ready⟩ := hm.classRuntime c.name hr
  have hquiet' : DefHookQuiet (installMethod m d.name (toRubyParams d.params) (toRuby d.body)) :=
    defHookQuiet_install hquiet (scoped_defHookQuiet ready)
  have he := step_def_install hctl hquiet'
  rw [hn] at he
  cases StepResult.next.inj he
  exact ⟨_, hn, hstate, instance_site_install site hquiet⟩

#print axioms instance_site_install
#print axioms step_scoped_instance_world
end Ratchet.Denote.Typed
