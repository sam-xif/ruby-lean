import Denote.Rules.Method.BodyEntry
import Denote.Rules.Method.MethodResolve
import Denote.Sem.Closure.Reify

/-! Resolve installed user methods before entering a callback-capable body. Literal
blocks must also pass the runtime's lambda/proc/new interception, including overrides. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem SemMethod.topInvoke {κ : Ctx} {Γ Γm : Env} {I τ : Ty} {decl : Defn}
    {cb : CheckedCallback κ Γ I} {m : Machine} {cl : Closure} {o : ObjId}
    (hbody : SemMethod cb ⟨"Object", "Object", decl.name, false⟩ [] decl.body τ Γm)
    (hm : StateOk κ Γ I m) (hk : m.kont = []) (ht : FirstOrder τ = true)
    (hp : decl.params = []) (hd : decl ∈ κ.defs)
    (hc : cl.captured = some (m.stack.headD 0))
    (hslots : CaptureSlots cb.names (withoutNames (cb.params.map (·.1) ++ cl.locals) cb.out) m)
    (hproc : (m.heap.get o).payload = .proc cl) (hcode : ClosureMatches cb.code cl) :
    StepSpec m Γ τ (Interp.invoke m m.currentFrame.self .implicit decl.name [] (some (.ref o)) []) κ I := by
  have ready := hm.runtime cb.mainRuntime
  obtain ⟨md, hl, hparams, he, hu, hmcode⟩ := defsOk_lookup hm.defs hd ready.chain
  have h := hbody.call0 hm hk ht (by simpa only [hp, toRubyParams] using hparams) he
    (hmcode.owner.trans ready.owner.symm) (hmcode.cref.trans ready.cref.symm)
    hmcode.superName hmcode.captured hmcode.declared hc hslots hproc hcode
  rw [ready.self] at h ⊢
  rw [invoke_ordinary_userMethod ready.payload hl hmcode.builtin hu hmcode.fromPrelude rfl
    (by simp [ready.chain, Interp.crubyShadow]; rfl)]
  exact h

/-- Installed ordinary methods shadow Kernel's lambda/proc and the main receiver cannot
be a Class/Proc/Hash allocator. The new branch still checks the post-allocation lookup. -/
theorem finishSend_main_userBlock {m : Machine} {name : String} {md md' : MethodDef}
    {owner owner' : ObjId} (ps : List RubyCore.Param) (locals : List String) (body : RubyCore.Expr)
    (hl : lookup m.heap (.ref Boot.mainId) name = some (owner, md))
    (hb : md.builtin = none) (hu : md.undefined = false)
    (hl' : lookup (reifiedMachine m ps locals body false).heap (.ref Boot.mainId) name = some (owner', md'))
    (hb' : md'.builtin = none) :
    Interp.finishSend m (.ref Boot.mainId) .implicit name [] (.lit ps locals body) =
      Interp.invoke (reifiedMachine m ps locals body false) (.ref Boot.mainId)
        .implicit name [] (some (.ref m.heap.objs.size)) [] := by
  rw [lookup_eq_methodOn] at hl hl'
  unfold Interp.finishSend
  rw [hl]
  simp only [hb, hu, Option.isNone_none, Bool.not_false, Bool.and_true, Bool.not_true,
    Bool.and_false, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, Bool.true_and, reifyBlock_eq]
  simp only [show (Boot.mainId == Boot.procId) = false from rfl,
    show (Boot.mainId == Boot.hashId) = false from rfl,
    show (Boot.mainId == Boot.classId) = false from rfl,
    show (Boot.mainId == Boot.moduleId) = false from rfl,
    Bool.false_or, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  by_cases hn : name = "new"
  · subst name
    simp only [beq_self_eq_true, ↓reduceIte]
    simp only [hl', hb', Option.isNone_none, ↓reduceIte]
  · simp [hn]

theorem SemMethod.topFinishBlock {κ : Ctx} {Γ Γm : Env} {I τ : Ty} {decl : Defn}
    {cb : CheckedCallback κ Γ I} {m : Machine}
    (hbody : SemMethod cb ⟨"Object", "Object", decl.name, false⟩ [] decl.body τ Γm)
    (hm : StateOk κ Γ I m) (hk : m.kont = []) (ht : FirstOrder τ = true)
    (hp : decl.params = []) (hd : decl ∈ κ.defs) (hlam : cb.code.lam = false)
    (hslots : CaptureSlots cb.names (withoutNames (cb.params.map (·.1) ++ cb.code.locals) cb.out) m) :
    StepSpec m Γ τ (Interp.finishSend m m.currentFrame.self .implicit decl.name []
      (.lit (toRubyParams cb.code.params) cb.code.locals (toRuby cb.code.body))) κ I := by
  let ps := toRubyParams cb.code.params
  let ls := cb.code.locals
  let body := toRuby cb.code.body
  let entry := reifiedMachine m ps ls body false
  have hs : StateOk κ Γ I entry := reified_state hm ps ls body false
  have ready := hm.runtime cb.mainRuntime
  have ready' := hs.runtime cb.mainRuntime
  obtain ⟨md, hl, _, _, hu, hcode⟩ := defsOk_lookup hm.defs hd ready.chain
  obtain ⟨md', hl', _, _, _, hcode'⟩ := defsOk_lookup hs.defs hd ready'.chain
  rw [ready.self, finishSend_main_userBlock ps ls body hl hcode.builtin hu hl' hcode'.builtin]
  have h := hbody.topInvoke hs hk ht hp hd (cl := reifiedClosure m ps ls body false)
    (o := m.heap.objs.size) rfl hslots (by simp only [entry, reifiedMachine, pushHeap_get_self])
    ⟨rfl, rfl, rfl, hlam.symm⟩
  rw [ready'.self] at h
  exact h.rebase (.of_ext (reified_ext hm ps ls body false))

#print axioms SemMethod.topInvoke
#print axioms finishSend_main_userBlock
#print axioms SemMethod.topFinishBlock
end Ratchet.Denote.Typed
