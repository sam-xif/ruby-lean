import Books.TypeSoundness.Rules.Method.BodyEntry
import Books.TypeSoundness.Rules.Method.MethodResolve
import Books.TypeSoundness.Conformance.Closure.Reify
import Books.TypeSoundness.Rules.Closure.Attached

/-! Resolve installed user methods before entering a callback-capable body. Literal
blocks must also pass the runtime's lambda/proc/new interception, including overrides. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

theorem invoke_ordinary_shadow {m : Machine} {o owner : ObjId} {site : SendSite}
    {name cname : String} {md : MethodDef} {args : List Value} {blk : Option Value}
    (ho : (m.heap.get o).payload = .none)
    (hl : lookup m.heap (.ref o) name = some (owner, md))
    (hb : md.builtin = none) (hu : md.undefined = false) (hp : md.fromPrelude = false)
    (hs : Interp.crubyShadow m.heap
      ((ancestors m.heap (classOf m.heap (.ref o))).takeWhile (· != owner)) name = some cname) :
    Interp.invoke m (.ref o) site name args blk [] =
      .unsupported s!"unmodeled builtin would shadow: {cname}#{name}" := by
  unfold Interp.invoke
  simp only [hl, Option.isNone, Bool.and_false, Bool.false_eq_true, ↓reduceIte, ho]
  simp only [Interp.invoke.invokeDispatch, hl, hu, hp, Bool.false_eq_true, ↓reduceIte,
    Interp.crubyResolvedShadow, hb, Option.any, hs]

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
  obtain ⟨md, hl, hparams, he, hu, hmcode⟩ := defsOk_lookup hm.defs hd ready
  have h := hbody.call0 hm hk ht (by simpa only [hp, toRubyParams] using hparams) he
    (hmcode.definee.trans ready.owner.symm) (hmcode.cref.trans ready.cref.symm)
    hmcode.superName hmcode.captured hmcode.declared hmcode.fromBlock hmcode.forTargets
    hc hslots hproc hcode
  rw [ready.self] at h ⊢
  cases hs : Interp.crubyShadow m.heap
      ((ancestors m.heap (classOf m.heap (.ref Boot.mainId))).takeWhile (· != Boot.objectId))
      decl.name with
  | none =>
    rw [invoke_ordinary_userMethod ready.payload hl hmcode.builtin hu hmcode.fromPrelude rfl hs]
    exact h
  | some cname =>
    rw [invoke_ordinary_shadow ready.payload hl hmcode.builtin hu hmcode.fromPrelude hs]
    trivial

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
  let M := attMachine m ps ls body
  have hs : StateOk κ Γ I M := att_state hm ps ls body
  have hfr : Framed m M := att_framed hm ps ls body
  have ready := hm.runtime cb.mainRuntime
  have ready' := hs.runtime cb.mainRuntime
  have hr0 := hm.frameInRange
  obtain ⟨md, hl, _, _, hu, hcode⟩ := defsOk_lookup hm.defs hd ready
  obtain ⟨md', hl', hparams', he', hu', hcode'⟩ := defsOk_lookup hs.defs hd ready'
  have hslots' : CaptureSlots cb.names (withoutNames (cb.params.map (·.1) ++ cb.code.locals) cb.out) M := by
    intro x τ hx
    rw [← hslots x τ hx]
    change frameBinds (pushDead _ _) (m.stack.headD 0) x = _
    exact congrArg (fun f : RubyCore.Frame => f.locals.any (·.1 == x))
      (pushDead_getD (m := attBase m ps ls body) (f := m.currentFrame) hr0.2)
  have hproc : (M.heap.get m.heap.objs.size).payload = .proc (litClosure m ps ls body false) := by
    rw [att_payload]; rfl
  have h := hbody.topInvoke hs rfl ht hp hd (cl := litClosure m ps ls body false)
    (o := m.heap.objs.size) rfl hslots' hproc ⟨rfl, rfl, rfl, hlam.symm, rfl, rfl⟩
  rw [ready'.self] at h
  have hclean : ∀ Y, Interp.invoke M (.ref Boot.mainId) .implicit decl.name []
      (some (.ref m.heap.objs.size)) [] = .next Y → RootClean Y := by
    intro Y hY
    cases hsh : Interp.crubyShadow M.heap
        ((ancestors M.heap (classOf M.heap (.ref Boot.mainId))).takeWhile (· != Boot.objectId))
        decl.name with
    | some cname =>
      rw [invoke_ordinary_shadow ready'.payload hl' hcode'.builtin hu' hcode'.fromPrelude hsh] at hY
      cases hY
    | none =>
    rw [invoke_ordinary_userMethod ready'.payload hl' hcode'.builtin hu' hcode'.fromPrelude rfl hsh,
      enterUserMethod_required_block _ _ _ _ [] [] _ (by simpa only [hp, toRubyParams, List.map_nil] using hparams')
        hcode'.captured hcode'.declared rfl hcode'.fromBlock hcode'.forTargets] at hY
    cases hY; exact hs.rootClean
  rw [lookup_eq_methodOn] at hl
  rw [ready.self, finishSend_attached_shadowed m _ .implicit decl.name hl hcode.builtin hu hk
    hm.rootClean, Proof.Root.invoke_frame _ (by intro k hk; simp at hk; subst hk; rfl)]
  cases hrun : Interp.invoke M (.ref Boot.mainId) .implicit decl.name []
      (some (.ref m.heap.objs.size)) [] with
  | next Y =>
    rw [hrun] at h
    have hY := hclean Y hrun
    change RunSpec m (Proof.pushRootK _ Y) _ _ _ _
    rw [Proof.pushRootK_quiescent _ Y hY.1 hY.2]
    exact RunSpec.bindAny (S := Y) h hs.rootClean hY
      (by intro k hk; simp at hk; subst hk; rfl)
      (fun a n hn => blockCallK_answer _ ht hfr hn)
  | unsupported r => trivial
  | done v n => rw [hrun] at h; exact h.elim
  | uncaught v n => rw [hrun] at h; exact h.elim
  | stuck r => rw [hrun] at h; exact h.elim

#print axioms SemMethod.topInvoke
#print axioms SemMethod.topFinishBlock
end Checker.Soundness.Typed
