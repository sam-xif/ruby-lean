import Denote.Rules.Method.MethodKw
import Denote.Rules.Expr.ArrayCompact

/-! Top-level methods with required positionals and a trailing named `*rest`. The surplus
arguments are allocated as a fresh Array before the frame is pushed, and bound after it. -/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem classifyFull_rest (names : List String) (r : String) :
    Interp.classifyFull (names.map RubyCore.Param.req ++ [.rest (some r)]) =
      some ⟨names, [], some r, [], [], none, none, []⟩ := by
  have hnames : names.zipIdx.map (fun p => RubyCore.Param.req p.1) =
      names.map RubyCore.Param.req := by
    change List.map (RubyCore.Param.req ∘ Prod.fst) _ = _
    rw [← List.map_map, List.zipIdx_map_fst]
  have hd : names.dropWhile (fun _ => true) = [] := by
    clear hnames
    induction names <;> simp_all [List.dropWhile]
  have ht : names.takeWhile (fun _ => true) = names := by
    clear hnames hd
    induction names <;> simp_all [List.takeWhile]
  unfold Interp.classifyFull
  simp [List.flatMap_append, List.zipIdx_append, List.reverse_append, Function.comp_def,
    List.takeWhile_append_of_pos, List.dropWhile_append_of_pos, List.filterMap_map,
    List.flatMap_map, hnames, hd, ht, List.takeWhile_map, List.dropWhile_map,
    List.filterMap_append, ← List.map_eq_flatMap, List.zipIdx_map, List.map_map]

/-- The surplus is allocated first, the frame predeclares `rest` as nil, and the
binding phase stores the Array before the body runs. -/
theorem enterUserMethod_rest (m : Machine) (recv : Value) (name : String)
    (md : MethodDef) (names : List String) (r : String) (args : List Value)
    (hp : md.params = names.map RubyCore.Param.req ++ [.rest (some r)])
    (hc : md.capturedFrame = none) (hd : md.declared = [])
    (ha : names.length ≤ args.length)
    (hblock : md.fromBlock = false) (hfor : md.forTargets = none) :
    Interp.enterUserMethod m recv name md args none =
      .next (Interp.withCtl
        (({ pushMethodFrame (Builtins.allocArr m (args.drop names.length).toArray).2
              (requiredFrame recv name md (names ++ [r]) (args.take names.length ++ [.nil])) with
            kont := .frameK m.frames.size :: m.kont } : Machine).setLocal r
          (Builtins.allocArr m (args.drop names.length).toArray).1)
        (.eval md.body)) := by
  have hf : (names.zip (args.take names.length)).filter (fun _ => true) =
      names.zip (args.take names.length) := List.filter_eq_self.mpr (fun _ _ => rfl)
  have hz : (names ++ [r]).zip (args.take names.length ++ [Value.nil]) =
      names.zip (args.take names.length) ++ [(r, .nil)] :=
    List.zip_append (by simp [Nat.min_eq_left ha])
  have htd : (args.drop names.length).take (args.length - names.length) = args.drop names.length :=
    List.take_of_length_le (by simp)
  unfold Interp.enterUserMethod
  rw [hp, classifyFull_rest]
  simp [Interp.appendKwHash, hc, hd, ha, requiredFrame, pushMethodFrame,
    Interp.withKont, hp, hblock, hfor, hf, hz, Builtins.allocArr, Heap.alloc, htd]
  done

theorem setLocal_withKont (e : Machine) (K : List Kont) (x : String) (v : Value) :
    ({ e with kont := K } : Machine).setLocal x v = { e.setLocal x v with kont := K } :=
  setLocal_reCtl e e.ctl K x v

theorem rest_method_runSpec {κ : Ctx} {Γ Γb : Env} {I τ σ : Ty} {m : Machine}
    {md : MethodDef} {name r : String} {ps : List SigParam} {args : List Value}
    {e : Ratchet.Expr} {fr : Option Ratchet.Frame}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hkont : m.kont = [])
    (hp : md.params = (ps.map (·.1)).map RubyCore.Param.req ++ [.rest (some r)])
    (hcap : md.capturedFrame = none) (hdecl : md.declared = []) (hbody : md.body = toRuby e)
    (hblock : md.fromBlock = false) (hfor : md.forTargets = none)
    (hss : md.superScope = none) (hown : md.definee.getD md.owner = md.owner)
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hσ : FirstOrder σ = true)
    (hτ : FirstOrder τ = true) (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hscope : ∀ names vs, frameScope (requiredFrame m.currentFrame.self name md names vs) =
      frameScope m.currentFrame)
    (hk : ∀ x, constGet? (κ.withFrame fr) x = constGet? κ x)
    (hframe : ∀ names vs, FrameOk fr (pushMethodFrame (Builtins.allocArr m (args.drop ps.length).toArray).2
      (requiredFrame m.currentFrame.self name md names vs)))
    (hb : SemSafeCtxA (κ.withFrame fr) (ps ++ [(r, .arrayOf σ)]) I e τ (κ.withFrame fr) Γb I)
    (hafter : envAfter ps r (.arrayOf σ) = ps ++ [(r, .arrayOf σ)])
    (hkill : killClosOverSpine I r (.arrayOf σ) = I)
    (hcapS : capStale r (.arrayOf σ) (.arrayOf σ) = false)
    (hctx : capStaleCtx r (.arrayOf σ) (κ.withFrame fr) = false)
    (hlen : ps.length ≤ args.length) (hargs : DenAll (ps.map (·.2)) m (args.take ps.length))
    (hrest : ∀ x ∈ args.drop ps.length, denM σ m x) :
    ∃ next, Interp.enterUserMethod m m.currentFrame.self name md args none = .next next ∧
      RunSpec m next Γ τ κ I := by
  let M := (Builtins.allocArr m (args.drop ps.length).toArray).2
  let rv := (Builtins.allocArr m (args.drop ps.length).toArray).1
  have hres := array_alloc_result hm (args.drop ps.length) hrest
  have hM : StateOk κ Γ I M := hres.2.2 rv rfl
  have hrv : denM (.arrayOf σ) M rv := hres.2.1
  have hcur : M.currentFrame = m.currentFrame := rfl
  have hargs' : DenAll (ps.map (·.2)) M (args.take ps.length) :=
    denAll_framed (fun t ht => by
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp ht; exact (hps p hp').1) hres.1 hargs
  let f := requiredFrame M.currentFrame.self name md (ps.map (·.1) ++ [r])
    (args.take ps.length ++ [.nil])
  let entry := pushMethodFrame M f
  have hscope' : ∀ names vs, frameScope (requiredFrame M.currentFrame.self name md names vs) =
      frameScope M.currentFrame := fun names vs => hscope names vs
  have hsc := hscope' (ps.map (·.1) ++ [r]) (args.take ps.length ++ [.nil])
  have he : StateOk (κ.withFrame fr) ps I entry :=
    method_enter_state hM ht ha (congrArg FrameScope.self hsc)
      (congrArg FrameScope.blk hsc) (congrArg FrameScope.cref hsc)
      (congrArg FrameScope.defmod hsc) (congrArg FrameScope.captured hsc)
      (fun _ => by simp only [defaultDefVis, currentFrame_pushMethodFrame, f, requiredFrame]; rfl) hk
      (optOmitted_envOk M _ name md ps r (args.take ps.length) (by simp [Nat.min_eq_left hlen])
        hargs' hps)
      (hframe _ _) rfl ⟨hss, hown.symm⟩
      (congrArg FrameScope.libraryOrigin hsc)
      (congrArg FrameScope.definitionFrame hsc)
  have hrvE : denM (.arrayOf σ) entry rv :=
    (denM_heap_only (m₁ := M) (m₂ := entry) (by simpa [FirstOrder] using hσ) rfl).mp hrv
  have hs : StateOk (κ.withFrame fr) (ps ++ [(r, .arrayOf σ)]) I (entry.setLocal r rv) := by
    have h := StateOk_setLocal he hrvE hcapS hctx (ρ := .arrayOf σ) (by simp [stripAlias])
      (by intro y ρ hy; cases hy)
    rw [show envSet (killClosOver (killAliasesTo ps r) r (.arrayOf σ)) r (.arrayOf σ) =
      envAfter ps r (.arrayOf σ) from rfl, hafter, hkill] at h
    exact h
  have hbodyRun : RunSpec entry (evalFrom (entry.setLocal r rv) e) Γb τ
      (κ.withFrame fr) I :=
    RunSpec.rebase (hb _ hs) (Framed_setLocal entry r rv (by
      rw [← currentFrame_headD he.frameInRange.1]; exact he.localAlias))
  have hu : RootUncaptured M := by
    unfold RootUncaptured
    rw [rootFrame_eq_currentFrame hM.frameInRange.1]
    exact (congrArg FrameScope.captured (hscope' [] [])).symm
  have hrun := methodFrame_runSpec_at hM.frameInRange.2 (f := f) rfl hτ hbodyRun
    (fun n v hr => method_pop_state hM ht ha hu rfl hsc hk hΓ hr.1 (hr.2.2 v rfl))
    hM.rootClean hm.rootClean
  refine ⟨_, ?_, hrun.rebase hres.1⟩
  rw [enterUserMethod_rest m _ name md (ps.map (·.1)) r args hp hcap hdecl (by simpa using hlen)
    hblock hfor, setLocal_withKont]
  simp only [Interp.withCtl, pushK, evalFrom, hkont, hbody, List.nil_append, List.length_map]
  rfl

#print axioms rest_method_runSpec
theorem denAll_split {m : Machine} : ∀ {xs ys : List Ty} {vs : List Value},
    DenAll (xs ++ ys) m vs → DenAll xs m (vs.take xs.length) ∧ DenAll ys m (vs.drop xs.length)
  | [], _, _, h => by simpa using h
  | _ :: _, _, [], h => by cases h
  | x :: xs, ys, v :: vs, h => by
    obtain ⟨h1, h2⟩ := h
    obtain ⟨a, b⟩ := denAll_split h2
    exact ⟨⟨h1, a⟩, by simpa using b⟩

theorem denAll_replicate {m : Machine} {σ : Ty} : ∀ {k : Nat} {ws : List Value},
    DenAll (List.replicate k σ) m ws → ∀ w ∈ ws, denM σ m w
  | 0, [], _, w, hw => by cases hw
  | 0, _ :: _, h, _, _ => by cases h
  | _ + 1, [], h, _, _ => by cases h
  | k + 1, v :: vs, h, w, hw => by
    obtain ⟨h1, h2⟩ := h
    rcases List.mem_cons.mp hw with rfl | hw
    · exact h1
    · exact denAll_replicate h2 w hw

theorem toRubyParams_rest (ps : List SigParam) (r : String) :
    toRubyParams (ps.map (fun p => Ratchet.Param.req p.1) ++ [.rest (some r)]) =
      (ps.map (·.1)).map RubyCore.Param.req ++ [.rest (some r)] := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simpa only [List.map_cons, List.cons_append, toRubyParams, toRubyParam] using
      congrArg (RubyCore.Param.req p.1 :: ·) ih

theorem top_rest_method_stepSpec {κ : Ctx} {Γ Γb : Env} {I τ σ : Ty} {m : Machine}
    {decl : Defn} {args : List Value} {ps : List SigParam} {r : String}
    (hparams : decl.params = ps.map (fun p => Ratchet.Param.req p.1) ++ [.rest (some r)])
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false) (hσ : FirstOrder σ = true)
    (hτ : FirstOrder τ = true)
    (hbody : SemSafeCtxA (κ.withFrame (some ⟨"Object", "Object", decl.name, false⟩))
      (ps ++ [(r, .arrayOf σ)]) I decl.body τ
      (κ.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) Γb I)
    (hafter : envAfter ps r (.arrayOf σ) = ps ++ [(r, .arrayOf σ)])
    (hkill : killClosOverSpine I r (.arrayOf σ) = I)
    (hcapS : capStale r (.arrayOf σ) (.arrayOf σ) = false)
    (hctx : capStaleCtx r (.arrayOf σ) (κ.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) = false)
    (hm : StateOk κ Γ I m) (hd : decl ∈ κ.defs)
    (ht : ReframeFO κ I) (ha : κ.asms = []) (hc : κ.consts = [])
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hkont : m.kont = [])
    (hlen : ps.length ≤ args.length) (hargs : DenAll (ps.map (·.2)) m (args.take ps.length))
    (hrest : ∀ x ∈ args.drop ps.length, denM σ m x)
    (hruntime : κ.scope.runtimeMain = true) (hblock : κ.blockTy = none) :
    StepSpec m Γ τ
      (Interp.finishSend m m.currentFrame.self .implicit decl.name args .none) κ I := by
  have ready := hm.runtime hruntime
  have hblk : m.currentFrame.blk = none := by simpa only [BlockTyOk, hblock] using hm.blockTy
  obtain ⟨md, hl, hp, hb, hu, hcode⟩ := defsOk_lookup hm.defs hd ready
  have hres := array_alloc_result hm (args.drop ps.length) hrest
  have readyM := (hres.2.2 _ rfl).runtime hruntime
  have hpr : toRubyParams decl.params = (ps.map (·.1)).map RubyCore.Param.req ++ [.rest (some r)] := by
    rw [hparams]; exact toRubyParams_rest ps r
  cases hs : Interp.crubyShadow m.heap
      ((ancestors m.heap (classOf m.heap (.ref Boot.mainId))).takeWhile (· != Boot.objectId))
      decl.name with
  | some cname =>
    rw [ready.self, finishSend_ordinary_shadow ready.payload hl hcode.builtin hu
      hcode.fromPrelude hs]
    trivial
  | none =>
    have hdef : md.definee.getD Boot.objectId = Boot.objectId := by
      simpa only [hcode.owner] using hcode.definee
    obtain ⟨next, he, hr⟩ := rest_method_runSpec (name := decl.name) (σ := σ)
      (fr := some ⟨"Object", "Object", decl.name, false⟩) (e := decl.body)
      hm ht ha hkont (hp.trans hpr)
      hcode.captured hcode.declared hb hcode.fromBlock hcode.forTargets hcode.superScope
      (by rw [hcode.owner]; exact hdef) hps hσ hτ hΓ
      (fun names vs => by simp [frameScope, requiredFrame, hcode.owner, hcode.cref,
        hdef, hcode.fromPrelude, ready.owner, ready.cref, ready.captured,
        ready.origin, hm.localAlias, hblk, hcode.definitionFrame, ready.defFrame])
      (fun x => (constGet?_empty (κ := κ.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) hc x).trans
        (constGet?_empty hc x).symm)
      (fun names vs => by
        simp only [FrameOk, Frame.recvTy, Bool.false_eq_true, ↓reduceIte, denM,
          currentFrame_pushMethodFrame, requiredFrame, hcode.superName, Option.getD_none]
        exact ⟨trivial, by rw [ready.self]; exact readyM.object, trivial⟩)
      hbody hafter hkill hcapS hctx hlen hargs hrest
    rw [ready.self] at he ⊢
    rw [finishSend_ordinary_userMethod ready.payload hl hcode.builtin hu hcode.fromPrelude hs, he]
    exact hr

#print axioms top_rest_method_stepSpec
theorem SemSafeCtxA.callSigRest {κ κ' : Ctx} {Γ Γ' Γb : Env} {I I' τ σ : Ty}
    {decl : Defn} {ps : List SigParam} {r : String} {args : List Ratchet.Expr} {tys : List Ty}
    (hparams : decl.params = ps.map (fun p => Ratchet.Param.req p.1) ++ [.rest (some r)])
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false) (hσ : FirstOrder σ = true)
    (hτ : FirstOrder τ = true)
    (hbody : SemSafeCtxA (κ'.withFrame (some ⟨"Object", "Object", decl.name, false⟩))
      (ps ++ [(r, .arrayOf σ)]) I' decl.body τ
      (κ'.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) Γb I')
    (hafter : envAfter ps r (.arrayOf σ) = ps ++ [(r, .arrayOf σ)])
    (hkill : killClosOverSpine I' r (.arrayOf σ) = I')
    (hcapS : capStale r (.arrayOf σ) (.arrayOf σ) = false)
    (hctx : capStaleCtx r (.arrayOf σ) (κ'.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) = false)
    (hargs : SemAllCtxA κ Γ I args tys κ' Γ' I')
    (htys : tys = ps.map (·.2) ++ List.replicate (tys.length - ps.length) σ)
    (hd : decl ∈ κ'.defs)
    (hstart : κ.scope.runtimeMain = true) (hruntime : κ'.scope.runtimeMain = true)
    (hself : κ'.selfTy = none) (hblock : κ'.blockTy = none) (hconst : κ'.consts = [])
    (hasms : κ'.asms = []) (hI : FirstOrder I' = true)
    (hΓ : ∀ p ∈ Γ', FirstOrder (stripAlias p.2) = true) :
    SemSafeCtxA κ Γ I (.send none decl.name args none) τ κ' Γ' I' := by
  intro m hm
  let start := evalFrom m (.send none decl.name args none)
  have hfinish (n' : Machine) (hn : StateOk κ' Γ' I' n') (hk : n'.kont = [])
      (vs : List Value) (hv : DenAll tys n' vs) :
      StepSpec n' Γ' τ (Interp.finishSend n' (.ref Boot.mainId) .implicit decl.name vs .none) κ' I' := by
    rw [htys] at hv
    have hsp := denAll_split hv
    have hl := denAll_length hv
    have h := top_rest_method_stepSpec hparams hps hσ hτ hbody hafter hkill hcapS hctx hn hd
      (ReframeFO.empty hI hself hblock hconst) hasms hconst hΓ hk
      (by rw [hl]; simp) (by simpa using hsp.1)
      (denAll_replicate (by simpa using hsp.2)) hruntime hblock
    simpa only [(hn.runtime hruntime).self] using h
  apply RunSpec.rebase (middle := start) ?_ (Framed_reCtl _ _ [])
  apply RunSpec.of_stepSpec (by rfl)
  have hh := hargs.startArgs (m := start) (recv := .ref Boot.mainId) (name := decl.name)
    (StateOk_reCtl hm _ []) rfl [] []
    (by
      intro τ' hτ'
      simp only [List.nil_append] at hτ'
      rw [htys] at hτ'
      rcases List.mem_append.mp hτ' with h | h
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
        exact (hps p hp).1
      · rw [List.eq_of_mem_replicate h]; exact hσ)
    trivial hfinish
  have hselfm : start.currentFrame.self = .ref Boot.mainId := (hm.runtime hstart).self
  change StepSpec start Γ' τ
    (Interp.startArgs start start.currentFrame.self .implicit decl.name [] (toRubyList args) .none) κ' I'
  rw [hselfm]
  exact hh

theorem SemSafeCtxA.defDeclRest {κ : Ctx} {Γ Γb : Env} {I τ σ : Ty} {d : Defn}
    {ps : List SigParam} {r : String}
    (_hparams : d.params = ps.map (fun p => Ratchet.Param.req p.1) ++ [.rest (some r)])
    (_hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false) (_hσ : FirstOrder σ = true)
    (_hret : FirstOrder τ = true)
    (_hbody : SemSafeCtxA (topBodyCtx κ d) (ps ++ [(r, .arrayOf σ)]) I d.body τ (topBodyCtx κ d) Γb I)
    (hruntime : κ.scope.runtimeMain = true) (hclasses : topDeclClassesB κ d.name = true)
    (hself : κ.selfTy = none) (hblock : κ.blockTy = none) (hconst : κ.consts = [])
    (hasms : κ.asms = []) (hI : FirstOrder I = true)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hfresh : ∀ old ∈ κ.defs, old.name ≠ d.name)
    (hmiss : "method_missing" ≠ d.name) (hquiet : "method_added" ≠ d.name) :
    SemSafeCtxA κ Γ I (.def' d.name d.params d.body) .sym (topDeclCtx κ d) Γ I :=
  top_definition hruntime hclasses hself hblock hconst hasms hI hΓ hfresh hmiss hquiet

#print axioms SemSafeCtxA.callSigRest
#print axioms SemSafeCtxA.defDeclRest
end Ratchet.Denote.Typed
