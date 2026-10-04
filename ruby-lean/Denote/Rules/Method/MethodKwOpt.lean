import Denote.Rules.Method.MethodKw

/-! Top-level methods whose parameters are required keywords followed by one keyword with
a default. A call passes the required keywords in order, then optionally the last one;
an omitted default runs in the callee frame under `optDefK`, as a positional default does. -/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

abbrev keyParam (p : String × Option RubyCore.Expr) : RubyCore.Param := .key p.1 p.2

theorem classifyFull_keys (ks : List (String × Option RubyCore.Expr)) (hne : ks ≠ []) :
    Interp.classifyFull (ks.map keyParam) =
      some ⟨[], [], none, [], ks, none, none, []⟩ := by
  rcases ks with _ | ⟨k, ks⟩
  · exact absurd rfl hne
  have hnames : ((k :: ks).zipIdx).map (fun p => keyParam p.1) = (k :: ks).map keyParam := by
    change List.map (keyParam ∘ Prod.fst) _ = _
    rw [← List.map_map, List.zipIdx_map_fst]
  have hd : ks.dropWhile (fun _ => true) = [] := by
    clear hnames hne; induction ks <;> simp_all [List.dropWhile]
  have ht : ks.takeWhile (fun _ => true) = ks := by
    clear hnames hd hne; induction ks <;> simp_all [List.takeWhile]
  obtain ⟨x, xs, hr⟩ : ∃ x xs, (k :: ks).reverse = x :: xs := by
    cases h : (k :: ks).reverse with
    | nil => simp at h
    | cons x xs => exact ⟨x, xs, rfl⟩
  have hr2 : List.map keyParam ks.reverse ++ [keyParam k] = keyParam x :: List.map keyParam xs := by
    have := congrArg (List.map keyParam) hr
    simpa using this
  unfold Interp.classifyFull
  simp only [List.flatMap_map, ← List.map_eq_flatMap, List.zipIdx_map,
    List.map_map, List.filterMap_map, Function.comp_def, Prod.map, keyParam]
  simp only [keyParam] at hnames hr2
  simp only [hnames]
  simp [← List.map_reverse, hr, hr2, List.takeWhile_map, List.dropWhile_map,
    Function.comp_def, hd, ht, List.filterMap_map, List.dropWhile, List.takeWhile]

theorem kwLookup_kwOf_none {names : List String} {vals : List Value} {n : String}
    (hn : n ∉ names) : Interp.kwLookup (kwOf names vals) n = none := by
  unfold Interp.kwLookup
  rw [Option.map_eq_none_iff, List.find?_eq_none]
  intro p hp
  simp only [kwOf, List.mem_map] at hp
  obtain ⟨⟨a, b⟩, hq, rfl⟩ := hp
  have ha := (List.of_mem_zip hq).1
  have hne : a ≠ n := fun h => hn (h ▸ ha)
  simp [hne]

theorem kwLookup_append_left {names : List String} {vals : List Value}
    {rest : List (Value × Value)} {x : String}
    (h : (Interp.kwLookup (kwOf names vals) x).isSome = true) :
    Interp.kwLookup (kwOf names vals ++ rest) x = Interp.kwLookup (kwOf names vals) x := by
  unfold Interp.kwLookup at h ⊢
  rw [List.find?_append]
  revert h
  generalize List.find? _ (kwOf names vals) = o
  intro h
  cases o with
  | none => cases h
  | some p => rfl

theorem kwLookup_append_last {names : List String} {vals : List Value} {n : String} {v : Value}
    (hn : n ∉ names) : Interp.kwLookup (kwOf names vals ++ [(.sym n, v)]) n = some v := by
  have h := kwLookup_kwOf_none (vals := vals) hn
  unfold Interp.kwLookup at h ⊢
  rw [Option.map_eq_none_iff] at h
  rw [List.find?_append, h]
  simp

/-- All keywords supplied: the frame has the required-positional shape. -/
theorem enterUserMethod_kwOptSupplied (m : Machine) (recv : Value) (name : String)
    (md : MethodDef) (names : List String) (n : String) (d : RubyCore.Expr)
    (vs : List Value) (v : Value)
    (hp : md.params = (names.map (fun x => (x, none)) ++ [(n, some d)]).map keyParam)
    (hn : (names ++ [n]).Nodup) (hl : vs.length = names.length)
    (hc : md.capturedFrame = none) (hd : md.declared = [])
    (hblock : md.fromBlock = false) (hfor : md.forTargets = none) :
    Interp.enterUserMethod m recv name md [] none (kwOf names vs ++ [(.sym n, v)]) =
      .next (Interp.withKont (pushMethodFrame m
        (requiredFrame recv name md (names ++ [n]) (vs ++ [v])))
        (.eval md.body) (.frameK m.frames.size)) := by
  have hnd := List.nodup_append.mp hn
  have hnn : n ∉ names := fun h => hnd.2.2 n h n (by simp) rfl
  have hsome : ∀ x ∈ names, (Interp.kwLookup (kwOf names vs) x).isSome = true :=
    fun x hx => kwLookup_kwOf_some hnd.1 hl hx
  have hprov : names.filterMap (fun kn =>
      (Interp.kwLookup (kwOf names vs ++ [(.sym n, v)]) kn).map (fun w => (kn, w))) =
      names.zip vs := by
    rw [← kwLookup_kwOf hnd.1 hl]
    exact filterMap_congr_mem (fun x hx => by rw [kwLookup_append_left (hsome x hx)])
  have hlast := kwLookup_append_last (vals := vs) (v := v) hnn
  have hnomiss : ¬ ∃ x, x ∈ names ∧
      Interp.kwLookup (kwOf names vs ++ [(.sym n, v)]) x = none := by
    rintro ⟨x, hx, h⟩
    have h2 := hsome x hx
    rw [← kwLookup_append_left (rest := [(.sym n, v)]) h2, h] at h2
    cases h2
  unfold Interp.enterUserMethod
  rw [hp, classifyFull_keys _ (by simp)]
  simp [Interp.appendKwHash, hc, hd, requiredFrame, pushMethodFrame,
    Interp.withKont, hp, hblock, hfor, hprov, hlast, List.filterMap_append, List.filterMap_map,
    Function.comp_def, hnomiss]
  rw [if_neg]
  · have hf : (names.zip vs).filter (fun _ => true) = names.zip vs :=
      List.filter_eq_self.mpr (fun _ _ => rfl)
    have hnone : names.filterMap (fun _ => (none : Option (String × RubyCore.Expr))) = [] :=
      List.filterMap_eq_nil_iff.mpr (fun _ _ => rfl)
    simp [Function.comp_def, hprov, hlast, hf, hnone, List.zip_append hl.symm]
    rfl
  · intro h
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_false, Bool.and_true] at h
    obtain ⟨_, h2⟩ := h
    obtain ⟨p, hp'⟩ := List.isEmpty_eq_false_iff_exists_mem.mp h2
    rw [List.mem_filter] at hp'
    obtain ⟨hp', hpred⟩ := hp'
    rcases List.mem_append.mp hp' with hq | hq
    · simp only [kwOf, List.mem_map] at hq
      obtain ⟨⟨a, b⟩, hq, rfl⟩ := hq
      simp [(List.of_mem_zip hq).1] at hpred
    · simp at hq; subst hq; simp at hpred

/-- The defaulted keyword omitted: predeclared nil, its default runs before the body. -/
theorem enterUserMethod_kwOptOmitted (m : Machine) (recv : Value) (name : String)
    (md : MethodDef) (names : List String) (n : String) (d : RubyCore.Expr) (vs : List Value)
    (hp : md.params = (names.map (fun x => (x, none)) ++ [(n, some d)]).map keyParam)
    (hn : (names ++ [n]).Nodup) (hl : vs.length = names.length)
    (hc : md.capturedFrame = none) (hd : md.declared = [])
    (hblock : md.fromBlock = false) (hfor : md.forTargets = none) :
    Interp.enterUserMethod m recv name md [] none (kwOf names vs) =
      .next (Interp.withKont
        { pushMethodFrame m (requiredFrame recv name md (names ++ [n]) (vs ++ [.nil])) with
          kont := .frameK m.frames.size :: m.kont }
        (.eval d) (.optDefK n [] [] md.body)) := by
  have hnd := List.nodup_append.mp hn
  have hnn : n ∉ names := fun h => hnd.2.2 n h n (by simp) rfl
  have hprov := kwLookup_kwOf hnd.1 hl
  have hlast := kwLookup_kwOf_none (vals := vs) hnn
  have hnomiss : ¬ ∃ x, x ∈ names ∧ Interp.kwLookup (kwOf names vs) x = none := by
    rintro ⟨x, hx, h⟩
    have h2 := kwLookup_kwOf_some hnd.1 hl hx
    rw [h] at h2
    cases h2
  unfold Interp.enterUserMethod
  rw [hp, classifyFull_keys _ (by simp)]
  simp [Interp.appendKwHash, hc, hd, requiredFrame, pushMethodFrame,
    Interp.withKont, hp, hblock, hfor, hprov, hlast, List.filterMap_append, List.filterMap_map,
    Function.comp_def, hnomiss]
  rw [if_neg]
  · have hf : (names.zip vs).filter (fun _ => true) = names.zip vs :=
      List.filter_eq_self.mpr (fun _ _ => rfl)
    have hnone : names.filterMap (fun _ => (none : Option (String × RubyCore.Expr))) = [] :=
      List.filterMap_eq_nil_iff.mpr (fun _ _ => rfl)
    simp [Function.comp_def, hprov, hlast, hf, hnone, List.zip_append hl.symm]
  · intro h
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_false, Bool.and_true] at h
    obtain ⟨_, h2⟩ := h
    obtain ⟨p, hp'⟩ := List.isEmpty_eq_false_iff_exists_mem.mp h2
    rw [List.mem_filter] at hp'
    obtain ⟨hp', hpred⟩ := hp'
    simp only [kwOf, List.mem_map] at hp'
    obtain ⟨⟨a, b⟩, hq, rfl⟩ := hp'
    simp [(List.of_mem_zip hq).1] at hpred

theorem kwopt_method_runSpec {κ : Ctx} {Γ Γb : Env} {I τ σ : Ty} {m : Machine}
    {md : MethodDef} {name n : String} {ps : List SigParam} {keys : List String}
    {args : List Value} {d e : Ratchet.Expr} {fr : Option Ratchet.Frame}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hkont : m.kont = [])
    (hp : md.params =
      ((ps.map (fun p : SigParam => p.1)).map (fun x => (x, (none : Option RubyCore.Expr))) ++
        [(n, some (toRuby d))]).map keyParam)
    (hnd : (ps.map (·.1) ++ [n]).Nodup)
    (hcap : md.capturedFrame = none) (hdecl : md.declared = []) (hbody : md.body = toRuby e)
    (hblock : md.fromBlock = false) (hfor : md.forTargets = none)
    (hss : md.superScope = none) (hown : md.definee.getD md.owner = md.owner)
    (hps : ∀ p ∈ ps ++ [(n, σ)], FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hτ : FirstOrder τ = true) (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hscope : ∀ names vs, frameScope (requiredFrame m.currentFrame.self name md names vs) =
      frameScope m.currentFrame)
    (hk : ∀ x, constGet? (κ.withFrame fr) x = constGet? κ x)
    (hframe : ∀ names vs,
      FrameOk fr (pushMethodFrame m (requiredFrame m.currentFrame.self name md names vs)))
    (hd : SemSafeCtxA (κ.withFrame fr) ps I d σ (κ.withFrame fr) ps I)
    (hb : SemSafeCtxA (κ.withFrame fr) (ps ++ [(n, σ)]) I e τ (κ.withFrame fr) Γb I)
    (hafter : envAfter ps n σ = ps ++ [(n, σ)]) (hkill : killClosOverSpine I n σ = I)
    (hcapS : capStale n σ σ = false) (hctx : capStaleCtx n σ (κ.withFrame fr) = false)
    (hargs : (keys = ps.map (·.1) ∧ args.length = ps.length ∧ DenAll (ps.map (·.2)) m args) ∨
      (keys = (ps ++ [(n, σ)]).map (·.1) ∧ args.length = ps.length + 1 ∧
        DenAll ((ps ++ [(n, σ)]).map (·.2)) m args)) :
    ∃ next, Interp.enterUserMethod m m.currentFrame.self name md [] none (kwOf keys args) =
        .next next ∧ RunSpec m next Γ τ κ I := by
  have hpsL : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false :=
    fun p hp => hps p (List.mem_append_left _ hp)
  have hσ : isAliasTy σ = false := (hps (n, σ) (by simp)).2
  have hu : RootUncaptured m := by
    unfold RootUncaptured
    rw [rootFrame_eq_currentFrame hm.frameInRange.1]
    exact (congrArg FrameScope.captured (hscope [] [])).symm
  have enter (names : List String) (vs : List Value) (Γe : Env)
      (he : EnvOk Γe (pushMethodFrame m (requiredFrame m.currentFrame.self name md names vs))) :
      StateOk (κ.withFrame fr) Γe I
        (pushMethodFrame m (requiredFrame m.currentFrame.self name md names vs)) :=
    method_enter_state hm ht ha (congrArg FrameScope.self (hscope names vs))
      (congrArg FrameScope.blk (hscope names vs)) (congrArg FrameScope.cref (hscope names vs))
      (congrArg FrameScope.defmod (hscope names vs)) (congrArg FrameScope.captured (hscope names vs))
      (fun _ => by simp only [defaultDefVis, currentFrame_pushMethodFrame, requiredFrame]; rfl) hk
      he (hframe names vs) rfl ⟨hss, hown.symm⟩
      (congrArg FrameScope.libraryOrigin (hscope names vs))
      (congrArg FrameScope.definitionFrame (hscope names vs))
  have pop (names : List String) (vs : List Value) : ∀ n v,
      ResultOk (pushMethodFrame m (requiredFrame m.currentFrame.self name md names vs)) Γb τ
        (.val v) n (κ.withFrame fr) I → StateOk κ Γ I (popMethodFrame n) :=
    fun n v hr => method_pop_state hm ht ha hu rfl (hscope names vs) hk hΓ hr.1 (hr.2.2 v rfl)
  rcases hargs with ⟨rfl, hlen, hden⟩ | ⟨rfl, hlen, hden⟩
  · have he := enter (ps.map (·.1) ++ [n]) (args ++ [.nil]) ps
      (optOmitted_envOk m _ name md ps n args hlen hden hpsL)
    have hs := methodFrame_runSpec_at hm.frameInRange.2
      (f := requiredFrame m.currentFrame.self name md (ps.map (·.1) ++ [n]) (args ++ [.nil]))
      rfl hτ (opt_default_chain he hd hb hafter hkill hcapS hctx hσ) (pop _ _) hm.rootClean
      hm.rootClean
    refine ⟨_, ?_, hs⟩
    rw [enterUserMethod_kwOptOmitted m _ name md (ps.map (·.1)) n (toRuby d) args hp hnd
      (by simpa using hlen) hcap hdecl hblock hfor]
    simp only [Interp.withKont, pushK, evalFrom, pushMethodFrame, hkont, hbody, List.nil_append]
    rfl
  · obtain ⟨vs, v, rfl⟩ : ∃ vs v, args = vs ++ [v] := by
      rcases List.eq_nil_or_concat args with h | ⟨vs, v, h⟩
      · subst h; simp at hlen
      · exact ⟨vs, v, by simpa using h⟩
    have hl : vs.length = (ps.map (·.1)).length := by simpa using hlen
    have he := enter ((ps ++ [(n, σ)]).map (·.1)) (vs ++ [v]) (ps ++ [(n, σ)])
      (requiredFrame_envOk m _ name md (ps ++ [(n, σ)]) (vs ++ [v]) (by simpa using hlen) hden hps)
    have hs := methodFrame_runSpec hm.frameInRange.2
      (f := requiredFrame m.currentFrame.self name md ((ps ++ [(n, σ)]).map (·.1)) (vs ++ [v]))
      rfl hτ (hb _ he) (pop _ _) hm.rootClean
    refine ⟨_, ?_, hs⟩
    rw [List.map_append, List.map_cons, List.map_nil, kwOf_append n v hl,
      enterUserMethod_kwOptSupplied m _ name md (ps.map (·.1)) n (toRuby d) vs v hp hnd hl
        hcap hdecl hblock hfor]
    simp only [Interp.withKont, pushK, evalFrom, pushMethodFrame, hkont, hbody, List.nil_append,
      List.map_append, List.map_cons, List.map_nil]

#print axioms kwopt_method_runSpec

theorem toRubyParams_kwOpt (ps : List SigParam) (n : String) (d : Ratchet.Expr) :
    toRubyParams (ps.map (fun p => Ratchet.Param.key p.1 none) ++ [.key n (some d)]) =
      ((ps.map (fun p : SigParam => p.1)).map (fun x => (x, (none : Option RubyCore.Expr))) ++
        [(n, some (toRuby d))]).map keyParam := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simpa only [List.map_cons, List.cons_append, toRubyParams, toRubyParam, toRubyOpt] using
      congrArg (RubyCore.Param.key p.1 none :: ·) ih

theorem top_kwopt_method_stepSpec {κ : Ctx} {Γ Γb : Env} {I τ σ : Ty} {m : Machine}
    {decl : Defn} {args : List Value} {ps : List SigParam} {n : String} {d : Ratchet.Expr}
    {keys : List String}
    (hparams : decl.params = ps.map (fun p => Ratchet.Param.key p.1 none) ++ [.key n (some d)])
    (hnd : (ps.map (·.1) ++ [n]).Nodup)
    (hps : ∀ p ∈ ps ++ [(n, σ)], FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hτ : FirstOrder τ = true)
    (hdflt : SemSafeCtxA (κ.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) ps I d σ (κ.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) ps I)
    (hbody : SemSafeCtxA (κ.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) (ps ++ [(n, σ)]) I decl.body τ (κ.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) Γb I)
    (hafter : envAfter ps n σ = ps ++ [(n, σ)]) (hkill : killClosOverSpine I n σ = I)
    (hcapS : capStale n σ σ = false) (hctx : capStaleCtx n σ (κ.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) = false)
    (hm : StateOk κ Γ I m) (hd : decl ∈ κ.defs)
    (ht : ReframeFO κ I) (ha : κ.asms = []) (hc : κ.consts = [])
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hkont : m.kont = [])
    (hargs : (keys = ps.map (·.1) ∧ args.length = ps.length ∧ DenAll (ps.map (·.2)) m args) ∨
      (keys = (ps ++ [(n, σ)]).map (·.1) ∧ args.length = ps.length + 1 ∧
        DenAll ((ps ++ [(n, σ)]).map (·.2)) m args))
    (hruntime : κ.scope.runtimeMain = true) (hblock : κ.blockTy = none) :
    StepSpec m Γ τ (Interp.finishSend m m.currentFrame.self .implicit decl.name [] .none
      (kwOf keys args)) κ I := by
  have ready := hm.runtime hruntime
  have hblk : m.currentFrame.blk = none := by simpa only [BlockTyOk, hblock] using hm.blockTy
  obtain ⟨md, hl, hp, hb, hu, hcode⟩ := defsOk_lookup hm.defs hd ready
  rw [ready.self]
  change StepSpec m Γ τ (Interp.invoke m (.ref Boot.mainId) .implicit decl.name [] none
    (kwOf keys args)) κ I
  cases hs : Interp.crubyShadow m.heap
      ((ancestors m.heap (classOf m.heap (.ref Boot.mainId))).takeWhile (· != Boot.objectId))
      decl.name with
  | some cname =>
    unfold Interp.invoke
    simp only [hl, Option.isNone, Bool.and_false, Bool.false_eq_true, ↓reduceIte, ready.payload]
    simp only [Interp.invoke.invokeDispatch, hl, hu, hcode.fromPrelude, Bool.false_eq_true, ↓reduceIte,
      Interp.crubyResolvedShadow, hcode.builtin, Option.any, hs]
    trivial
  | none =>
    have hdef : md.definee.getD Boot.objectId = Boot.objectId := by
      simpa only [hcode.owner] using hcode.definee
    obtain ⟨next, he, hr⟩ := kwopt_method_runSpec (name := decl.name) (keys := keys)
      (fr := (some ⟨"Object", "Object", decl.name, false⟩)) (d := d) (e := decl.body)
      hm ht ha hkont (hp.trans (by rw [hparams]; exact toRubyParams_kwOpt ps n d)) hnd
      hcode.captured hcode.declared hb hcode.fromBlock hcode.forTargets hcode.superScope
      (by rw [hcode.owner]; exact hdef) hps hτ hΓ
      (fun names vs => by simp [frameScope, requiredFrame, hcode.owner, hcode.cref,
        hdef, hcode.fromPrelude, ready.owner, ready.cref, ready.captured,
        ready.origin, hm.localAlias, hblk, hcode.definitionFrame, ready.defFrame])
      (fun x => (constGet?_empty (κ := κ.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) hc x).trans (constGet?_empty hc x).symm)
      (fun names vs => by
        simp only [FrameOk, Frame.recvTy, Bool.false_eq_true, ↓reduceIte, denM,
          currentFrame_pushMethodFrame, requiredFrame, hcode.superName, Option.getD_none]
        exact ⟨trivial, by rw [ready.self]; exact ready.object, trivial⟩)
      hdflt hbody hafter hkill hcapS hctx hargs
    rw [ready.self] at he
    rw [invoke_ordinary_userMethod ready.payload hl hcode.builtin hu hcode.fromPrelude rfl hs, he]
    exact hr

#print axioms top_kwopt_method_stepSpec

theorem SemSafeCtxA.callSigKwOpt {κ κ' : Ctx} {Γ Γ' Γb : Env} {I I' τ σ : Ty}
    {decl : Defn} {ps : List SigParam} {n : String} {d : Ratchet.Expr}
    {args : List Ratchet.Expr} {entries : List Ratchet.KwEntry} {keys : List String}
    {tys : List Ty}
    (hparams : decl.params = ps.map (fun p => Ratchet.Param.key p.1 none) ++ [.key n (some d)])
    (hnd : (ps.map (·.1) ++ [n]).Nodup) (hka : kwArgs? keys entries = some args)
    (hps : ∀ p ∈ ps ++ [(n, σ)], FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hτ : FirstOrder τ = true)
    (hdflt : SemSafeCtxA (κ'.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) ps I' d σ (κ'.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) ps I')
    (hbody : SemSafeCtxA (κ'.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) (ps ++ [(n, σ)]) I' decl.body τ (κ'.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) Γb I')
    (hafter : envAfter ps n σ = ps ++ [(n, σ)]) (hkill : killClosOverSpine I' n σ = I')
    (hcapS : capStale n σ σ = false) (hctx : capStaleCtx n σ (κ'.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) = false)
    (hargs : SemAllCtxA κ Γ I args tys κ' Γ' I')
    (hkt : (keys = ps.map (·.1) ∧ tys = ps.map (·.2)) ∨
      (keys = (ps ++ [(n, σ)]).map (·.1) ∧ tys = (ps ++ [(n, σ)]).map (·.2)))
    (hd : decl ∈ κ'.defs)
    (hstart : κ.scope.runtimeMain = true) (hruntime : κ'.scope.runtimeMain = true)
    (hself : κ'.selfTy = none) (hblock : κ'.blockTy = none) (hconst : κ'.consts = [])
    (hasms : κ'.asms = []) (hI : FirstOrder I' = true)
    (hΓ : ∀ p ∈ Γ', FirstOrder (stripAlias p.2) = true) :
    SemSafeCtxA κ Γ I (.send none decl.name [.kwargs entries] none) τ κ' Γ' I' := by
  obtain ⟨rfl, hlen⟩ := kwArgs?_sound hka
  have hkn : keys.Nodup := by
    rcases hkt with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact (List.nodup_append.mp hnd).1
    · simpa using hnd
  have hfo : ∀ t ∈ tys, FirstOrder t = true := by
    intro t ht
    rcases hkt with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    · simp only [List.mem_map] at ht
      obtain ⟨p, hp, rfl⟩ := ht
      first
      | exact (hps p (List.mem_append_left _ hp)).1
      | exact (hps p hp).1
  intro m hm
  let start := evalFrom m (.send none decl.name [.kwargs (kwPairs keys args)] none)
  apply RunSpec.rebase (middle := start) ?_ (Framed_reCtl _ _ [])
  apply RunSpec.of_stepSpec (by rfl)
  have hselfm : start.currentFrame.self = .ref Boot.mainId := (hm.runtime hstart).self
  change StepSpec start Γ' τ
    (Interp.startArgs start start.currentFrame.self .implicit decl.name []
      [.kwargs (toRubyKwList (kwPairs keys args))] .none) κ' I'
  rw [hselfm]
  change StepSpec start Γ' τ (Interp.startKwargs start (.ref Boot.mainId) .implicit decl.name []
      (kwOf [] []) (toRubyKwList (kwPairs keys args)) .none) κ' I'
  apply hargs.startKwargs (StateOk_reCtl hm _ []) rfl [] [] [] keys
    hlen.symm (by simpa using hkn) rfl (by simpa using hfo) trivial
  intro n' hn hk vs hv hvl
  have hlv := denAll_length hv
  have hargs' : (keys = ps.map (·.1) ∧ vs.length = ps.length ∧ DenAll (ps.map (·.2)) n' vs) ∨
      (keys = (ps ++ [(n, σ)]).map (·.1) ∧ vs.length = ps.length + 1 ∧
        DenAll ((ps ++ [(n, σ)]).map (·.2)) n' vs) := by
    rcases hkt with ⟨hk', rfl⟩ | ⟨hk', rfl⟩
    · exact .inl ⟨hk', by simpa using hlv, by simpa using hv⟩
    · exact .inr ⟨hk', by simpa using hlv, by simpa using hv⟩
  have h := top_kwopt_method_stepSpec hparams hnd hps hτ hdflt hbody hafter hkill hcapS hctx hn hd
    (ReframeFO.empty hI hself hblock hconst) hasms hconst hΓ hk hargs' hruntime hblock
  simpa only [(hn.runtime hruntime).self, List.nil_append] using h

/-- Definition installs the method; the default and body are rechecked at each call. -/
theorem SemSafeCtxA.defDeclKwOpt {κ : Ctx} {Γ Γb : Env} {I τ σ : Ty} {d : Defn}
    {ps : List SigParam} {n : String} {dflt : Ratchet.Expr}
    (_hparams : d.params = ps.map (fun p => Ratchet.Param.key p.1 none) ++ [.key n (some dflt)])
    (_hps : ∀ p ∈ ps ++ [(n, σ)], FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (_hret : FirstOrder τ = true)
    (_hdflt : SemSafeCtxA (topBodyCtx κ d) ps I dflt σ (topBodyCtx κ d) ps I)
    (_hbody : SemSafeCtxA (topBodyCtx κ d) (ps ++ [(n, σ)]) I d.body τ (topBodyCtx κ d) Γb I)
    (hruntime : κ.scope.runtimeMain = true) (hclasses : topDeclClassesB κ d.name = true)
    (hself : κ.selfTy = none) (hblock : κ.blockTy = none) (hconst : κ.consts = [])
    (hasms : κ.asms = []) (hI : FirstOrder I = true)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hfresh : ∀ old ∈ κ.defs, old.name ≠ d.name)
    (hmiss : "method_missing" ≠ d.name) (hquiet : "method_added" ≠ d.name) :
    SemSafeCtxA κ Γ I (.def' d.name d.params d.body) .sym (topDeclCtx κ d) Γ I :=
  top_definition hruntime hclasses hself hblock hconst hasms hI hΓ hfresh hmiss hquiet

#print axioms SemSafeCtxA.callSigKwOpt
#print axioms SemSafeCtxA.defDeclKwOpt
end Ratchet.Denote.Typed
