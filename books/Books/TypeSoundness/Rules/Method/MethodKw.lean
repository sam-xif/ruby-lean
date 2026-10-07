import Books.TypeSoundness.Rules.Method.MethodOptCall
import Checker.Check.OptShape

/-! Top-level methods whose parameters are required keywords, called with every keyword
in declared order. The callee frame then has the required-positional shape. -/

set_option autoImplicit false
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

def kwOf (names : List String) (vals : List Value) : List (Value × Value) :=
  (names.zip vals).map (fun p => (.sym p.1, p.2))

theorem classifyFull_kw (names : List String) :
    Interp.classifyFull (names.map (fun n => RubyCore.Param.key n none)) =
      some ⟨[], [], none, [], names.map (fun n => (n, none)), none, none, []⟩ := by
  rcases names with _ | ⟨n, ns⟩
  · rfl
  have hnames : (n :: ns).zipIdx.map (fun p => RubyCore.Param.key p.1 none) =
      (n :: ns).map (fun n => RubyCore.Param.key n none) := by
    change List.map ((fun n => RubyCore.Param.key n none) ∘ Prod.fst) _ = _
    rw [← List.map_map, List.zipIdx_map_fst]
  have hd : ns.dropWhile (fun _ => true) = [] := by
    clear hnames; induction ns <;> simp_all [List.dropWhile]
  have ht : ns.takeWhile (fun _ => true) = ns := by
    clear hnames hd; induction ns <;> simp_all [List.takeWhile]
  obtain ⟨x, xs, hr⟩ : ∃ x xs, (n :: ns).reverse = x :: xs := by
    cases h : (n :: ns).reverse with
    | nil => simp at h
    | cons x xs => exact ⟨x, xs, rfl⟩
  have hr2 : List.map (fun n => RubyCore.Param.key n none) ns.reverse ++ [RubyCore.Param.key n none] =
      RubyCore.Param.key x none :: List.map (fun n => RubyCore.Param.key n none) xs := by
    have := congrArg (List.map (fun n => RubyCore.Param.key n none)) hr
    simpa using this
  unfold Interp.classifyFull
  simp only [List.flatMap_map, ← List.map_eq_flatMap, List.zipIdx_map,
    List.map_map, List.filterMap_map, Function.comp_def, Prod.map]
  simp only [hnames]
  simp [← List.map_reverse, hr, hr2, List.takeWhile_map, List.dropWhile_map,
    Function.comp_def, hd, ht, List.filterMap_map, List.dropWhile, List.takeWhile]

theorem filterMap_congr_mem {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.filterMap_cons, h x (by simp),
      filterMap_congr_mem (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem kwLookup_kwOf {names : List String} {vals : List Value} (hn : names.Nodup)
    (hl : vals.length = names.length) :
    names.filterMap (fun kn => (Interp.kwLookup (kwOf names vals) kn).map (fun v => (kn, v))) =
      names.zip vals := by
  induction names generalizing vals with
  | nil => rfl
  | cons n ns ih =>
    cases vals with
    | nil => simp at hl
    | cons v vs =>
      have hn' := List.nodup_cons.mp hn
      have hrest : ns.filterMap (fun kn => (Interp.kwLookup (kwOf (n :: ns) (v :: vs)) kn).map
          (fun w => (kn, w))) = ns.filterMap (fun kn =>
            (Interp.kwLookup (kwOf ns vs) kn).map (fun w => (kn, w))) := by
        apply filterMap_congr_mem
        intro x hx
        have hne : n ≠ x := fun h => hn'.1 (h ▸ hx)
        simp [Interp.kwLookup, kwOf, hne]
      simp only [List.filterMap_cons, List.zip_cons_cons]
      rw [hrest, ih hn'.2 (by simpa using hl)]
      simp [Interp.kwLookup, kwOf]

theorem kwLookup_kwOf_some {names : List String} {vals : List Value} (hn : names.Nodup)
    (hl : vals.length = names.length) {x : String} (hx : x ∈ names) :
    (Interp.kwLookup (kwOf names vals) x).isSome = true := by
  induction names generalizing vals with
  | nil => cases hx
  | cons n ns ih =>
    cases vals with
    | nil => simp at hl
    | cons v vs =>
      have hn' := List.nodup_cons.mp hn
      by_cases hnx : n = x
      · subst hnx; simp [Interp.kwLookup, kwOf]
      · have hx' : x ∈ ns := (List.mem_cons.mp hx).resolve_left (fun h => hnx h.symm)
        have := ih hn'.2 (by simpa using hl) hx'
        simpa [Interp.kwLookup, kwOf, hnx] using this

theorem enterUserMethod_kw (m : Machine) (recv : Value) (name : String)
    (md : MethodDef) (names : List String) (vals : List Value)
    (hp : md.params = names.map (fun n => RubyCore.Param.key n none))
    (hn : names.Nodup) (hl : vals.length = names.length) (hne : names ≠ [])
    (hc : md.capturedFrame = none) (hd : md.declared = [])
    (hblock : md.fromBlock = false) (hfor : md.forTargets = none) :
    Interp.enterUserMethod m recv name md [] none (kwOf names vals) =
      .next (Interp.withKont (pushMethodFrame m (requiredFrame recv name md names vals))
        (.eval md.body) (.frameK m.frames.size)) := by
  have hprov := kwLookup_kwOf hn hl
  have hsome : ∀ x ∈ names, Interp.kwLookup (kwOf names vals) x ≠ none := by
    intro x hx h
    have := kwLookup_kwOf_some hn hl hx
    rw [h] at this; cases this
  have hkeys : ∀ p ∈ kwOf names vals, ∃ x ∈ names, p.1 = .sym x := by
    intro p hp'
    simp only [kwOf, List.mem_map] at hp'
    obtain ⟨q, hq, rfl⟩ := hp'
    exact ⟨q.1, (List.of_mem_zip hq).1, rfl⟩
  have hnomiss : ¬ ∃ x, x ∈ names ∧ Interp.kwLookup (kwOf names vals) x = none :=
    fun ⟨x, hx, h⟩ => hsome x hx h
  unfold Interp.enterUserMethod
  rw [hp, classifyFull_kw]
  simp [Interp.appendKwHash, hc, hd, requiredFrame, pushMethodFrame,
    Interp.withKont, hp, hblock, hfor, hprov, hne, hnomiss]
  have hzip : ∀ a b, (a, b) ∈ names.zip vals → a ∈ names := fun a b h => (List.of_mem_zip h).1
  have hf : (names.zip vals).filter (fun _ => true) = names.zip vals :=
    List.filter_eq_self.mpr (fun _ _ => rfl)
  have hnone : names.filterMap (fun _ => (none : Option (String × RubyCore.Expr))) = [] :=
    List.filterMap_eq_nil_iff.mpr (fun _ _ => rfl)
  rw [if_neg]
  · simp [Function.comp_def, hprov, hf, hnone]
    rfl
  · intro h
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_false, Bool.and_true] at h
    obtain ⟨_, h2⟩ := h
    obtain ⟨p, hp'⟩ := List.isEmpty_eq_false_iff_exists_mem.mp h2
    rw [List.mem_filter] at hp'
    obtain ⟨hp', hpred⟩ := hp'
    simp only [kwOf, List.mem_map] at hp'
    obtain ⟨⟨a, b⟩, hq, rfl⟩ := hp'
    simp [hzip a b hq] at hpred

theorem kw_method_runSpec {κ : Ctx} {Γ Γb : Env} {I τ : Ty} {m : Machine}
    {md : MethodDef} {name : String} {ps : List SigParam} {args : List Value}
    {e : Checker.Expr} {fr : Option Checker.Frame}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hkont : m.kont = []) (hp : md.params = (ps.map (·.1)).map (fun n => RubyCore.Param.key n none))
    (hnd : (ps.map (·.1)).Nodup) (hne : ps ≠ [])
    (hcap : md.capturedFrame = none) (hdecl : md.declared = []) (hbody : md.body = toRuby e)
    (hblock : md.fromBlock = false) (hfor : md.forTargets = none)
    (hss : md.superScope = none) (hown : md.definee.getD md.owner = md.owner)
    (hlen : args.length = ps.length) (hargs : DenAll (ps.map (·.2)) m args)
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hτ : FirstOrder τ = true) (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hscope : frameScope (requiredFrame m.currentFrame.self name md (ps.map (·.1)) args) =
      frameScope m.currentFrame)
    (hk : ∀ x, constGet? (κ.withFrame fr) x = constGet? κ x)
    (hframe : FrameOk fr
      (pushMethodFrame m (requiredFrame m.currentFrame.self name md (ps.map (·.1)) args)))
    (hb : SemSafeCtxA (κ.withFrame fr) ps I e τ (κ.withFrame fr) Γb I) :
    ∃ next, Interp.enterUserMethod m m.currentFrame.self name md [] none
        (kwOf (ps.map (·.1)) args) = .next next ∧
      RunSpec m next Γ τ κ I := by
  let f := requiredFrame m.currentFrame.self name md (ps.map (·.1)) args
  let entry := pushMethodFrame m f
  have he : StateOk (κ.withFrame fr) ps I entry :=
    method_enter_state hm ht ha (congrArg FrameScope.self hscope)
      (congrArg FrameScope.blk hscope) (congrArg FrameScope.cref hscope)
      (congrArg FrameScope.defmod hscope) (congrArg FrameScope.captured hscope)
      (fun _ => by simp only [defaultDefVis, currentFrame_pushMethodFrame, f, requiredFrame]; rfl) hk
      (requiredFrame_envOk m _ name md ps args hlen hargs hps) hframe rfl ⟨hss, hown.symm⟩
      (congrArg FrameScope.libraryOrigin hscope) (congrArg FrameScope.definitionFrame hscope)
  have hu : RootUncaptured m := by
    unfold RootUncaptured
    rw [rootFrame_eq_currentFrame hm.frameInRange.1]
    exact (congrArg FrameScope.captured hscope).symm
  have hs := methodFrame_runSpec hm.frameInRange.2 (f := f) rfl hτ (hb entry he)
    (fun n v hr => method_pop_state hm ht ha hu rfl hscope hk hΓ hr.1 (hr.2.2 v rfl)) hm.rootClean
  refine ⟨_, ?_, hs⟩
  rw [enterUserMethod_kw m _ name md (ps.map (·.1)) args hp hnd (by simpa using hlen)
    (by cases ps <;> simp_all) hcap hdecl hblock hfor]
  simp only [Interp.withKont, pushK, evalFrom, f, pushMethodFrame, hkont, hbody, List.nil_append]

#print axioms kw_method_runSpec
theorem toRubyParams_kw (ps : List SigParam) :
    toRubyParams (ps.map (fun p => Checker.Param.key p.1 none)) =
      (ps.map (·.1)).map (fun n => RubyCore.Param.key n none) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simpa only [List.map_cons, toRubyParams, toRubyParam, toRubyOpt] using
      congrArg (RubyCore.Param.key p.1 none :: ·) ih

theorem top_kw_method_stepSpec {κ : Ctx} {Γ Γb : Env} {I τ : Ty} {m : Machine} {decl : Defn}
    {args : List Value} {ps : List SigParam}
    (hparams : decl.params = ps.map (fun p => Checker.Param.key p.1 none))
    (hnd : (ps.map (·.1)).Nodup) (hne : ps ≠ [])
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hτ : FirstOrder τ = true)
    (hbody : SemSafeCtxA (κ.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) ps I decl.body τ
      (κ.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) Γb I)
    (hm : StateOk κ Γ I m) (hd : decl ∈ κ.defs)
    (ht : ReframeFO κ I) (ha : κ.asms = []) (hc : κ.consts = [])
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hkont : m.kont = []) (hlen : args.length = ps.length)
    (hargs : DenAll (ps.map (·.2)) m args)
    (hruntime : κ.scope.runtimeMain = true) (hblock : κ.blockTy = none) :
    StepSpec m Γ τ (Interp.finishSend m m.currentFrame.self .implicit decl.name [] .none
      (kwOf (ps.map (·.1)) args)) κ I := by
  have ready := hm.runtime hruntime
  have hblk : m.currentFrame.blk = none := by simpa only [BlockTyOk, hblock] using hm.blockTy
  obtain ⟨md, hl, hp, hb, hu, hcode⟩ := defsOk_lookup hm.defs hd ready
  rw [ready.self]
  change StepSpec m Γ τ (Interp.invoke m (.ref Boot.mainId) .implicit decl.name [] none
    (kwOf (ps.map (·.1)) args)) κ I
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
    obtain ⟨next, he, hr⟩ := kw_method_runSpec (name := decl.name)
      (fr := some ⟨"Object", "Object", decl.name, false⟩) (e := decl.body)
      hm ht ha hkont (hp.trans (by rw [hparams]; exact toRubyParams_kw ps)) hnd hne
      hcode.captured hcode.declared hb hcode.fromBlock hcode.forTargets hcode.superScope
      (by rw [hcode.owner]; exact hdef) hlen hargs hps hτ hΓ
      (by simp [frameScope, requiredFrame, hcode.owner, hcode.cref,
        hdef, hcode.fromPrelude, ready.owner, ready.cref, ready.captured,
        ready.origin, hm.localAlias, hblk, hcode.definitionFrame, ready.defFrame])
      (fun x => (constGet?_empty (κ := κ.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) hc x).trans
        (constGet?_empty hc x).symm)
      (by
        simp only [FrameOk, Frame.recvTy, Bool.false_eq_true, ↓reduceIte, denM,
          currentFrame_pushMethodFrame, requiredFrame, hcode.superName, Option.getD_none]
        exact ⟨trivial, by rw [ready.self]; exact ready.object, trivial⟩)
      hbody
    rw [ready.self] at he
    rw [invoke_ordinary_userMethod ready.payload hl hcode.builtin hu hcode.fromPrelude rfl hs, he]
    exact hr

#print axioms top_kw_method_stepSpec
theorem kwAdd_fresh {keys : List String} {vals : List Value} {k : String} {v : Value}
    (hk : k ∉ keys) :
    Interp.kwAdd (kwOf keys vals) (.sym k) v = kwOf keys vals ++ [(.sym k, v)] := by
  unfold Interp.kwAdd
  have hn : (kwOf keys vals).findIdx? (fun p => p.1.identEq (.sym k)) = none := by
    rw [List.findIdx?_eq_none_iff]
    intro p hp
    simp only [kwOf, List.mem_map] at hp
    obtain ⟨⟨a, b⟩, hq, rfl⟩ := hp
    have ha := (List.of_mem_zip hq).1
    have hne : a ≠ k := fun h => hk (h ▸ ha)
    simp [Value.identEq, hne]
  rw [hn]

theorem kwOf_append {keys : List String} {vals : List Value} (k : String) (v : Value)
    (hl : vals.length = keys.length) :
    kwOf (keys ++ [k]) (vals ++ [v]) = kwOf keys vals ++ [(.sym k, v)] := by
  simp [kwOf, List.zip_append hl.symm]

theorem SemAllCtxA.startKwargs {κ κ' : Ctx} {Γ Γ' : Env} {I I' : Ty}
    {es : List Checker.Expr} {tys : List Ty} (hs : SemAllCtxA κ Γ I es tys κ' Γ' I')
    {τ : Ty} {recv : Value} {name : String} {m : Machine}
    (hm : StateOk κ Γ I m) (hk : m.kont = []) (seenK : List String) (seen : List Ty)
    (acc : List Value) (keys : List String) (hlenK : keys.length = es.length)
    (hnd : (seenK ++ keys).Nodup) (hlenS : acc.length = seenK.length)
    (hf : ∀ σ ∈ seen ++ tys, FirstOrder σ = true) (ha : DenAll seen m acc)
    (finish : ∀ n, StateOk κ' Γ' I' n → n.kont = [] → ∀ vs, DenAll (seen ++ tys) n vs →
      vs.length = (seenK ++ keys).length →
      StepSpec n Γ' τ (Interp.finishSend n recv .implicit name [] .none
        (kwOf (seenK ++ keys) vs)) κ' I') :
    StepSpec m Γ' τ (Interp.startKwargs m recv .implicit name [] (kwOf seenK acc)
      (toRubyKwList (kwPairs keys es)) .none) κ' I' := by
  induction hs generalizing m seen acc seenK keys with
  | nil =>
    cases keys with
    | cons _ _ => simp at hlenK
    | nil =>
      show StepSpec m _ τ (Interp.finishSend m recv .implicit name [] .none (kwOf seenK acc)) _ _
      simpa using finish m hm hk acc (by simpa using ha) (by simpa using hlenS)
  | @cons κ κ₁ κ₂ Γ Γ₁ Γ₂ I I₁ I₂ σ e es tys he hs hp ih =>
    cases keys with
    | nil => simp at hlenK
    | cons key ks =>
    have hfresh : key ∉ seenK := by
      intro h
      exact (List.nodup_append.mp hnd).2.2 key h key (by simp) rfl
    show StepSpec m _ τ (.next (Interp.withKont m (.eval (toRuby e))
      (.kwPairK key (toRubyKwList (kwPairs ks es)) (kwOf seenK acc) recv .implicit name [] .none))) _ _
    simp only [StepSpec, Interp.withKont, hk]
    change RunSpec m (pushK [.kwPairK key (toRubyKwList (kwPairs ks es)) (kwOf seenK acc) recv
      .implicit name [] .none] (evalFrom m e)) Γ₂ τ κ₂ I₂
    apply (he m hm).bindSpec hm.rootClean (by
      intro k h
      simp only [List.mem_singleton] at h
      subst h
      rfl)
    intro a n hn
    cases a with
    | val v =>
      have hfr : Framed m (deliverA (.val v) n []) := hn.1.trans (Framed_reCtl _ _ _)
      have hacc : DenAll (seen ++ [σ]) (deliverA (.val v) n []) (acc ++ [v]) :=
        denAll_append (denAll_framed (fun t ht => hf t (by simp [ht])) hfr ha)
          ⟨denM_deliverA.mpr hn.2.1, trivial⟩
      have hnext := ih (StateOk_deliverA (hn.2.2 v rfl)) rfl (seenK ++ [key]) (seen ++ [σ])
        (acc ++ [v]) ks (by simpa using hlenK) (by simpa using hnd) (by simp [hlenS])
        (by simpa only [List.append_assoc, List.singleton_append] using hf) hacc
        (by simpa only [List.append_assoc, List.singleton_append] using finish)
      have hrun : RunSpec (deliverA (.val v) n [])
          (deliverA (.val v) n [.kwPairK key (toRubyKwList (kwPairs ks es)) (kwOf seenK acc) recv
            .implicit name [] .none]) Γ₂ τ κ₂ I₂ := by
        apply RunSpec.of_stepSpec (by rfl)
        rw [kwOf_append key v hlenS, ← kwAdd_fresh hfresh] at hnext
        exact hnext
      exact hrun.rebase hfr
    | esc j =>
      apply RunSpec.step (by rfl)
        (show Interp.stepFn _ = .next (deliverA (.esc j) n []) from by cases j <;> rfl)
      exact RunSpec.answer ⟨hn.1, hn.2.1, fun _ hv => by cases hv⟩

#print axioms SemAllCtxA.startKwargs
theorem SemSafeCtxA.callSigKw {κ κ' : Ctx} {Γ Γ' Γb : Env} {I I' τ : Ty}
    {decl : Defn} {ps : List SigParam} {args : List Checker.Expr} {entries : List Checker.KwEntry}
    (hparams : decl.params = ps.map (fun p => Checker.Param.key p.1 none))
    (hnd : (ps.map (·.1)).Nodup) (hne : ps ≠ [])
    (hka : kwArgs? (ps.map (·.1)) entries = some args)
    (hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (hτ : FirstOrder τ = true)
    (hbody : SemSafeCtxA (κ'.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) ps I' decl.body τ
      (κ'.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) Γb I')
    (hargs : SemAllCtxA κ Γ I args (ps.map (·.2)) κ' Γ' I')
    (hd : decl ∈ κ'.defs)
    (hstart : κ.scope.runtimeMain = true) (hruntime : κ'.scope.runtimeMain = true)
    (hself : κ'.selfTy = none) (hblock : κ'.blockTy = none) (hconst : κ'.consts = [])
    (hasms : κ'.asms = []) (hI : FirstOrder I' = true)
    (hΓ : ∀ p ∈ Γ', FirstOrder (stripAlias p.2) = true) :
    SemSafeCtxA κ Γ I (.send none decl.name [.kwargs entries] none) τ κ' Γ' I' := by
  obtain ⟨rfl, hlen'⟩ := kwArgs?_sound hka
  have hlen : args.length = ps.length := by simpa using hlen'
  intro m hm
  let start := evalFrom m (.send none decl.name [.kwargs (kwPairs (ps.map (·.1)) args)] none)
  apply RunSpec.rebase (middle := start) ?_ (Framed_reCtl _ _ [])
  apply RunSpec.of_stepSpec (by rfl)
  have hselfm : start.currentFrame.self = .ref Boot.mainId := (hm.runtime hstart).self
  change StepSpec start Γ' τ
    (Interp.startArgs start start.currentFrame.self .implicit decl.name []
      [.kwargs (toRubyKwList (kwPairs (ps.map (·.1)) args))] .none) κ' I'
  rw [hselfm]
  change StepSpec start Γ' τ (Interp.startKwargs start (.ref Boot.mainId) .implicit decl.name []
      (kwOf [] []) (toRubyKwList (kwPairs (ps.map (·.1)) args)) .none) κ' I'
  apply hargs.startKwargs (StateOk_reCtl hm _ []) rfl [] [] [] (ps.map (·.1))
    (by simpa using hlen.symm) (by simpa using hnd) rfl
    (by
      intro σ hσ
      simp only [List.nil_append, List.mem_map] at hσ
      obtain ⟨p, hp, rfl⟩ := hσ
      exact (hps p hp).1)
    trivial
  intro n hn hk vs hv hvl
  have h := top_kw_method_stepSpec hparams hnd hne hps hτ hbody hn hd
    (ReframeFO.empty hI hself hblock hconst) hasms hconst hΓ hk (by simpa using hvl)
    (by simpa using hv) hruntime hblock
  simpa only [(hn.runtime hruntime).self, List.nil_append] using h

theorem SemSafeCtxA.defDeclKw {κ : Ctx} {Γ Γb : Env} {I τ : Ty} {d : Defn} {ps : List SigParam}
    (_hparams : d.params = ps.map (fun p => Checker.Param.key p.1 none))
    (_hps : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false)
    (_hret : FirstOrder τ = true)
    (_hbody : SemSafeCtxA (topBodyCtx κ d) ps I d.body τ (topBodyCtx κ d) Γb I)
    (hruntime : κ.scope.runtimeMain = true) (hclasses : topDeclClassesB κ d.name = true)
    (hself : κ.selfTy = none) (hblock : κ.blockTy = none) (hconst : κ.consts = [])
    (hasms : κ.asms = []) (hI : FirstOrder I = true)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hfresh : ∀ old ∈ κ.defs, old.name ≠ d.name)
    (hmiss : "method_missing" ≠ d.name) (hquiet : "method_added" ≠ d.name) :
    SemSafeCtxA κ Γ I (.def' d.name d.params d.body) .sym (topDeclCtx κ d) Γ I :=
  top_definition hruntime hclasses hself hblock hconst hasms hI hΓ hfresh hmiss hquiet

#print axioms SemSafeCtxA.callSigKw
#print axioms SemSafeCtxA.defDeclKw
end Checker.Soundness.Typed
