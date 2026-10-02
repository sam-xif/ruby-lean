import Denote.Rules.Method.MethodState
import Denote.Rules.Method.MethodReturn

/-! Method entry with required positionals and one trailing optional parameter. A
supplied argument binds like a required one; an omitted one is predeclared nil and its
default runs in the callee frame under `optDefK`. -/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem classifyFull_opt (names : List String) (n : String) (d : RubyCore.Expr) :
    Interp.classifyFull (names.map RubyCore.Param.req ++ [.opt n d]) =
      some ⟨names, [(n, d)], none, [], [], none, none, []⟩ := by
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
  done

/-- A supplied optional binds exactly like one more required parameter. -/
theorem enterUserMethod_optSupplied (m : Machine) (recv : Value) (name : String)
    (md : MethodDef) (names : List String) (n : String) (d : RubyCore.Expr) (args : List Value)
    (hp : md.params = names.map RubyCore.Param.req ++ [.opt n d])
    (hc : md.capturedFrame = none) (hd : md.declared = [])
    (ha : args.length = names.length + 1)
    (hblock : md.fromBlock = false) (hfor : md.forTargets = none) :
    Interp.enterUserMethod m recv name md args none =
      .next (Interp.withKont (pushMethodFrame m (requiredFrame recv name md (names ++ [n]) args))
        (.eval md.body) (.frameK m.frames.size)) := by
  obtain ⟨pre, a, rfl⟩ : ∃ pre a, args = pre ++ [a] := by
    rcases List.eq_nil_or_concat args with h | ⟨pre, a, h⟩
    · subst h; simp at ha
    · exact ⟨pre, a, by simpa using h⟩
  have hl : pre.length = names.length := by simpa using ha
  have hf : (names.zip pre).filter (fun _ => true) = names.zip pre :=
    List.filter_eq_self.mpr (fun _ _ => rfl)
  unfold Interp.enterUserMethod
  rw [hp, classifyFull_opt]
  simp [Interp.appendKwHash, hc, hd, hl, requiredFrame, pushMethodFrame,
    Interp.withKont, Interp.withCtl, hp, hblock, hfor, List.zip_append, hf]

/-- An omitted optional is predeclared nil; its default runs before the body. -/
theorem enterUserMethod_optOmitted (m : Machine) (recv : Value) (name : String)
    (md : MethodDef) (names : List String) (n : String) (d : RubyCore.Expr) (args : List Value)
    (hp : md.params = names.map RubyCore.Param.req ++ [.opt n d])
    (hc : md.capturedFrame = none) (hd : md.declared = [])
    (ha : args.length = names.length)
    (hblock : md.fromBlock = false) (hfor : md.forTargets = none) :
    Interp.enterUserMethod m recv name md args none =
      .next (Interp.withKont
        { pushMethodFrame m (requiredFrame recv name md (names ++ [n]) (args ++ [.nil])) with
          kont := .frameK m.frames.size :: m.kont }
        (.eval d) (.optDefK n [] [] md.body)) := by
  have hf : (names.zip args).filter (fun _ => true) = names.zip args :=
    List.filter_eq_self.mpr (fun _ _ => rfl)
  unfold Interp.enterUserMethod
  rw [hp, classifyFull_opt]
  simp [Interp.appendKwHash, hc, hd, ha, requiredFrame, pushMethodFrame,
    Interp.withKont, hp, hblock, hfor, List.zip_append, hf,
    List.take_of_length_le (Nat.le_of_eq ha)]

/-- Before its default runs, the omitted optional reads nil: the frame conforms to the
required parameters alone. -/
theorem optOmitted_envOk (m : Machine) (recv : Value) (name : String)
    (md : MethodDef) (ps : List SigParam) (n : String) (args : List Value)
    (hlen : args.length = ps.length) (hargs : DenAll (ps.map (·.2)) m args)
    (htys : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false) :
    EnvOk ps (pushMethodFrame m
      (requiredFrame recv name md (ps.map (·.1) ++ [n]) (args ++ [.nil]))) := by
  have hzip : (ps.map (·.1) ++ [n]).zip (args ++ [.nil]) = (ps.map (·.1)).zip args ++ [(n, .nil)] :=
    List.zip_append (by simpa using hlen.symm)
  constructor
  · intro x τ hget
    obtain ⟨v, hv, hd⟩ := required_lookup hargs hget
    obtain ⟨z, hz⟩ := envGet?_mem hget
    have ht := htys (z, τ) hz
    have hs : stripAlias τ = τ := by cases τ <;> simp_all [stripAlias, isAliasTy]
    have hfind : (((ps.map (·.1)).zip args ++ [(n, Value.nil)]).find? (·.1 == x)).map (·.2) = some v := by
      rw [List.find?_append]
      cases hf : ((ps.map (·.1)).zip args).find? (·.1 == x) with
      | none => rw [hf] at hv; cases hv
      | some p => rw [hf] at hv; simpa using hv
    constructor
    · rw [requiredFrame_getLocal, hzip, hfind, Option.getD_some, hs]
      exact (denM_heap_only (m₁ := m) (m₂ := pushMethodFrame m
        (requiredFrame recv name md (ps.map (·.1) ++ [n]) (args ++ [.nil]))) ht.1 rfl).mp hd
    · intro y ρ hy
      rw [hy] at ht
      simp [isAliasTy] at ht
  · intro x hx
    rw [requiredFrame_getLocal, hzip, List.find?_append]
    have h0 := required_lookup_none hlen hx
    cases hf : ((ps.map (·.1)).zip args).find? (·.1 == x) with
    | some p => rw [hf] at h0; cases h0
    | none =>
      by_cases hxn : n = x
      · subst hxn; simp
      · simp [hxn]

/-- The default runs at the callee frame over the required parameters; its value binds
the optional through `optDefK`, and the body then runs over every parameter. -/
theorem opt_default_chain {κb : Ctx} {ps : List SigParam} {I : Ty} {n : String} {σ τ : Ty}
    {Γb : Env} {d e : Ratchet.Expr} {entry : Machine}
    (he : StateOk κb ps I entry)
    (hd : SemSafeCtxA κb ps I d σ κb ps I)
    (hb : SemSafeCtxA κb (ps ++ [(n, σ)]) I e τ κb Γb I)
    (hafter : envAfter ps n σ = ps ++ [(n, σ)]) (hkill : killClosOverSpine I n σ = I)
    (hcap : capStale n σ σ = false) (hctx : capStaleCtx n σ κb = false)
    (hal : isAliasTy σ = false) :
    RunSpec entry (pushK [.optDefK n [] [] (toRuby e)] (evalFrom entry d)) Γb τ κb I := by
  apply (hd entry he).bindSpec he.rootClean (by intro c hc; simp at hc; subst hc; rfl)
  intro a n1 hr
  cases a with
  | esc j =>
    apply RunSpec.step (by rfl)
      (show Interp.stepFn (deliverA (.esc j) n1 [.optDefK n [] [] (toRuby e)]) =
        .next (deliverA (.esc j) n1 []) from by cases j <;> rfl)
    exact RunSpec.answer ⟨hr.1, hr.2.1, fun _ hv => by cases hv⟩
  | val v =>
    let B := Ratchet.Denote.reCtl n1 (.value v) []
    have hBs : StateOk κb ps I B := StateOk_reCtl (hr.2.2 v rfl) _ _
    have hBd : denM σ B v := denM_reCtl.mpr hr.2.1
    have hs : StateOk κb (ps ++ [(n, σ)]) I (B.setLocal n v) := by
      have h := StateOk_setLocal hBs hBd hcap hctx (ρ := σ)
        (by cases σ <;> simp_all [stripAlias, isAliasTy])
        (by intro y ρ hy; rw [hy] at hal; simp [isAliasTy] at hal)
      rw [show envSet (killClosOver (killAliasesTo ps n) n σ) n σ = envAfter ps n σ from rfl,
        hafter, hkill] at h
      exact h
    apply RunSpec.step (by rfl)
      (show Interp.stepFn (deliverA (.val v) n1 [.optDefK n [] [] (toRuby e)]) =
        .next (evalFrom (B.setLocal n v) e) from rfl)
    exact RunSpec.rebase (hb _ hs) (hr.1.trans ((Framed_reCtl n1 _ []).trans
      (Framed_setLocal B n v (by
        rw [← currentFrame_headD hBs.frameInRange.1]; exact hBs.localAlias))))

#print axioms opt_default_chain
/-- `methodFrame_runSpec` at any start machine below the frame boundary. -/
theorem methodFrame_runSpec_at {m : Machine} {f : RubyCore.Frame} {S : Machine}
    {Γb Γ : Env} {κb κ : Ctx} {Ib I τ : Ty}
    (hl : m.stack.headD 0 < m.frames.size) (hc : f.captured = none)
    (ht : FirstOrder τ = true)
    (hb : RunSpec (pushMethodFrame m f) S Γb τ κb Ib)
    (hs : ∀ n v, ResultOk (pushMethodFrame m f) Γb τ (.val v) n κb Ib →
      StateOk κ Γ I (popMethodFrame n)) (hroot : RootClean m) (hS : RootClean S) :
    RunSpec m (pushK [.frameK m.frames.size] S) Γ τ κ I := by
  apply hb.bindAny hroot hS (by
    intro k hk
    simp only [List.mem_singleton] at hk
    subst hk
    rfl)
  intro a n hr
  exact methodFrame_continue_spec hl hc ht hs hr

theorem opt_method_runSpec {κ : Ctx} {Γ Γb : Env} {I τ σ : Ty} {m : Machine}
    {md : MethodDef} {name n : String} {ps : List SigParam} {args : List Value}
    {d e : Ratchet.Expr} {fr : Option Ratchet.Frame}
    (hm : StateOk κ Γ I m) (ht : ReframeFO κ I) (ha : κ.asms = [])
    (hkont : m.kont = [])
    (hp : md.params = (ps.map (·.1)).map RubyCore.Param.req ++ [.opt n (toRuby d)])
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
    (hargs : (args.length = ps.length ∧ DenAll (ps.map (·.2)) m args) ∨
      (args.length = ps.length + 1 ∧ DenAll ((ps ++ [(n, σ)]).map (·.2)) m args)) :
    ∃ next, Interp.enterUserMethod m m.currentFrame.self name md args none = .next next ∧
      RunSpec m next Γ τ κ I := by
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
  rcases hargs with ⟨hlen, hden⟩ | ⟨hlen, hden⟩
  · have he := enter (ps.map (·.1) ++ [n]) (args ++ [.nil]) ps
      (optOmitted_envOk m _ name md ps n args hlen hden hpsL)
    have hs := methodFrame_runSpec_at hm.frameInRange.2
      (f := requiredFrame m.currentFrame.self name md (ps.map (·.1) ++ [n]) (args ++ [.nil]))
      rfl hτ (opt_default_chain he hd hb hafter hkill hcapS hctx hσ) (pop _ _) hm.rootClean
      hm.rootClean
    refine ⟨_, ?_, hs⟩
    rw [enterUserMethod_optOmitted m _ name md (ps.map (·.1)) n (toRuby d) args hp hcap hdecl
      (by simpa using hlen) hblock hfor]
    simp only [Interp.withKont, pushK, evalFrom, pushMethodFrame, hkont, hbody, List.nil_append]
    rfl
  · have he := enter ((ps ++ [(n, σ)]).map (·.1)) args (ps ++ [(n, σ)])
      (requiredFrame_envOk m _ name md (ps ++ [(n, σ)]) args (by simpa using hlen) hden hps)
    have hs := methodFrame_runSpec hm.frameInRange.2
      (f := requiredFrame m.currentFrame.self name md ((ps ++ [(n, σ)]).map (·.1)) args)
      rfl hτ (hb _ he) (pop _ _) hm.rootClean
    refine ⟨_, ?_, hs⟩
    rw [enterUserMethod_optSupplied m _ name md (ps.map (·.1)) n (toRuby d) args hp hcap hdecl
      (by simpa using hlen) hblock hfor]
    simp only [Interp.withKont, pushK, evalFrom, pushMethodFrame, hkont, hbody, List.nil_append,
      List.map_append, List.map_cons, List.map_nil]

#print axioms opt_method_runSpec
end Ratchet.Denote.Typed
