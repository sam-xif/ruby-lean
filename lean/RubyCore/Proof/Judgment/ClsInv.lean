import RubyCore.Proof.Judgment.Konts
import RubyCore.Proof.Static.ClsValues

/-!
# The J-invariant's structures across a class allocation (J43 / W2c, third half)

The `ClsGrow` congruence suite lifted to the invariant's own structures:
`VTy`/`VTys`, `FrameConformsJ`/`FramesOkJ`, `StackCtx`, `GlobalsOk`, `KontOkJ`.
Everything is at *old* ids, with the bounds coming out of the facts each clause
already carries (`classPayload?_isSome_lt`, `plainRecv`'s own size test) — the
same discipline as the `TypeAgree` congruences, one relation over.
-/

namespace RubyCore
namespace Proof
namespace Judgment

open Interp
open RubyCore.Types
open RubyCore.Judgment
open RubyCore.Proof.Static

variable {h h' : Heap}

theorem VTy.clsGrow (hg : ClsGrow h h') (hch : ChainsIn h) {v : Value} {τ : Ty}
    (hv : VTy h v τ) : VTy h' v τ := by
  obtain ⟨σ, hvt, hsub⟩ := hv
  exact ⟨σ, ClsGrow.valueTy_old hg hch hvt, hsub⟩

theorem VTys.clsGrow (hg : ClsGrow h h') (hch : ChainsIn h) :
    ∀ {vs : List Value} {τs : List Ty}, VTys h vs τs → VTys h' vs τs
  | [], [], hv => hv
  | _ :: _, _ :: _, hv => ⟨VTy.clsGrow hg hch hv.1, VTys.clsGrow hg hch hv.2⟩
  | [], _ :: _, hv => absurd hv (by simp [VTys])
  | _ :: _, [], hv => absurd hv (by simp [VTys])

theorem FrameConformsJ.clsGrow (hg : ClsGrow h h') (hch : ChainsIn h)
    {frames : Array Frame} {Γ : Env} {fid : FrameId}
    (hc : FrameConformsJ h frames Γ fid) : FrameConformsJ h' frames Γ fid := by
  refine ⟨hc.1, ?_, fun x τ hx => VTy.clsGrow hg hch (hc.2.2 x τ hx)⟩
  rw [hg.classPayload?_isSome_old (classPayload?_isSome_lt hc.2.1)]
  exact hc.2.1

theorem FramesOkJ.clsGrow (hg : ClsGrow h h') (hch : ChainsIn h)
    {frames : Array Frame} :
    ∀ {fids : List FrameId} {Γs : List Env},
      FramesOkJ h frames fids Γs → FramesOkJ h' frames fids Γs
  | [], [], hf => hf
  | _ :: _, _ :: _, hf =>
      ⟨hf.1, hf.2.1, FrameConformsJ.clsGrow hg hch hf.2.2.1,
       FramesOkJ.clsGrow hg hch hf.2.2.2⟩
  | [], _ :: _, hf => absurd hf (by simp [FramesOkJ])
  | _ :: _, [], hf => absurd hf (by simp [FramesOkJ])

theorem GlobalsOk.clsGrow (hg : ClsGrow h h') (hch : ChainsIn h) {D : Decls}
    {gs : List (String × Value)} (hgl : GlobalsOk D h gs) : GlobalsOk D h' gs := by
  intro x p σ hpg hf hgt
  exact ClsGrow.valueTy_old hg hch (hgl x p σ hpg hf hgt)

set_option maxHeartbeats 1000000 in
/-- `StackCtx` across a class allocation — `StackCtx.heap_congr`, one relation
    over: the chain half runs on `ancestors_old` (the id bounds coming out of
    `valueTy_ref_lt` and membership), everything else on the pinned reads. -/
theorem StackCtx.clsGrow (hg : ClsGrow h h') (hch : ChainsIn h) (hsat : Saturated h)
    {frames : Array Frame} :
    ∀ {st : List FrameId} {cs : List FrameCtx},
      StackCtx h frames st cs → StackCtx h' frames st cs
  | [], [], hs => hs
  | fid :: fids, c :: cs, hs => by
      have hlt : (frames.getD fid default).defmod < h.objs.size :=
        classPayload?_isSome_lt hs.1
      refine ⟨?_, ?_, hs.2.2.1, fun sc hsc => ?_,
        hs.2.2.2.2.1, hs.2.2.2.2.2.1, hs.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2.1,
        hs.2.2.2.2.2.2.2.2.1,
        StackCtx.clsGrow hg hch hsat hs.2.2.2.2.2.2.2.2.2⟩
      · rw [hg.classPayload?_isSome_old hlt]; exact hs.1
      · rw [hg.className_old hlt]; exact hs.2.1
      · obtain ⟨hv, hchain⟩ := hs.2.2.2.1 sc hsc
        refine ⟨ClsGrow.valueTy_old hg hch hv, ?_⟩
        -- membership is the bound (`classOf_lt_of_mem_ancestors`)
        have hkb : classOf h (frames.getD fid default).self < h.objs.size :=
          classOf_lt_of_mem_ancestors hs.1 hchain
        have hco : classOf h' (frames.getD fid default).self
            = classOf h (frames.getD fid default).self := by
          cases hsv : (frames.getD fid default).self with
          | ref o =>
            rw [hsv] at hv
            exact hg.classOf_old hch
              (valueTy_ref_lt (by simp [subTy]) (by simp [subTy]) hv)
          | bool b => cases b <;> rfl
          | _ => rfl
        rw [hco, ClsGrow.ancestors_old hg hch hsat hkb]
        exact hchain
  | [], _ :: _, hs => hs.elim
  | _ :: _, [], hs => hs.elim

/-- `KontOkJ.heap_congr'`, one relation over: only `argsK` stores heap facts
    (`VTy`/`VTys` on the receiver and the evaluated prefix), and those cross by
    `VTy.clsGrow`; every other constructor is structural. -/
theorem KontOkJ.clsGrow {ans : Ty} {A : SemAxioms} :
    ∀ {D : Decls} {Γs : List (JCtx × Env)} {τ : Ty} {k : List Kont},
      KontOkJ ans A D h Γs τ k → ClsGrow h h' → ChainsIn h →
      KontOkJ ans A D h' Γs τ k := by
  intro D Γs τ k hk
  induction hk with
  | nil hsub hr hl => intro _ _; exact .nil hsub hr hl
  | seqNil hw _ hsu ih => intro hg hch; exact .seqNil hw (ih hg hch) hsu
  | seqCons hm hs hw _ hsu ih => intro hg hch; exact .seqCons hm hs hw (ih hg hch) hsu
  | asgn hib hw _ hsu ih => intro hg hch; exact .asgn hib hw (ih hg hch) hsu
  | cpathK hb hsco hsw _ hsu ih =>
      intro hg hch; exact .cpathK hb hsco hsw (ih hg hch) hsu
  | retValK hσ hms hsub _ hsu ih =>
      intro hg hch; exact .retValK hσ hms hsub (ih hg hch) hsu
  | casgnK hct hsct hrd hsub _ hsu ih =>
      intro hg hch; exact .casgnK hct hsct hrd hsub (ih hg hch) hsu
  | hshKeyK hfv hmv hfp hmk hmvs hjv hpr hw _ hsu ih =>
      intro hg hch; exact .hshKeyK hfv hmv hfp hmk hmvs hjv hpr hw (ih hg hch) hsu
  | hshValK hfp hmk hmvs hpr hw _ hsu ih =>
      intro hg hch; exact .hshValK hfp hmk hmvs hpr hw (ih hg hch) hsu
  | ifElseK hft hfe hmt hme ht he hjt hje hct hce hw _ hsu ih =>
      intro hg hch
      exact .ifElseK hft hfe hmt hme ht he hjt hje hct hce hw (ih hg hch) hsu
  | ifNoneK hft hmt ht hjt hjn hct hce hw _ hsu ih =>
      intro hg hch; exact .ifNoneK hft hmt ht hjt hjn hct hce hw (ih hg hch) hsu
  | whileCond hl hw _ hsu ih => intro hg hch; exact .whileCond hl hw (ih hg hch) hsu
  | whileBody hl hw _ hsu ih => intro hg hch; exact .whileBody hl hw (ih hg hch) hsu
  | recvK hfm hm hargs hsg hsub hw _ hsu ih =>
      intro hg hch; exact .recvK hfm hm hargs hsg hsub hw (ih hg hch) hsu
  | recvK0 hsg hw _ hsu ih => intro hg hch; exact .recvK0 hsg hw (ih hg hch) hsu
  | argsK hrv hva hst hfm hm hrest hsr hsg hw _ hsu ih =>
      intro hg hch
      exact .argsK (VTy.clsGrow hg hch hrv) (VTys.clsGrow hg hch hva) hst hfm hm
        hrest hsr hsg hw (ih hg hch) hsu
  | frameK hrt hil _ ih => intro hg hch; exact .frameK hrt hil (ih hg hch)
  | asgnIvar hsc hw hcf _ hsu ih =>
      intro hg hch; exact .asgnIvar hsc hw hcf (ih hg hch) hsu
  | asgnGvar hpg hgt hcf hw _ hsu ih =>
      intro hg hch; exact .asgnGvar hpg hgt hcf hw (ih hg hch) hsu
  | ifNarrowElseK hft hfe hmt hme hget ht he hjt hje2 hct hce hs0 hT hFn hFf hjw _ hsu ih =>
      intro hg hch
      exact .ifNarrowElseK hft hfe hmt hme hget ht he hjt hje2 hct hce hs0 hT hFn hFf
        hjw (ih hg hch) hsu
  | ifNarrowNoneK hft hmt hget ht hjt hjn hct hcb hs0 hT hjw _ hsu ih =>
      intro hg hch
      exact .ifNarrowNoneK hft hmt hget ht hjt hjn hct hcb hs0 hT hjw (ih hg hch) hsu
  | arrK hfm hm hje hw _ hsu ih => intro hg hch; exact .arrK hfm hm hje hw (ih hg hch) hsu

end Judgment
end Proof
end RubyCore
