import Denote.Typed.Controls

/-! Constructor-wise builders for proof-term-audited corpus derivations. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem derivD_fltLit {Γ : Env} {b : UInt64} : (DJudgeC dclinks).judge Γ (.flt b) .float Γ :=
  fun _ hF => hF DClink.fltLit (by simp [dclinks])

theorem derivD_strLit {Γ : Env} {s : String} :
    (DJudgeC dclinks).judge Γ (.str s) (.cls "String") Γ :=
  fun _ hF => hF DClink.strLit (by simp [dclinks])

theorem derivD_symLit {Γ : Env} {s : String} : (DJudgeC dclinks).judge Γ (.sym s) .sym Γ :=
  fun _ hF => hF DClink.symLit (by simp [dclinks])

theorem derivD_truLit {Γ : Env} : (DJudgeC dclinks).judge Γ .tru .bool Γ :=
  fun _ hF => hF DClink.truLit (by simp [dclinks])

theorem derivD_flsLit {Γ : Env} : (DJudgeC dclinks).judge Γ .fls .bool Γ :=
  fun _ hF => hF DClink.flsLit (by simp [dclinks])

theorem derivD_nilLit {Γ : Env} : (DJudgeC dclinks).judge Γ .nil .nilT Γ :=
  fun _ hF => hF DClink.nilLit (by simp [dclinks])

theorem derivD_var {Γ : Env} {x : String} {τ : Ty}
    (hg : envGet? Γ x = some τ) (ha : isAliasTy τ = false) :
    (DJudgeC dclinks).judge Γ (.var .lvar x) τ Γ :=
  fun _ hF => hF DClink.var (by simp [dclinks]) hg ha

theorem derivD_vasgn {Γ Γ' : Env} {x : String} {e : Ratchet.Expr} {τ : Ty}
    (he : (DJudgeC dclinks).judge Γ e τ Γ')
    (hc : capStale x τ τ = false) (ha : isAliasTy τ = false) :
    (DJudgeC dclinks).judge Γ (.vasgn .lvar x e) τ (envAfter Γ' x τ) :=
  fun F hF => hF DClink.vasgn (by simp [dclinks]) (he F hF) hc ha rfl

theorem derivD_seq {Γ Γ' : Env} {es : List Ratchet.Expr} {τ : Ty}
    (he : (DJudgeC dclinks).seq Γ es τ Γ') :
    (DJudgeC dclinks).judge Γ (.seq es) τ Γ' :=
  fun F hF => hF DClink.seq (by simp [dclinks]) (he F hF)

theorem derivD_seqLast {Γ Γ' : Env} {e : Ratchet.Expr} {τ : Ty}
    (he : (DJudgeC dclinks).judge Γ e τ Γ') : (DJudgeC dclinks).seq Γ [e] τ Γ' :=
  fun F hF => hF DClink.DJudgeSeq.last (by simp [dclinks]) (he F hF)

theorem derivD_seqCons {Γ Γ₁ Γ₂ : Env} {e e' : Ratchet.Expr} {es : List Ratchet.Expr}
    {σ τ : Ty} (he : (DJudgeC dclinks).judge Γ e σ Γ₁)
    (ht : (DJudgeC dclinks).seq Γ₁ (e' :: es) τ Γ₂) :
    (DJudgeC dclinks).seq Γ (e :: e' :: es) τ Γ₂ :=
  fun F hF => hF DClink.DJudgeSeq.cons (by simp [dclinks]) (he F hF) (ht F hF)

theorem derivD_allNil {Γ : Env} : (DJudgeC dclinks).all Γ [] [] Γ :=
  fun _ hF => hF DClink.DJudgeAll.nil (by simp [dclinks])

theorem derivD_allCons {Γ Γ₁ Γ₂ : Env} {e : Ratchet.Expr} {es : List Ratchet.Expr}
    {τ : Ty} {tys : List Ty} (he : (DJudgeC dclinks).judge Γ e τ Γ₁)
    (ht : (DJudgeC dclinks).all Γ₁ es tys Γ₂) (hp : plainArgB e = true) :
    (DJudgeC dclinks).all Γ (e :: es) (τ :: tys) Γ₂ :=
  fun F hF => hF DClink.DJudgeAll.cons (by simp [dclinks]) (he F hF) (ht F hF) hp

theorem derivD_prim {Γ Γ₁ Γ₂ : Env} {recv : Ratchet.Expr} {name : String}
    {args : List Ratchet.Expr} {σ τ : Ty} {tys : List Ty}
    (hr : (DJudgeC dclinks).judge Γ recv σ Γ₁) (ha : (DJudgeC dclinks).all Γ₁ args tys Γ₂)
    (hp : DPrim σ name tys τ) :
    (DJudgeC dclinks).judge Γ (.send (some recv) name args none) τ Γ₂ :=
  fun F hF => hF DClink.prim (by simp [dclinks]) (hr F hF) (ha F hF) hp rfl (by intro; rfl)

theorem derivD_if {Γ Γc Γ₁ Γ₂ : Env} {c t e : Ratchet.Expr} {σ τ₁ τ₂ : Ty}
    (hc : (DJudgeC dclinks).judge Γ c σ Γc) (ht : (DJudgeC dclinks).judge Γc t τ₁ Γ₁)
    (he : (DJudgeC dclinks).judge Γc e τ₂ Γ₂) :
    (DJudgeC dclinks).judge Γ (.if' c t (some e)) (joinT τ₁ τ₂) (joinEnv Γ₁ Γ₂) :=
  fun F hF => hF DClink.if' (by simp [dclinks]) (hc F hF) (ht F hF) (he F hF)

theorem derivD_ifNoElse {Γ Γc Γt : Env} {c t : Ratchet.Expr} {σ τ : Ty}
    (hc : (DJudgeC dclinks).judge Γ c σ Γc) (ht : (DJudgeC dclinks).judge Γc t τ Γt) :
    (DJudgeC dclinks).judge Γ (.if' c t none) (joinT τ .nilT) (joinEnv Γt Γc) :=
  fun F hF => hF DClink.ifNoElse (by simp [dclinks]) (hc F hF) (ht F hF)

theorem derivD_bareName {Γ : Env} : (DJudgeC dclinks).judge Γ (.vcall "x") .any Γ :=
  fun _ hF => hF DClink.bareName (by simp [dclinks]) rfl rfl rfl

theorem derivD_arrayLit {Γ Γ' : Env} {es : List Ratchet.Expr} {tys : List Ty}
    (hs : (DJudgeC dclinks).all Γ es tys Γ') (hf : FirstOrder (elemTy tys) = true) :
    (DJudgeC dclinks).judge Γ (.array es) (.arrayOf (elemTy tys)) Γ' :=
  fun F hF => hF DClink.arrayLit (by simp [dclinks]) (hs F hF) hf

theorem derivD_pairsNil {Γ : Env} : (DJudgeC dclinks).pairs Γ [] [] [] Γ :=
  fun _ hF => hF DClink.DJudgePairs.nil (by simp [dclinks])

theorem derivD_pairsCons {Γ Γk Γv Γ' : Env} {k v : Ratchet.Expr}
    {ps : List (Ratchet.Expr × Ratchet.Expr)} {σ τ : Ty} {ks vs : List Ty}
    (hk : (DJudgeC dclinks).judge Γ k σ Γk) (hv : (DJudgeC dclinks).judge Γk v τ Γv)
    (hs : (DJudgeC dclinks).pairs Γv ps ks vs Γ') :
    (DJudgeC dclinks).pairs Γ ((k, v) :: ps) (σ :: ks) (τ :: vs) Γ' :=
  fun F hF => hF DClink.DJudgePairs.cons (by simp [dclinks]) (hk F hF) (hv F hF) (hs F hF)

theorem derivD_hashLit {Γ Γ' : Env} {ps : List (Ratchet.Expr × Ratchet.Expr)} {ks vs : List Ty}
    (hs : (DJudgeC dclinks).pairs Γ ps ks vs Γ') (hk : FirstOrder (elemTy ks) = true)
    (hv : FirstOrder (elemTy vs) = true) :
    (DJudgeC dclinks).judge Γ (.hash ps) (.hashOf (elemTy ks) (elemTy vs)) Γ' :=
  fun F hF => hF DClink.hashLit (by simp [dclinks]) (hs F hF) hk hv

end Ratchet.Denote.Typed
