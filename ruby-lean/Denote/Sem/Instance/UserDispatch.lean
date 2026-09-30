import Denote.Sem.Names.DispatchName

/-! Resolved user-method dispatch. The prefix before the owner must be free of
native shadows, but a user definition at its owner takes precedence. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem invokeDispatch_userMethod {m : Machine} {recv : Value} {site : SendSite}
    {name : String} {md : MethodDef} {owner : ObjId} {args : List Value}
    {blk : Option Value} {kw : List (Value × Value)}
    (hl : lookup m.heap recv name = some (owner, md))
    (hb : md.builtin = none) (hu : md.undefined = false) (hp : md.fromPrelude = false)
    (hv : Interp.visError? m recv site md name = none)
    (hs : Interp.crubyShadow m.heap
      ((ancestors m.heap (classOf m.heap recv)).takeWhile (· != owner)) name = none) :
    Interp.invoke.invokeDispatch m recv site name args blk kw =
      Interp.enterUserMethod m recv name md args blk kw := by
  simp only [Interp.invoke.invokeDispatch, hl, hu, hp, Bool.false_eq_true, ↓reduceIte,
    Interp.crubyResolvedShadow, hb, Option.any, hs, hv]

/-- Ordinary objects have no Proc/Hash/Class interception. A found entry also
shadows the reflective `send` family, so no method-name blacklist is necessary. -/
theorem invoke_ordinary_userMethod {m : Machine} {o owner : ObjId} {site : SendSite}
    {name : String} {md : MethodDef} {args : List Value} {blk : Option Value}
    {kw : List (Value × Value)}
    (ho : (m.heap.get o).payload = .none)
    (hl : lookup m.heap (.ref o) name = some (owner, md))
    (hb : md.builtin = none) (hu : md.undefined = false) (hp : md.fromPrelude = false)
    (hv : Interp.visError? m (.ref o) site md name = none)
    (hs : Interp.crubyShadow m.heap
      ((ancestors m.heap (classOf m.heap (.ref o))).takeWhile (· != owner)) name = none) :
    Interp.invoke m (.ref o) site name args blk kw =
      Interp.enterUserMethod m (.ref o) name md args blk kw := by
  unfold Interp.invoke
  simp only [hl, Option.isNone, Bool.and_false, Bool.false_eq_true, ↓reduceIte, ho]
  exact invokeDispatch_userMethod hl hb hu hp hv hs

theorem invoke_direct_userMethod {m : Machine} {o owner : ObjId} {site : SendSite}
    {name : String} {md : MethodDef} {args : List Value}
    (hn : DirectSendName name)
    (hl : lookup m.heap (.ref o) name = some (owner, md))
    (hb : md.builtin = none) (hu : md.undefined = false) (hp : md.fromPrelude = false)
    (hv : Interp.visError? m (.ref o) site md name = none)
    (hs : Interp.crubyShadow m.heap
      ((ancestors m.heap (classOf m.heap (.ref o))).takeWhile (· != owner)) name = none) :
    Interp.invoke m (.ref o) site name args none [] =
      Interp.enterUserMethod m (.ref o) name md args none := by
  have hn' := hn.payload
  simp only [payloadSendNames, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn'
  obtain ⟨_, _, hindex, _, _, hescape, hquote, hunion, hsqrt, hexp, hlog⟩ := hn'
  have hd := invokeDispatch_userMethod (args := args) (blk := none) (kw := [])
    hl hb hu hp hv hs
  unfold Interp.invoke
  simp only [hl, Option.isNone, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  cases he : (m.heap.get o).payload <;>
    simp only [
      beq_eq_false_iff_ne.mpr hescape, beq_eq_false_iff_ne.mpr hquote,
      beq_eq_false_iff_ne.mpr hunion, Bool.false_or, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte]
  all_goals first | exact hd | skip
  all_goals split <;> simp_all

#print axioms invokeDispatch_userMethod
#print axioms invoke_ordinary_userMethod
#print axioms invoke_direct_userMethod
end Ratchet.Denote.Typed
