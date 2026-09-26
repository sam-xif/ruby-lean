import Denote.Rules.Method.MethodEntry

/-! Ordinary required-positionals with an implicitly supplied block. The block is kept
in the real method frame even when the definition has no explicit &b local. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

def requiredBlockFrame (recv : Value) (name : String) (md : MethodDef)
    (names : List String) (args : List Value) (blk : Option Value) : RubyCore.Frame :=
  { requiredFrame recv name md names args with blk := blk, callBlk := blk }

theorem enterUserMethod_required_block (m : Machine) (recv : Value) (name : String)
    (md : MethodDef) (names : List String) (args : List Value) (blk : Option Value)
    (hp : md.params = names.map RubyCore.Param.req)
    (hc : md.capturedFrame = none) (hd : md.declared = [])
    (ha : args.length = names.length) :
    Interp.enterUserMethod m recv name md args blk =
      .next (Interp.withKont (pushMethodFrame m (requiredBlockFrame recv name md names args blk))
        (.eval md.body) (.frameK m.frames.size)) := by
  unfold Interp.enterUserMethod
  rw [hp, classifyFull_required]
  have hf : (names.zip args).filter (fun _ => true) = names.zip args :=
    List.filter_eq_self.mpr (fun _ _ => rfl)
  simp [Interp.appendKwHash, hc, hd, ← ha, requiredBlockFrame, requiredFrame, pushMethodFrame,
    Interp.withKont, Interp.withCtl, hp, hf]

#print axioms enterUserMethod_required_block
end Ratchet.Denote.Typed
