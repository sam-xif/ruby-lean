import Denote.Sem.ClassShape
import Denote.Sem.ClassNew
import Denote.Typed.MethodEntry

/-! The actual new/initialize interception and required-parameter frame. This does not
certify an initializer body: its annotated InitState/run obligation is separate. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

def ctorAllocated (m : Machine) (k : ObjId) : Machine :=
  { m with heap := pushHeap m.heap { klass := k }, kont := .newK (.ref m.heap.objs.size) :: m.kont }

theorem finishSend_constructor {m : Machine} {k : ObjId} {md : MethodDef} {args : List Value}
    (hc : OrdinaryClass m.heap k) (hd : NewDispatch m.heap (classOf m.heap (.ref k)))
    (hmath : k ≠ Boot.mathId) (hi : Interp.userInit? m.heap k = some md) :
    Interp.finishSend m (.ref k) .explicit "new" args .none =
      Interp.enterUserMethod (ctorAllocated m k) (.ref m.heap.objs.size) "initialize" md args none := by
  obtain ⟨cp, hp, hm⟩ := hc.payload
  simp only [Interp.finishSend]
  rw [Interp.invoke.eq_def]
  simp only [show ("new" == "send") = false from rfl,
    show ("new" == "public_send") = false from rfl,
    show ("new" == "__send__") = false from rfl,
    show ("new" == "escape") = false from rfl,
    show ("new" == "quote") = false from rfl,
    show ("new" == "union") = false from rfl,
    Bool.false_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hp,
    beq_eq_false_iff_ne.mpr hmath, Bool.and_false]
  simp only [Interp.invoke.invokeMaybeNew]
  have hn := hd.no_userNew
  simp only [hm, beq_self_eq_true, Bool.not_false, Bool.true_and, Bool.not_eq_true']
  split
  · rename_i e he
    simp only [he] at hn
    split
    · simp only [hi, hc.noCore, hc.noPayload]; rfl
    · rename_i h
      exact False.elim (h hn)
  · simp only [↓reduceIte, hi, hc.noCore, hc.noPayload]; rfl

theorem constructor_required_entry {m : Machine} {k : ObjId} {md : MethodDef}
    {args : List Value} {names : List String}
    (hc : OrdinaryClass m.heap k) (hd : NewDispatch m.heap (classOf m.heap (.ref k)))
    (hmath : k ≠ Boot.mathId) (hi : Interp.userInit? m.heap k = some md)
    (hp : md.params = names.map RubyCore.Param.req) (hcap : md.capturedFrame = none)
    (hdecl : md.declared = []) (ha : args.length = names.length) :
    Interp.finishSend m (.ref k) .explicit "new" args .none =
      .next (Interp.withKont
        (pushMethodFrame (ctorAllocated m k)
          (requiredFrame (.ref m.heap.objs.size) "initialize" md names args))
        (.eval md.body) (.frameK m.frames.size)) := by
  rw [finishSend_constructor hc hd hmath hi]
  exact enterUserMethod_required _ _ _ _ _ _ hp hcap hdecl ha

#print axioms finishSend_constructor
#print axioms constructor_required_entry
end Ratchet.Denote.Typed
