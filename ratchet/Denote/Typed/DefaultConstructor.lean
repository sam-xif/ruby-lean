import Denote.Typed.DefaultAllocation
import Denote.Sem.RootLookup

/-! The real default-constructor dispatch. Full conformance and the existing def table
derive root absence; positive new lookup remains a separate dispatch obligation. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem finishSend_no_initializer {m : Machine} {k : ObjId} {args : List Value}
    (hc : PlainAllocator m.heap k) (hi : Interp.userInit? m.heap k = none) :
    Interp.finishSend m (.ref k) .explicit "new" args .none =
      Interp.invoke.invokeDispatch m (.ref k) .explicit "new" args none [] := by
  obtain ⟨cp, hp, _⟩ := hc.payload
  simp only [Interp.finishSend]
  rw [Interp.invoke.eq_def]
  simp only [show ("new" == "send") = false from rfl,
    show ("new" == "public_send") = false from rfl,
    show ("new" == "__send__") = false from rfl,
    show ("new" == "escape") = false from rfl,
    show ("new" == "quote") = false from rfl,
    show ("new" == "union") = false from rfl,
    Bool.false_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hp,
    beq_eq_false_iff_ne.mpr hc.notMath, Bool.and_false]
  simp only [Interp.invoke.invokeMaybeNew, hi]
  split <;> simp only [ite_self]

theorem class_new_builtin (m : Machine) (k : ObjId) (hc : PlainAllocator m.heap k) :
    Builtins.run "Class#new" (.ref k) [] m = Builtins.newImpl m (.ref k) [] := by
  obtain ⟨cp, hp, _⟩ := hc.payload
  have hbyte : Builtins.unrepresentableByteStr m.heap (.ref k) = false := by
    simp [Builtins.unrepresentableByteStr, Builtins.strPayload?, hp]
  simp only [Builtins.run, List.any_cons, List.any_nil, hbyte, Bool.false_or,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem default_constructor_resolved {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {k owner : ObjId} {md : MethodDef} {cn : String}
    (hm : StateOk κ Γ I m) (hc : PlainAllocator m.heap k) (hn : classNamed? m.heap cn = some k)
    (hd : NewDispatch m.heap (classOf m.heap (.ref k)))
    (hl : Interp.methodOn m.heap (classOf m.heap (.ref k)) "new" = some (owner, md))
    (hi : Interp.userInit? m.heap k = none) (hk : m.kont = []) :
    StepSpec m Γ (.inst cn .ivar0) (Interp.finishSend m (.ref k) .explicit "new" [] .none) κ I := by
  obtain ⟨hb, hu, hv, hp, hs⟩ := hd.found owner md hl
  rw [finishSend_no_initializer hc hi,
    invokeDispatch_builtin (by simpa only [lookup_eq_methodOn] using hl) hb hu hv hp hs
      (by rfl) (by rfl)]
  change StepSpec m Γ (.inst cn .ivar0) (builtinStep (Builtins.run "Class#new" (.ref k) [] m)) κ I
  rw [class_new_builtin m k hc]
  exact newImpl_default_step hm hc hn hk

/-- Both the declared prefix and root table are checked. Root absence follows from full
conformance; positive new lookup is still explicit before checker admission. -/
theorem declared_default_constructor {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine}
    {c : Cls} {k owner : ObjId} {md : MethodDef}
    (hm : StateOk κ Γ I m) (hc : c ∈ κ.classes) (hn : classNamed? m.heap c.name = some k)
    (halloc : c.name ∈ κ.pos.plainAlloc) (hnew : smroGet? κ.classes c.name "new" = none)
    (hprefix : noDeclaredSelectorB κ.classes c.name "initialize" = true)
    (hroot : rootInitFreeB κ.defs = true)
    (hl : Interp.methodOn m.heap (classOf m.heap (.ref k)) "new" = some (owner, md))
    (hk : m.kont = []) :
    StepSpec m Γ (.inst c.name .ivar0) (Interp.finishSend m (.ref k) .explicit "new" [] .none) κ I := by
  obtain ⟨j, hj, hp⟩ := hm.allocators c.name halloc
  have he : j = k := Option.some.inj (hj.symm.trans hn)
  subst j
  have hd := (hm.declCls c hc k hn).2.2.2.2.1 hnew
  exact default_constructor_resolved hm hp hn ⟨hd.1, hd.2⟩ hl
    (hm.userInit_none hc hn hprefix hroot) hk

#print axioms default_constructor_resolved
#print axioms declared_default_constructor
end Ratchet.Denote.Typed
