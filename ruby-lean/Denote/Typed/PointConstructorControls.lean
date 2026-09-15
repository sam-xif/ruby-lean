import Denote.Typed.PointConstructor
import Denote.Typed.PointClassControls
import Ratchet.CtxEq

/-! A completed annotated class run supplies the constructor's whole input world.
No external allocator, dispatch, initializer-code, or body assumption is needed. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed.PointClass
open RubyCore Ratchet Ratchet.Denote

theorem after_class_constructor {Γ : Env} {I : Ty} {m n : Machine}
    {fuel rest : Nat} {v : Value}
    (hm : StateOk ctx0 Γ I m) (hI : FirstOrder I = true)
    (hΓ : ∀ p ∈ Γ, FirstOrder (stripAlias p.2) = true)
    (hr : runA fuel (evalFrom m program) = .ans (.val v) n rest) (x y : Int) :
    ∃ k p, classNamed? n.heap "Point" = some k ∧
      Interp.finishSend n (.ref k) .explicit "new" [.int x, .int y] .none = .next p ∧
      RunSpec m p Γ (.inst "Point" pointInitSpine) callerCtx I := by
  have result := (runSpec hm hI hΓ).2 fuel (.val v) n rest hr
  have hk : n.kont = [] :=
    (congrArg Machine.kont (deliverA_nil_self (answerPoint_of_ans _ _ _ _ _ hr))).symm
  obtain ⟨k, p, hn, hs, hp⟩ := constructor_run (result.2.2 v rfl) hI hΓ hk x y
  exact ⟨k, p, hn, hs, hp.rebase result.1⟩

-- The capability survives both method definitions and restoration of the caller's scope.
#guard entryCtx.pos.plainAlloc == ["Point"]
#guard afterInit.pos.plainAlloc == ["Point"]
#guard callerCtx.pos.plainAlloc == ["Point"]

-- Branch compatibility cannot silently add or remove allocation capabilities.
private def noAllocator : Ctx := { callerCtx with pos := { callerCtx.pos with plainAlloc := [] } }
#guard ctxEqB callerCtx callerCtx
#guard !ctxEqB callerCtx noAllocator
#guard !ctxEqB noAllocator callerCtx

-- Allocation shape alone supplies no method or initializer declaration.
private def allocationOnly : Ctx := { ctx0 with pos := { ctx0.pos with plainAlloc := ["Point"] } }
#guard allocationOnly.classes.isEmpty && allocationOnly.defs.isEmpty
#guard (ctorGet? allocationOnly.classes "Point").isNone

#print axioms after_class_constructor
end Ratchet.Denote.Typed.PointClass
