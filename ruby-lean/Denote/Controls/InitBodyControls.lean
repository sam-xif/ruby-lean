import Denote.Rules.Init.InitWrite
import Ratchet.Controls.WriteControls

/-! The complete 061 initializer body, from its Integer parameter annotations.
This is a semantic body pilot, not class/constructor admission by the validator.
-/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

def pointInitParams : Env := [("x", .int), ("y", .int)]
def pointInitBody : Ratchet.Expr :=
  .seq [.vasgn .ivar "@x" (.var .lvar "x"), .vasgn .ivar "@y" (.var .lvar "y")]
def pointInitSpine : Ty := .ivarCons "@x" .int (.ivarCons "@y" .int .ivar0)

/-- No call arguments occur in the theorem: the full body uses the annotated domain. -/
theorem point_initializer_sem {κ : Ctx} {cn : String}
    (hs : κ.selfTy = some (.inst cn .ivar0)) (hb : κ.blockTy = none) (hc : κ.consts = []) :
    SemInitA κ pointInitParams .ivar0 pointInitBody .any κ pointInitParams pointInitSpine := by
  have hx : SemInitA κ pointInitParams .ivar0 (.vasgn .ivar "@x" (.var .lvar "x")) .int
      κ pointInitParams (.ivarCons "@x" .int .ivar0) :=
    SemInitA.ivarAsgnChecked (SemInitA.var rfl rfl) (by
      simp [writeTypesB, pointInitParams, IvarStable, stripAlias, writeFieldsB, spineKeys, hs, hb, hc])
  have hy : SemInitA κ pointInitParams (.ivarCons "@x" .int .ivar0)
      (.vasgn .ivar "@y" (.var .lvar "y")) .int κ pointInitParams pointInitSpine :=
    SemInitA.ivarAsgnChecked (x := "@y") (SemInitA.var rfl rfl) (by
      simp [writeTypesB, pointInitParams, IvarStable, stripAlias, writeFieldsB, spineKeys, ivarGet?, hs, hb, hc])
  exact (SemInitA.sequence (.cons hx (.last hy))).ignoreResult

-- Discarding the result never discards outgoing conformance or all-fuel safety.
theorem point_initializer_safe {anchor : Heap} {κ : Ctx} {cn : String} {m : Machine}
    (hs : κ.selfTy = some (.inst cn .ivar0)) (hb : κ.blockTy = none) (hc : κ.consts = [])
    (hm : InitState anchor κ pointInitParams .ivar0 m) : StuckFree m pointInitBody :=
  (point_initializer_sem hs hb hc anchor m hm).1

theorem point_initializer_self_type {anchor : Heap} {κ : Ctx} {cn : String} {m n : Machine}
    {fuel rest : Nat} {v : Value}
    (hs : κ.selfTy = some (.inst cn .ivar0)) (hb : κ.blockTy = none) (hc : κ.consts = [])
    (hm : InitState anchor κ pointInitParams .ivar0 m)
    (hr : runA fuel (evalFrom m pointInitBody) = .ans (.val v) n rest) :
    denM (.inst cn pointInitSpine) n n.currentFrame.self := by
  have hn := ((point_initializer_sem hs hb hc anchor m hm).2 fuel (.val v) n rest hr).2.2 v rfl
  have ht := hn.typed.selfTy
  simp only [SelfTyOk, hs, denM, denSpineFrom, and_true] at ht
  rw [denM]
  exact ⟨ht, hn.typed.selfSpine.1⟩

-- The guard also justifies a typed collection parameter and a non-void return.
example {κ : Ctx} {cn : String}
    (hs : κ.selfTy = some (.inst cn .ivar0)) (hb : κ.blockTy = none) (hc : κ.consts = []) :
    SemInitA κ [("items", .arrayOf .int)] .ivar0
      (.vasgn .ivar "@items" (.var .lvar "items")) (.arrayOf .int)
      κ [("items", .arrayOf .int)] (.ivarCons "@items" (.arrayOf .int) .ivar0) :=
  SemInitA.ivarAsgnChecked (x := "@items") (SemInitA.var rfl rfl) (by
    simp [writeTypesB, IvarStable, stripAlias, writeFieldsB, spineKeys, hs, hb, hc])

-- Updating a visible binding does not revive its shadowed, differently typed duplicate.
example {m : Machine} {o : ObjId} (hs : m.currentFrame.self = .ref o)
    (ho : o < m.heap.objs.size)
    (hi : SelfSpineOk (.ivarCons "@x" .nilT (.ivarCons "@x" .bool .ivar0)) m) :
    SelfSpineOk (.ivarCons "@x" .int (.ivarCons "@x" .bool .ivar0))
      (Interp.bindIvar m "@x" (.int 1)) :=
  selfSpine_bindIvar (x := "@x") (ρ := .int) (v := .int 1) hs ho hi (by simp [denM, isIntV]) (by
    intro y τ hy hg
    simp [ivarGet?, Ne.symm hy] at hg)

-- The scoped run contract cannot claim a wrong type, even at execution bound zero.
example (anchor : Heap) (origin m : Machine) (κ : Ctx) (Γ : Env) (I : Ty) :
    ¬ InitRunSpec anchor origin (deliverA (.val (.int 1)) m []) Γ .bool κ I := by
  intro h
  have hr := h.2 0 (.val (.int 1)) (deliverA (.val (.int 1)) m []) 0 (by
    rw [runA_ans (by rfl)])
  have hb := hr.2.1
  simp only [AnsOk, denM, isBoolV, Bool.false_eq_true] at hb

#print axioms point_initializer_sem
#print axioms point_initializer_safe
#print axioms point_initializer_self_type
end Ratchet.Denote.Typed
