import Denote.Bridge
import Denote.Examples.Derivations
import Denote.Clink.Certify
import Denote.Sem.Closure.Dispatch

/-! Optional completeness of the full authoring judgments. These helpers
certify raw DJudge/Certified/body proofs, which can use any authoring constructor
and therefore require every clink. The actual validateD safety theorems live in
Bridge.lean and consume enabled evidence instead. Existing complete-registry
method/instance/control clients import this module explicitly. -/

set_option autoImplicit false

namespace Ratchet.Denote.Typed

open RubyCore Ratchet Ratchet.Denote

/-! ## §1 Fourteen-family mutual induction, using the initializer registry bridge -/

/-- **Every syntactic derivation is a certified one.** The registry covers `DJudge`, so the
judgment `check` returns lands in the judgment `dregistry_safe` consumes. -/
theorem djudge_certified {κ κ' : Ctx} {I I' : Ty} {Γ Γ' : Env} {e : Ratchet.Expr} {τ : Ty}
    (h : DJudge Γ e τ Γ' κ I κ' I') : (DJudgeC dclinks).judge Γ e τ Γ' κ I κ' I' := by
  intro F hF
  certify_djudgments DJudge.rec h F hF

/-- Callback methods cross the same registry, uniformly over the entire declared signature. -/
theorem dmethod_certified {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret τ : Ty}
    {Γ Γ' : Env} {e : Ratchet.Expr} (h : DMethod κ I fr ps ret Γ e τ Γ') :
    (DJudgeC dclinks).method κ I fr ps ret Γ e τ Γ' := by
  intro F hF
  certify_djudgments DMethod.rec h F hF

/-- Fundamental lemma at arbitrary method contexts, not just the top-level specialization. -/
theorem djudge_context {κ κ' : Ctx} {I I' : Ty} {Γ Γ' : Env} {e : Ratchet.Expr} {τ : Ty}
    (h : DJudge Γ e τ Γ' κ I κ' I') : SemSafeCtxA κ Γ I e τ κ' Γ' I' :=
  dregistry_context (djudge_certified h)

/-- Every registered rule proves the strengthened escape contract, including checked
method bodies at arbitrary contexts. Untyped block-control escapes are impossible. -/
theorem djudge_escape_only_raise {κ κ' : Ctx} {I I' : Ty} {Γ Γ' : Env}
    {e : Ratchet.Expr} {τ : Ty} (h : DJudge Γ e τ Γ' κ I κ' I')
    {m n : Machine} (hm : StateOk κ Γ I m) {fuel rest : Nat} {j : Jump}
    (hr : runA fuel (evalFrom m e) = .ans (.esc j) n rest) :
    ∃ exc, j = .raiseJ exc ∧ Semantics.isTypeError n.heap exc = false :=
  (((djudge_context h) m hm).2 fuel (.esc j) n rest hr).2.1.only_raise

/-- Every certified evaluation retains existing Proc descriptors, including a receiver
saved before evaluating arguments. Captured frame contents are a separate obligation. -/
theorem djudge_saved_proc {κ κ' : Ctx} {I I' : Ty} {Γ Γ' : Env}
    {e : Ratchet.Expr} {τ : Ty} (h : DJudge Γ e τ Γ' κ I κ' I')
    {m n : Machine} (hm : StateOk κ Γ I m) {fuel rest : Nat} {a : Answer}
    {v : Value} {cl : Closure} (hp : procClosure? m.heap v = some cl)
    (hr : runA fuel (evalFrom m e) = .ans a n rest) :
    procClosure? n.heap v = some cl :=
  (((djudge_context h) m hm).2 fuel a n rest hr).1.procs.payload v cl hp

/-- A saved Proc's dispatch class also survives argument/body evaluation. Retaining
its payload or nominal Proc type alone would not establish this equality. -/
theorem djudge_saved_proc_dispatch {κ κ' : Ctx} {I I' : Ty} {Γ Γ' : Env}
    {e : Ratchet.Expr} {τ : Ty} (h : DJudge Γ e τ Γ' κ I κ' I')
    {m n : Machine} (hm : StateOk κ Γ I m) {fuel rest : Nat} {a : Answer}
    {v : Value} {cl : Closure} (hp : procClosure? m.heap v = some cl)
    (hr : runA fuel (evalFrom m e) = .ans a n rest) :
    classOf n.heap v = classOf m.heap v :=
  (((djudge_context h) m hm).2 fuel a n rest hr).1.procs.dispatch v cl hp

/-- Every certified answer preserves prelude-loading mode, including bodies whose
runtime activation permissions were dropped at captured entry. -/
theorem djudge_phase {κ κ' : Ctx} {I I' : Ty} {Γ Γ' : Env} {e : Ratchet.Expr} {τ : Ty}
    (h : DJudge Γ e τ Γ' κ I κ' I') {m n : Machine} (hm : StateOk κ Γ I m)
    {fuel rest : Nat} {a : Answer} (hr : runA fuel (evalFrom m e) = .ans a n rest) :
    n.preludeMode = m.preludeMode :=
  (((djudge_context h) m hm).2 fuel a n rest hr).1.phase

/-- Certified evaluation retains every old binding and preserves the exact binding
domain of each saved frame, even when captured writes change its values. -/
theorem djudge_bindings {κ κ' : Ctx} {I I' : Ty} {Γ Γ' : Env} {e : Ratchet.Expr} {τ : Ty}
    (h : DJudge Γ e τ Γ' κ I κ' I') {m n : Machine} (hm : StateOk κ Γ I m)
    {fuel rest : Nat} {a : Answer} (hr : runA fuel (evalFrom m e) = .ans a n rest) :
    BindingsPres m n :=
  (((djudge_context h) m hm).2 fuel a n rest hr).1.frames.bindings

/-- Existing lookup owners survive every certified answer within the source fuel
budget, provided the source capture chain is live. -/
theorem djudge_owners {κ κ' : Ctx} {I I' : Ty} {Γ Γ' : Env} {e : Ratchet.Expr} {τ : Ty}
    (h : DJudge Γ e τ Γ' κ I κ' I') {m n : Machine} (hm : StateOk κ Γ I m)
    {fuel rest : Nat} {a : Answer} (hr : runA fuel (evalFrom m e) = .ans a n rest) :
    OwnersPres m n :=
  (((djudge_context h) m hm).2 fuel a n rest hr).1.frames.owners

/-- An initially bound active local protects every saved same-named slot, even when
the active frame captures its caller. Parameter types therefore cannot overwrite caller types. -/
theorem djudge_shadows {κ κ' : Ctx} {I I' : Ty} {Γ Γ' : Env} {e : Ratchet.Expr} {τ : Ty}
    (h : DJudge Γ e τ Γ' κ I κ' I') {m n : Machine} (hm : StateOk κ Γ I m)
    {fuel rest : Nat} {a : Answer} (hr : runA fuel (evalFrom m e) = .ans a n rest) :
    ShadowPres m n :=
  (((djudge_context h) m hm).2 fuel a n rest hr).1.frames.shadows

/-- Every checked value state retains native Proc dispatch while call is unreserved.
A declaration that reserves the selector removes this capability instead of carrying
an assumption about the old method table past a possible write. -/
theorem djudge_proc_call {κ κ' : Ctx} {I I' : Ty} {Γ Γ' : Env} {e : Ratchet.Expr} {τ : Ty}
    (h : DJudge Γ e τ Γ' κ I κ' I') (hf : nameFreeN κ' "call" = true)
    {m n : Machine} (hm : StateOk κ Γ I m) {fuel rest : Nat} {v : Value}
    (hr : runA fuel (evalFrom m e) = .ans (.val v) n rest) : ProcCallReady n.heap :=
  ((((djudge_context h) m hm).2 fuel (.val v) n rest hr).2.2 v rfl).procCall hf

/-- A checker result carries the generic semantic contract, including a method frame. -/
theorem certified_context {κ : Ctx} {I : Ty} {Γ : Env} {e : Ratchet.Expr}
    (c : Certified Γ e κ I) : SemSafeCtxA κ Γ I e c.ty c.ctx c.out c.spine :=
  djudge_context c.judged

theorem certified_safe {κ : Ctx} {I : Ty} {Γ : Env} {e : Ratchet.Expr}
    (c : Certified Γ e κ I) {m : Machine} (hm : StateOk κ Γ I m) : StuckFree m e :=
  (certified_context c).closed hm

/-- An annotation-based body derivation crosses the same registry as whole programs. -/
theorem annotated_add_judgment {κ : Ctx} {I : Ty} (hf : nameFreeN κ "+" = true) :
    DJudge [("x", .int), ("y", .int)]
      (.send (some (.var .lvar "x")) "+" [.var .lvar "y"] none)
      .int [("x", .int), ("y", .int)] κ I :=
  .prim (.var rfl rfl) (.cons (.var rfl rfl) .nil rfl) .intAdd hf (by intro h; cases h)

example {κ : Ctx} {I : Ty} (hf : nameFreeN κ "+" = true) :
    SemSafeCtxA κ [("x", .int), ("y", .int)] I
      (.send (some (.var .lvar "x")) "+" [.var .lvar "y"] none)
      .int κ [("x", .int), ("y", .int)] I := djudge_context (annotated_add_judgment hf)

/-! The enabled-validator safety theorems now live in Bridge.lean. The raw
DJudge completeness helpers in this module require the complete registry. -/

#print axioms djudge_certified
#print axioms djudge_context
#print axioms djudge_escape_only_raise
#print axioms djudge_saved_proc
#print axioms djudge_saved_proc_dispatch
#print axioms djudge_phase
#print axioms djudge_bindings
#print axioms djudge_owners
#print axioms djudge_shadows
#print axioms djudge_proc_call
#print axioms certified_context

end Ratchet.Denote.Typed

namespace Ratchet.Denote.Typed
theorem dmethodFlow_certified {κ : Ctx} {I : Ty} {fr : Frame} {ps : List Ty} {ret τ : Ty}
    {Γ Γ' : Env} {facts out : CallbackFacts} {e : Ratchet.Expr} {callback : Bool}
    (h : DMethodFlow κ I fr ps ret Γ facts e τ callback Γ' out) :
    (DJudgeC dclinks).methodFlow κ I fr ps ret Γ facts e τ callback Γ' out := by
  intro F hF
  certify_djudgments DMethodFlow.rec h F hF
#print axioms dmethodFlow_certified
end Ratchet.Denote.Typed
