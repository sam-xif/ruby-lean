import Books.TypeSoundness.Rules.Method.BodyYield
import Books.TypeSoundness.Rules.Expr.Send
import Books.TypeSoundness.Rules.Expr.Sequence

/-! A checked captured write followed by fresh method-local insertion and retyping.
The same local name in both frames must retain separate complete environments. -/
set_option autoImplicit false
namespace Checker.Soundness.Typed.MethodBodyControls
open RubyCore Checker Checker.Soundness

private def writeBody : Checker.Expr := .vasgn .lvar "total"
  (.send (some (.var .lvar "total")) "+" [.var .lvar "x"] none)
private def code : ClosureCode := ⟨[.req "x"], [], writeBody, false, rfl⟩
private def localFlow : Checker.Expr :=
  .seq [.vasgn .lvar "total" .nil, .vasgn .lvar "total" (.int 7)]
private def mixedBody : Checker.Expr := .seq [.yield' [.int 1], localFlow]

/-- Every fuel budget is safe, and every value answer retains an Integer caller total
alongside the independently retyped method total. The callback body is proved here. -/
theorem mixed_body {origin m : Machine} {Γ₀ : Env} {cl : Closure}
    {fr : Checker.Frame} {o : ObjId}
    (ho : StateOk ctx0 Γ₀ .ivar0 origin)
    (hn : CallbackCaller ctx0 [("total", .int)] .ivar0 cl [("x", .int)] ["total"]
      [("x", .int), ("total", .int)] m)
    (hm : StateOk (callbackMethodCtx ctx0 fr code) [] .ivar0 m) (hs : CallbackMethodScope m)
    (hblk : m.currentFrame.blk = some (.ref o)) (hproc : (m.heap.get o).payload = .proc cl)
    (hp : cl.params = [.req "x"]) (he : cl.body = toRuby writeBody) (hl : cl.locals = [])
    (fresh : origin.frames.size ≤ m.stack.headD 0)
    (hcaller : Framed origin (popMethodFrame m)) :
    MethodRunSpec m (evalFrom m mixedBody) [("total", .int)] [("total", .int)] .int
      ctx0 (callbackMethodCtx ctx0 fr code) .ivar0 .ivar0 ∧
    RunSpec origin (pushK [.frameK (m.stack.headD 0)] (evalFrom m mixedBody))
      [("total", .int)] .int ctx0 .ivar0 := by
  have hu : RootUncaptured m := by
    rw [RootUncaptured, rootFrame_eq_currentFrame hm.frameInRange.1]
    exact hs.uncaptured
  have hou : RootUncaptured origin := by
    rw [RootUncaptured, rootFrame_eq_currentFrame ho.frameInRange.1]
    exact (ho.runtime rfl).captured
  have hne : m.stack.headD 0 ≠ (popMethodFrame m).stack.headD 0 := by
    rw [hcaller.stack]
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le ho.frameInRange.2 fresh)
  have hfirst := method_yield_int hn hm hs hne hblk hproc hp he rfl rfl
    (by rw [hl]; rfl) rfl rfl (by rw [hl]; rfl)
    (by
      rw [hl]
      exact ((SemSafeCtxA.var rfl rfl).prim (.cons (SemSafeCtxA.var rfl rfl) .nil rfl)
        .intAdd rfl (by intro h; cases h)).vasgn rfl rfl rfl) 1
  have hlocal : SemSafeCtxA (callbackMethodCtx ctx0 fr code) [] .ivar0 localFlow .int
      (callbackMethodCtx ctx0 fr code) [("total", .int)] .ivar0 :=
    (SemSafeCtxA.nilLit.vasgn rfl rfl rfl).seq (SemSafeCtxA.intLit.vasgn rfl rfl rfl)
  have hrun := hfirst.seq (fun n v hres =>
    hlocal.methodOrdinary ho (hres.2.2 v rfl).1 (hres.2.2 v rfl).2
      (hres.1.uncaptured hm.frameInRange hu) rfl rfl (by rw [hres.1.stack]; exact fresh)
      (hres.1.project ho.frameInRange hou hm.frameInRange hu fresh hcaller))
  exact ⟨hrun, hrun.methodReturn ho.frameInRange hou hm.frameInRange hu fresh hcaller rfl _⟩

#print axioms mixed_body
end Checker.Soundness.Typed.MethodBodyControls
