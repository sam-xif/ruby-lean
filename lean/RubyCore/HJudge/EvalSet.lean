/-
  RubyCore.HJudge.EvalSet — the `rb_eval` simp-set membership (grown by need;
  see Eval.lean for the design note). Separate file because a registered
  simp attribute only becomes usable in importing files.

  **Ported from `mdd/sorbet-lean/SorbetLean/EvalSet.lean`** (spike S2),
  membership verbatim.
-/
import RubyCore.HJudge.Eval

namespace RubyCore.HJudge

open RubyCore

attribute [rb_eval]
  -- the step function and its dispatchers
  Interp.stepFn Interp.evalExpr Interp.applyKont Interp.unwind
  -- send path
  Interp.invoke Interp.startArgs Interp.finishSend Interp.startKwargs
  Interp.continueArray Interp.doYield Interp.startYield
  -- machine plumbing
  Interp.withCtl Interp.withKont Interp.raiseErr
  Machine.currentFrame Machine.setCurrentFrame Machine.getLocal Machine.setLocal
  Machine.init Machine.initOn
  -- our split wrappers
  MCfg.load Machine.cfg
  -- dispatch resolution + heap layer (grown by need)
  Interp.invoke.invokeDispatch Interp.enterUserMethod Interp.dispatchMiss
  Interp.visError? Interp.crubyShadow Interp.crubySingletonShadow
  Interp.lookupAbove Interp.methodOn
  lookup defineMethod Heap.get Heap.set Heap.alloc Heap.classPayload?
  ancestors classOf
  -- builtins layer + list plumbing (grown by need)
  Builtins.run List.foldl
  Builtins.allocStr Builtins.allocArr Builtins.allocHsh Builtins.allocExc

end RubyCore.HJudge
