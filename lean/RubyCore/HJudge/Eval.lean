/-
  RubyCore.HJudge.Eval — the simp evaluator (cerberus `app_norm` pattern).

  **Ported from `mdd/sorbet-lean/SorbetLean/Eval.lean`** (spike S2).

  `Interp.invoke` (and so every send) is opaque to whnf — well-founded
  recursion via its `where`-bound dispatch — so raw-`rfl` walking dies at the
  first dispatch, and the Direction-A replays pay `native_decide` in opt-in
  files instead. `native_decide` cannot handle ∀-quantified lemmas (symbolic
  arguments), which are the walk's whole point. So: a registered simp set
  `rb_eval` over the interpreter's definitions — equation lemmas fire where
  whnf cannot, symbolic arguments ride along, and branch points surface as
  residual `if`/`match` on symbolic scrutinees, where the narrowing step
  (`cases`) enters.

  The set is grown by need (a stuck normalization names its missing head).
-/
import RubyCore.HJudge.Walk

set_option autoImplicit false

namespace RubyCore.HJudge

open RubyCore

register_simp_attr rb_eval

end RubyCore.HJudge
