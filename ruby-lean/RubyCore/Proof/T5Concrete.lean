/-
Concrete T5 (`class_hierarchy`) type-safety verdicts, by EXECUTION (Direction A
of `type-safety-by-reachability.md` §3). Companion to the readable sources in
`type-safety-demos/t5_safe.rb` / `t5_buggy.rb`.

Both are terminating, so the run itself is the certificate:
- SAFE: the run reaches a value ⇒ no reachable type-stuck outcome (prove).
- BUGGY: the run reaches an uncaught `NoMethodError` (a type-family exception,
  `Rock#speak` is undefined) ⇒ a type-stuck outcome is reachable; the run is the
  counterexample (disprove).

⚠ TRUST NOTE — NOT axiom-clean (isolated here, like `QLearningTypeSafe`). The
run is evaluated by `native_decide` (the boot heap uses `Array.qsort` and is not
kernel-reducible), adding one `ofReduceBool` axiom per verdict. The bridges
`runsToValueB_type_safe` / `runsToTypeErrorB_unsafe` (`RunCert.lean`) are
axiom-clean; only the boolean run-checks carry the compiler.

The Direction-B (invariant) proof of the *unbounded* T5 loop — which does not
run the program — is separate; its object-model core is `T5.dispatch_progress`.

The JSON literals are `bin/export-json` output for the two demo sources.
-/
import RubyCore.Proof.RunCert

namespace RubyCore
namespace Proof
namespace T5Concrete

/-- Desugared RubyCore AST of `type-safety-demos/t5_safe.rb`. -/
def safeJson : String :=
"{\"v\":4,\"ast\":[\"seq\",[\"class\",\"Animal\",null,[\"def\",\"speak\",[],[\"str\",\"...\"]]],[\"class\",\"Dog\",[\"const\",\"Animal\"],[\"def\",\"speak\",[],[\"str\",\"woof\"]]],[\"class\",\"Cat\",[\"const\",\"Animal\"],[\"def\",\"speak\",[],[\"str\",\"meow\"]]],[\"vasgn\",\"local\",\"animals\",[\"array\",[[\"send\",[\"const\",\"Dog\"],\"new\",[],null],[\"send\",[\"const\",\"Cat\"],\"new\",[],null],[\"send\",[\"const\",\"Animal\"],\"new\",[],null]]]],[\"vasgn\",\"local\",\"i\",[\"int\",0]],[\"while\",[\"send\",[\"var\",\"local\",\"i\"],\"<\",[[\"send\",[\"var\",\"local\",\"animals\"],\"length\",[],null]],null],[\"seq\",[\"send\",null,\"puts\",[[\"send\",[\"send\",[\"var\",\"local\",\"animals\"],\"[]\",[[\"var\",\"local\",\"i\"]],null],\"speak\",[],null]],null],[\"vasgn\",\"local\",\"i\",[\"send\",[\"var\",\"local\",\"i\"],\"+\",[[\"int\",1]],null]]]]]}\n"
/-- Desugared RubyCore AST of `type-safety-demos/t5_buggy.rb`. -/
def buggyJson : String :=
"{\"v\":4,\"ast\":[\"seq\",[\"class\",\"Dog\",null,[\"def\",\"speak\",[],[\"str\",\"woof\"]]],[\"class\",\"Rock\",null,[\"nil\"]],[\"vasgn\",\"local\",\"things\",[\"array\",[[\"send\",[\"const\",\"Dog\"],\"new\",[],null],[\"send\",[\"const\",\"Rock\"],\"new\",[],null]]]],[\"vasgn\",\"local\",\"i\",[\"int\",0]],[\"while\",[\"send\",[\"var\",\"local\",\"i\"],\"<\",[[\"send\",[\"var\",\"local\",\"things\"],\"length\",[],null]],null],[\"seq\",[\"send\",null,\"puts\",[[\"send\",[\"send\",[\"var\",\"local\",\"things\"],\"[]\",[[\"var\",\"local\",\"i\"]],null],\"speak\",[],null]],null],[\"vasgn\",\"local\",\"i\",[\"send\",[\"var\",\"local\",\"i\"],\"+\",[[\"int\",1]],null]]]]]}\n"
/-- **T5 safe is type-safe.** The run reaches a value; no reachable outcome is a
    type-family `uncaught`. -/
theorem t5_safe_runs_to_value : runsToValueB safeJson 100000 = true := by native_decide

theorem t5_safe_type_safe :
    ∃ e : Expr, ∃ r, ReachableResult (Machine.init e) r ∧ ¬ typeStuck r :=
  runsToValueB_type_safe t5_safe_runs_to_value

/-- **T5 buggy is NOT type-safe.** The run reaches an uncaught `NoMethodError`
    (`Rock#speak` undefined) — a reachable type-stuck outcome. The run trace is
    the counterexample. -/
theorem t5_buggy_hits_type_error : runsToTypeErrorB buggyJson 100000 = true := by native_decide

theorem t5_buggy_unsafe :
    ∃ e : Expr, ∃ r, ReachableResult (Machine.init e) r ∧ typeStuck r :=
  runsToTypeErrorB_unsafe t5_buggy_hits_type_error

end T5Concrete
end Proof
end RubyCore
