/-
Concrete type-safety of the `q_learning_extended` demo, by EXECUTION
(Direction A of `AGENTS.md` §Type safety as reachability §3).

This file leverages `run_value_type_safe`: a run that terminates in a value
reaches a non-type-stuck outcome.  We discharge its hypothesis
`run fuel (Machine.init e) = .value v m` for the *actual* linked q_learning
program by running the interpreter inside the proof.

⚠ TRUST NOTE — this file is DELIBERATELY NOT axiom-clean.  `run` is iterated
`stepFn`, whose dispatch bottoms out in `invoke` — now a *well-founded* `def`
(L52), so it is symbolically reasoning-amenable (that is what unblocks the
Direction-B/T5 proofs).  But well-founded recursion compiles to `Acc.rec`, which
the kernel's whnf does NOT reduce, so `rfl`/`decide` still cannot *evaluate* a
concrete dispatching run (verified: the `rfl` still fails).  The only way to
evaluate a dispatching run *inside a proof* is `native_decide`, which compiles
and runs the interpreter and adds `Lean.ofReduceBool` (+ the compiler) to the
trust base — the `..._native.native_decide.ax_N` axiom below.  That is exactly
the Direction-A trust position: "the certificate is the execution."  It is kept
in its own file, OUT of the `RubyCore.Proof.TypeSafety`/`Demo` axiom-clean core,
so the metatheory (`invariant_sound`, adequacy, …) stays audited to
`propext`/`Classical.choice`/`Quot.sound` only.  The axiom-clean alternative is
to de-`partial` the dispatch helpers (fuel-structural `def`s) so the kernel can
reduce `run`, then `decide` — a model refactor, not done here.

The JSON literal is the desugared+linked RubyCore AST emitted by
`typecheck-pipeline/bin/link` (byte-identical to what `bin/demo-qlearning
--extended` feeds the `rubycore` binary).
-/
import RubyCore.Proof.TypeSafety

namespace RubyCore
namespace Proof
namespace QLearning

open Interp Lean

/-- The linked q_learning_extended program (desugared RubyCore AST, export v4). -/
def json : String :=
"{\"v\":4,\"ast\":[\"seq\",[\"module\",\"Ai4r\",[\"module\",\"Data\",[\"module\",\"Parameterizable\",[\"seq\",[\"module\",\"ClassMethods\",[\"seq\",[\"def\",\"get_parameters_info\",[],[\"seq\",[\"vasgn\",\"local\",\"__dt_t1\",[\"var\",\"ivar\",\"@_params_info_\"]],[\"if\",[\"var\",\"local\",\"__dt_t1\"],[\"var\",\"local\",\"__dt_t1\"],[\"hash\",[]]]]],[\"def\",\"parameters_info\",[[\"preq\",\"params_info\"]],[\"seq\",[\"vasgn\",\"ivar\",\"@_params_info_\",[\"send\",[\"send\",null,\"get_parameters_info\",[],null],\"merge\",[[\"var\",\"local\",\"params_info\"]],null]],[\"send\",[\"var\",\"local\",\"params_info\"],\"each_key\",[],[\"block\",[[\"preq\",\"param\"]],[],[\"if\",[\"send\",[\"seq\",[\"vasgn\",\"local\",\"__dt_t3\",[\"send\",null,\"method_defined?\",[[\"var\",\"local\",\"param\"]],null]],[\"if\",[\"var\",\"local\",\"__dt_t3\"],[\"var\",\"local\",\"__dt_t3\"],[\"send\",null,\"method_defined?\",[[\"send\",[\"seq\",[\"vasgn\",\"local\",\"__dt_t2\",[\"var\",\"local\",\"param\"]],[\"if\",[\"send\",[\"const\",\"String\"],\"===\",[[\"var\",\"local\",\"__dt_t2\"]],null],[\"var\",\"local\",\"__dt_t2\"],[\"send\",[\"var\",\"local\",\"__dt_t2\"],\"to_s\",[],null]]],\"+\",[[\"str\",\"=\"]],null]],null]]],\"!\",[],null],[\"send\",null,\"attr_accessor\",[[\"var\",\"local\",\"param\"]],null],null]]]]]]],[\"def\",\"set_parameters\",[[\"preq\",\"params\"]],[\"seq\",[\"send\",[\"var\",\"local\",\"params\"],\"each\",[],[\"block\",[[\"preq\",\"key\"],[\"preq\",\"val\"]],[],[\"if\",[\"send\",null,\"respond_to?\",[[\"send\",[\"seq\",[\"vasgn\",\"local\",\"__dt_t4\",[\"var\",\"local\",\"key\"]],[\"if\",[\"send\",[\"const\",\"String\"],\"===\",[[\"var\",\"local\",\"__dt_t4\"]],null],[\"var\",\"local\",\"__dt_t4\"],[\"send\",[\"var\",\"local\",\"__dt_t4\"],\"to_s\",[],null]]],\"+\",[[\"str\",\"=\"]],null]],null],[\"send\",null,\"public_send\",[[\"send\",[\"seq\",[\"vasgn\",\"local\",\"__dt_t5\",[\"var\",\"local\",\"key\"]],[\"if\",[\"send\",[\"const\",\"String\"],\"===\",[[\"var\",\"local\",\"__dt_t5\"]],null],[\"var\",\"local\",\"__dt_t5\"],[\"send\",[\"var\",\"local\",\"__dt_t5\"],\"to_s\",[],null]]],\"+\",[[\"str\",\"=\"]],null],[\"var\",\"local\",\"val\"]],null],null]]],[\"self\"]]],[\"def\",\"get_parameters\",[],[\"seq\",[\"vasgn\",\"local\",\"params\",[\"hash\",[]]],[\"send\",[\"send\",[\"send\",[\"self\"],\"class\",[],null],\"get_parameters_info\",[],null],\"each_key\",[],[\"block\",[[\"preq\",\"key\"]],[],[\"if\",[\"send\",null,\"respond_to?\",[[\"var\",\"local\",\"key\"]],null],[\"seq\",[\"send\",[\"var\",\"local\",\"params\"],\"[]=\",[[\"var\",\"local\",\"key\"],[\"vasgn\",\"local\",\"__dt_t6\",[\"send\",null,\"send\",[[\"var\",\"local\",\"key\"]],null]]],null],[\"var\",\"local\",\"__dt_t6\"]],null]]],[\"var\",\"local\",\"params\"]]],[\"defs\",[\"self\"],\"included\",[[\"preq\",\"base\"]],[\"send\",[\"var\",\"local\",\"base\"],\"extend\",[[\"const\",\"ClassMethods\"]],null]]]]]],[\"module\",\"Ai4r\",[\"module\",\"Reinforcement\",[\"class\",\"QLearning\",null,[\"seq\",[\"send\",null,\"include\",[[\"cpath\",[\"cpath\",[\"const\",\"Ai4r\"],\"Data\"],\"Parameterizable\"]],null],[\"send\",null,\"parameters_info\",[[\"kwargs\",[[[\"sym\",\"learning_rate\"],[\"str\",\"Update step size\"]],[[\"sym\",\"discount\"],[\"str\",\"Discount factor\"]],[[\"sym\",\"exploration\"],[\"str\",\"Exploration rate\"]]]]],null],[\"def\",\"initialize\",[],[\"seq\",[\"vasgn\",\"ivar\",\"@learning_rate\",[\"flt\",0.1]],[\"vasgn\",\"ivar\",\"@discount\",[\"flt\",0.9]],[\"vasgn\",\"ivar\",\"@exploration\",[\"flt\",0.1]],[\"vasgn\",\"ivar\",\"@q\",[\"send\",[\"const\",\"Hash\"],\"new\",[],[\"block\",[[\"preq\",\"h\"],[\"preq\",\"k\"]],[],[\"seq\",[\"send\",[\"var\",\"local\",\"h\"],\"[]=\",[[\"var\",\"local\",\"k\"],[\"vasgn\",\"local\",\"__dt_t1\",[\"send\",[\"const\",\"Hash\"],\"new\",[[\"flt\",0.0]],null]]],null],[\"var\",\"local\",\"__dt_t1\"]]]]]]],[\"def\",\"update\",[[\"preq\",\"state\"],[\"preq\",\"action\"],[\"preq\",\"reward\"],[\"preq\",\"next_state\"]],[\"seq\",[\"vasgn\",\"local\",\"best_next\",[\"seq\",[\"vasgn\",\"local\",\"__dt_t2\",[\"send\",[\"send\",[\"send\",[\"var\",\"ivar\",\"@q\"],\"[]\",[[\"var\",\"local\",\"next_state\"]],null],\"values\",[],null],\"max\",[],null]],[\"if\",[\"var\",\"local\",\"__dt_t2\"],[\"var\",\"local\",\"__dt_t2\"],[\"flt\",0.0]]]],[\"seq\",[\"vasgn\",\"local\",\"__dt_t3\",[\"send\",[\"var\",\"ivar\",\"@q\"],\"[]\",[[\"var\",\"local\",\"state\"]],null]],[\"vasgn\",\"local\",\"__dt_t4\",[\"var\",\"local\",\"action\"]],[\"vasgn\",\"local\",\"__dt_t5\",[\"send\",[\"send\",[\"var\",\"local\",\"__dt_t3\"],\"[]\",[[\"var\",\"local\",\"__dt_t4\"]],null],\"+\",[[\"send\",[\"var\",\"ivar\",\"@learning_rate\"],\"*\",[[\"send\",[\"send\",[\"var\",\"local\",\"reward\"],\"+\",[[\"send\",[\"var\",\"ivar\",\"@discount\"],\"*\",[[\"var\",\"local\",\"best_next\"]],null]],null],\"-\",[[\"send\",[\"send\",[\"var\",\"ivar\",\"@q\"],\"[]\",[[\"var\",\"local\",\"state\"]],null],\"[]\",[[\"var\",\"local\",\"action\"]],null]],null]],null]],null]],[\"send\",[\"var\",\"local\",\"__dt_t3\"],\"[]=\",[[\"var\",\"local\",\"__dt_t4\"],[\"var\",\"local\",\"__dt_t5\"]],null],[\"var\",\"local\",\"__dt_t5\"]]]],[\"def\",\"choose_action\",[[\"preq\",\"state\"]],[\"seq\",[\"if\",[\"send\",[\"send\",[\"var\",\"ivar\",\"@q\"],\"[]\",[[\"var\",\"local\",\"state\"]],null],\"empty?\",[],null],[\"return\",[\"nil\"]],null],[\"if\",[\"send\",[\"send\",null,\"rand\",[],null],\"<\",[[\"var\",\"ivar\",\"@exploration\"]],null],[\"send\",[\"send\",[\"send\",[\"var\",\"ivar\",\"@q\"],\"[]\",[[\"var\",\"local\",\"state\"]],null],\"keys\",[],null],\"sample\",[],null],[\"send\",[\"send\",[\"send\",[\"var\",\"ivar\",\"@q\"],\"[]\",[[\"var\",\"local\",\"state\"]],null],\"max_by\",[],[\"block\",[[\"preq\",\"_\"],[\"preq\",\"v\"]],[],[\"var\",\"local\",\"v\"]]],\"first\",[],null]]]],[\"send\",null,\"attr_reader\",[[\"sym\",\"q\"]],null]]]]],[\"vasgn\",\"local\",\"agent\",[\"send\",[\"cpath\",[\"cpath\",[\"const\",\"Ai4r\"],\"Reinforcement\"],\"QLearning\"],\"new\",[],null]],[\"send\",[\"var\",\"local\",\"agent\"],\"set_parameters\",[[\"kwargs\",[[[\"sym\",\"learning_rate\"],[\"flt\",0.5]],[[\"sym\",\"discount\"],[\"flt\",0.9]],[[\"sym\",\"exploration\"],[\"flt\",0.0]]]]],null],[\"vasgn\",\"local\",\"transitions\",[\"array\",[[\"array\",[[\"sym\",\"s1\"],[\"sym\",\"right\"],[\"int\",0],[\"sym\",\"s2\"]]],[\"array\",[[\"sym\",\"s2\"],[\"sym\",\"right\"],[\"int\",1],[\"sym\",\"s3\"]]],[\"array\",[[\"sym\",\"s1\"],[\"sym\",\"left\"],[\"int\",0],[\"sym\",\"s1\"]]],[\"array\",[[\"sym\",\"s2\"],[\"sym\",\"left\"],[\"int\",0],[\"sym\",\"s1\"]]]]]],[\"vasgn\",\"local\",\"states\",[\"array\",[[\"sym\",\"s1\"],[\"sym\",\"s2\"]]]],[\"vasgn\",\"local\",\"actions\",[\"array\",[[\"sym\",\"left\"],[\"sym\",\"right\"]]]],[\"send\",[\"int\",5],\"times\",[],[\"block\",[[\"preq\",\"i\"]],[],[\"seq\",[\"send\",[\"var\",\"local\",\"transitions\"],\"each\",[],[\"block\",[[\"preq\",\"t\"]],[],[\"send\",[\"var\",\"local\",\"agent\"],\"update\",[[\"send\",[\"var\",\"local\",\"t\"],\"[]\",[[\"int\",0]],null],[\"send\",[\"var\",\"local\",\"t\"],\"[]\",[[\"int\",1]],null],[\"send\",[\"var\",\"local\",\"t\"],\"[]\",[[\"int\",2]],null],[\"send\",[\"var\",\"local\",\"t\"],\"[]\",[[\"int\",3]],null]],null]]],[\"send\",null,\"puts\",[[\"send\",[\"send\",[\"str\",\"after sweep \"],\"+\",[[\"seq\",[\"vasgn\",\"local\",\"__dt_t1\",[\"send\",[\"var\",\"local\",\"i\"],\"+\",[[\"int\",1]],null]],[\"if\",[\"send\",[\"const\",\"String\"],\"===\",[[\"var\",\"local\",\"__dt_t1\"]],null],[\"var\",\"local\",\"__dt_t1\"],[\"send\",[\"var\",\"local\",\"__dt_t1\"],\"to_s\",[],null]]]],null],\"+\",[[\"str\",\":\"]],null]],null],[\"send\",[\"var\",\"local\",\"states\"],\"each\",[],[\"block\",[[\"preq\",\"s\"]],[],[\"seq\",[\"vasgn\",\"local\",\"cells\",[\"send\",[\"var\",\"local\",\"actions\"],\"map\",[],[\"block\",[[\"preq\",\"a\"]],[],[\"send\",[\"send\",[\"seq\",[\"vasgn\",\"local\",\"__dt_t2\",[\"var\",\"local\",\"a\"]],[\"if\",[\"send\",[\"const\",\"String\"],\"===\",[[\"var\",\"local\",\"__dt_t2\"]],null],[\"var\",\"local\",\"__dt_t2\"],[\"send\",[\"var\",\"local\",\"__dt_t2\"],\"to_s\",[],null]]],\"+\",[[\"str\",\"=\"]],null],\"+\",[[\"seq\",[\"vasgn\",\"local\",\"__dt_t3\",[\"send\",[\"send\",[\"send\",[\"var\",\"local\",\"agent\"],\"q\",[],null],\"[]\",[[\"var\",\"local\",\"s\"]],null],\"[]\",[[\"var\",\"local\",\"a\"]],null]],[\"if\",[\"send\",[\"const\",\"String\"],\"===\",[[\"var\",\"local\",\"__dt_t3\"]],null],[\"var\",\"local\",\"__dt_t3\"],[\"send\",[\"var\",\"local\",\"__dt_t3\"],\"to_s\",[],null]]]],null]]]],[\"send\",null,\"puts\",[[\"send\",[\"send\",[\"send\",[\"send\",[\"send\",[\"str\",\"  \"],\"+\",[[\"seq\",[\"vasgn\",\"local\",\"__dt_t4\",[\"var\",\"local\",\"s\"]],[\"if\",[\"send\",[\"const\",\"String\"],\"===\",[[\"var\",\"local\",\"__dt_t4\"]],null],[\"var\",\"local\",\"__dt_t4\"],[\"send\",[\"var\",\"local\",\"__dt_t4\"],\"to_s\",[],null]]]],null],\"+\",[[\"str\",\": \"]],null],\"+\",[[\"seq\",[\"vasgn\",\"local\",\"__dt_t5\",[\"send\",[\"var\",\"local\",\"cells\"],\"join\",[[\"str\",\", \"]],null]],[\"if\",[\"send\",[\"const\",\"String\"],\"===\",[[\"var\",\"local\",\"__dt_t5\"]],null],[\"var\",\"local\",\"__dt_t5\"],[\"send\",[\"var\",\"local\",\"__dt_t5\"],\"to_s\",[],null]]]],null],\"+\",[[\"str\",\"  -> best \"]],null],\"+\",[[\"seq\",[\"vasgn\",\"local\",\"__dt_t6\",[\"send\",[\"var\",\"local\",\"agent\"],\"choose_action\",[[\"var\",\"local\",\"s\"]],null]],[\"if\",[\"send\",[\"const\",\"String\"],\"===\",[[\"var\",\"local\",\"__dt_t6\"]],null],[\"var\",\"local\",\"__dt_t6\"],[\"send\",[\"var\",\"local\",\"__dt_t6\"],\"to_s\",[],null]]]],null]],null]]]]]]]]}"

/-- Parse + decode + run to a value, as one decidable boolean. -/
def runsToValue (js : String) (fuel : Nat) : Bool :=
  match Json.parse js with
  | .error _ => false
  | .ok j => match Decode.program j with
    | .error _ => false
    | .ok e => match run fuel (Machine.init e) with
      | .value _ _ => true
      | _ => false

/-- If `runsToValue` holds, the decoded program runs to a value, so by
    `run_value_type_safe` its execution reaches a non-type-stuck outcome. -/
theorem runsToValue_type_safe {js : String} {fuel : Nat}
    (h : runsToValue js fuel = true) :
    ∃ e : Expr, ∃ r, ReachableResult (Machine.init e) r ∧ ¬ typeStuck r := by
  unfold runsToValue at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i e _
      split at h
      · rename_i v m hrun
        exact ⟨e, run_value_type_safe hrun⟩
      · simp at h

/-- **q_learning_extended is type-safe** (for its concrete, deterministic run):
    the interpreter runs the linked program to a value, so no reachable outcome
    is a type-family `uncaught`.  Witnessed by execution (`native_decide`); see
    the trust note atop this file. -/
theorem qlearning_runs_to_value : runsToValue json 200000 = true := by native_decide

theorem qlearning_type_safe :
    ∃ e : Expr, ∃ r, ReachableResult (Machine.init e) r ∧ ¬ typeStuck r :=
  runsToValue_type_safe qlearning_runs_to_value

end QLearning
end Proof
end RubyCore
