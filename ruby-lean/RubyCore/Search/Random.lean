/-
**Phase 1 of the Direction-A witness finder: random (property-based) search for
type errors.** Realizes the first de-risking step of
`type-safety-by-reachability.md` §8 — "`Plausible` witness demo (Direction A,
shallow) over the current fuel interpreter … pure win, no new theory."

The claim being demonstrated: we can *find counterexamples that refute
`typeSafe?`* by running the semantics on generated inputs, and every witness
found is turned into a **certified** disproof of type safety by the axiom-clean
bridge `Proof.runTypeStuck_unsafe` (`RunCert.lean`).

ARCHITECTURE (why the search is allowed to be dumb)
  search (UNTRUSTED, random)  →  witness input n
     ↓ replay through the trusted `stepFn`/`run` (`native_decide`)
  `typeStuckAt prog fuel n = true`
     ↓ `Proof.runTypeStuck_unsafe` (axiom-clean)
  `∃ r, ReachableResult (Machine.init (prog n)) r ∧ typeStuck r`
So a *false* witness cannot survive (replay kills it) and the search needs no
soundness argument at all — "the certificate is the trace"
(`type-safety-by-reachability.md` §3).

WHAT THIS IS NOT: random search is **undirected**. It finds *shallow* witnesses
(bugs a random input is likely to hit) and provably will not find a needle behind
a narrow guard — demonstrated below by `narrowNeedle`, which is exactly the gap
the Phase-2 concolic engine (concrete run + path condition + solver-flip) closes.
A `success` verdict here is therefore **NOT** a type-safety proof; it is "no
witness found within these bounds" (the `VERIFIED(k)`/UNKNOWN distinction of
`bounded-effect-checking.md` §3). Proving safety is Direction B
(`Proof/T5Loop.lean`, `Proof/DispatchLoop.lean`).

INPUT MODEL: the "input" is an `Int` substituted into the program (the standard
property-based-testing shape). Symbolizing real program inputs (argv/stdin/env)
is future work and orthogonal — see `bounded-effect-checking.md` §2.

Off the default build target (like `RubyCore/Proof/`): `Plausible` is a dev-only
dependency and neither the `RubyCore` lib root nor the `rubycore` exe imports
this file (implementation-notes L58). Build/run:
    lake build RubyCore.Search.Random
-/
import Plausible
import RubyCore.Proof.RunCert

namespace RubyCore
namespace Search

open Interp Proof Plausible

/-! ## 1. The property under test -/

/-- Bad-state test at one concrete input: does the program, with `n` substituted,
    run to an uncaught *type-family* exception (`NoMethodError`/`ArgumentError`/
    `TypeError`)? This is the decidable mirror of `typeStuck`. -/
def typeStuckAt (prog : Int → Expr) (fuel : Nat) (n : Int) : Bool :=
  runTypeStuck (run fuel (Machine.init (prog n)))

/-- `typeSafe?` at one input — the property the search tries to **refute**. -/
def typeSafeAt (prog : Int → Expr) (fuel : Nat) (n : Int) : Bool :=
  !typeStuckAt prog fuel n

/-- Diagnostic classification of one run. Keeps the **frontier** visible: an
    `unsupported`/`outOfFuel` outcome is "we could not say", NOT evidence of
    safety (`bounded-effect-checking.md` §3; `type-safety-by-reachability.md` §2). -/
def outcomeAt (prog : Int → Expr) (fuel : Nat) (n : Int) : String :=
  match run fuel (Machine.init (prog n)) with
  | .value _ _ => "value (safe on this input)"
  | .uncaught exc m =>
    let cls := className m.heap (realClassOf m.heap exc)
    if isTypeErrorB m.heap exc then s!"TYPE-STUCK: uncaught {cls}"
    else s!"uncaught {cls} (not a type error)"
  | .unsupported r _ => s!"FRONTIER: unsupported ({r})"
  | .outOfFuel _ => "FRONTIER: out of fuel"
  | .stuck msg _ => s!"MODEL BUG: stuck ({msg})"

/-! ## 2. Program families (T2-style, `type-safety-by-reachability.md` §9.1)

    Each is an `Int → Expr`: a program with the input substituted. -/

/-- **T2 `nil_dispatch`** — the canonical reachable type error. A helper returns
    `Integer` or `nil` depending on the input; the caller sends `succ`
    unconditionally, so the `nil` path raises `NoMethodError`:

        def f(x); if x < 5 then 1 else nil end; end
        f(N).succ

    Witness set is broad (`N ≥ 5`), so random search finds it immediately.
    [V] CRuby agrees: `undefined method 'succ' for nil (NoMethodError)`. -/
def nilDispatch (n : Int) : Expr :=
  .seq [ .def' "f" [.req "x"]
           (.if' (.send (some (.var .lvar "x")) "<" [.int 5] .none) (.int 1) (some .nil)),
         .send (some (.send .none "f" [.int n] .none)) "succ" [] .none ]

/-- **Control: no witness exists.** `N.succ` is fine for every `Integer`. The
    search must report no counterexample — a false positive here would be a bug
    in the harness ("zero false positives by construction", §1). -/
def alwaysSafe (n : Int) : Expr := .send (some (.int n)) "succ" [] .none

/-- **The needle: a witness random search cannot find.** Only `N = 123456789`
    is type-stuck; every other input is safe:

        if N == 123456789 then nil.succ else 0 end

    Random sampling has vanishing probability of hitting it. This is the honest
    limitation of Phase 1 and the motivation for Phase 2 (a concolic engine solves
    `pathCondition ∧ n = 123456789` and produces the input directly). -/
def narrowNeedle (n : Int) : Expr :=
  .if' (.send (some (.int n)) "==" [.int 123456789] .none)
       (.send (some .nil) "succ" [] .none)
       (some (.int 0))

/-! ## 3. The search driver -/

/-- Run a random witness search for `prog`, printing the verdict. Seeded for
    reproducibility. `failed [n := …]` is a **found witness**; `success` means
    "no witness within these bounds" (NOT a safety proof, see the header). -/
def search (name : String) (prog : Int → Expr) (fuel : Nat)
    (cfg : Configuration := { randomSeed := some 42 }) : IO Unit := do
  let r ← Testable.checkIO
    (NamedBinder "n" (∀ n : Int, typeSafeAt prog fuel n = true)) cfg
  IO.println s!"  [{name}] {r}"

/-! ### Results (run at elaboration; informational, never fails the build)

    Actual output at seed 42 (the witness set for `nilDispatch` is every `n ≥ 5`,
    so the particular value depends on the seed):
      [nilDispatch      ] failed [n := 7, …]  ← WITNESS FOUND, refutes typeSafe?
      [alwaysSafe       ] success             ← no false positive
      [narrowNeedle     ] success             ← MISSED (needs Phase-2 concolic)
      [narrowNeedle(20x)] success             ← still missed at 20x budget -/

def runSearches : IO Unit := do
  IO.println "── Phase-1 random witness search (Direction A) ──"
  search "nilDispatch " nilDispatch 3000
  search "alwaysSafe  " alwaysSafe 3000
  search "narrowNeedle" narrowNeedle 3000
  -- even with a 20x budget the needle is not found: undirected search's limit
  search "narrowNeedle(20x)" narrowNeedle 3000
    { randomSeed := some 42, numInst := 2000, maxSize := 10000 }

#eval runSearches

/- The outcome at the needle's witness, for the record (the input the search
   could not guess but Phase 2 will solve for). -/
#eval outcomeAt narrowNeedle 3000 123456789

/-! ## 4. Certifying a found witness (search untrusted → trusted verdict)

    The search *reported* `n := 7` (seed 42). We now replay that input through
    the trusted interpreter and apply the axiom-clean bridge, yielding a real
    theorem that `nilDispatch 7` is not type-safe. A bogus witness could not
    survive this step — which is precisely why the search needs no soundness
    argument. -/

/-- Replay of the reported witness (`native_decide`: running the interpreter is
    not kernel-reducible — L55/L57 — so the trace is checked by execution, the
    Direction-A trust position). -/
theorem nilDispatch_witness_typeStuck : typeStuckAt nilDispatch 3000 7 = true := by
  native_decide

/-- **Certified counterexample.** `nilDispatch 7` (i.e. `f(7).succ` where `f`
    returns `nil` for `7`) reaches a type-stuck outcome: the program is NOT
    type-safe, and the run is the witness. Refutes `typeSafe?` for this program. -/
theorem nilDispatch_unsafe :
    ∃ r, ReachableResult (Machine.init (nilDispatch 7)) r ∧ typeStuck r :=
  runTypeStuck_unsafe nilDispatch_witness_typeStuck

/-- The needle, certified once its witness is known (Phase 2 will *derive* the
    input `123456789` instead of it being supplied by hand). -/
theorem narrowNeedle_witness_typeStuck :
    typeStuckAt narrowNeedle 3000 123456789 = true := by native_decide

theorem narrowNeedle_unsafe :
    ∃ r, ReachableResult (Machine.init (narrowNeedle 123456789)) r ∧ typeStuck r :=
  runTypeStuck_unsafe narrowNeedle_witness_typeStuck

end Search
end RubyCore
