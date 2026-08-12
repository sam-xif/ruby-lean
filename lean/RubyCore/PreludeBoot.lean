/-
Two-phase boot (L62): phase 1 runs the **prelude** (`prelude/prelude.rb`, carried
as `Prelude.json`) from H₀ with `preludeMode := true`, so the core-library methods
it defines land in the heap marked `fromPrelude`; phase 2 runs the program under
test on that heap.

The prelude is *model code*, so a prelude that raises, gates, or runs out of fuel
is a build-time bug, not a program-under-test outcome: `bootHeap` reports it as an
error string and `Main` exits 1 (harness error) rather than silently running with
a missing core library.
-/
import RubyCore.Prelude
import RubyCore.Interp

namespace RubyCore
namespace Prelude

/-- Fuel for phase 1. The prelude only installs methods (no loops at load time),
    so this is generous by orders of magnitude; it exists so a mistake in the
    prelude fails fast instead of hanging. -/
def bootFuel : Nat := 200_000

/-- Run phase 1 and return the booted machine (heap + globals). -/
def boot : Except String Machine :=
  match program with
  | .error e => .error s!"prelude decode: {e}"
  | .ok p =>
    match Interp.run bootFuel { Machine.init p with preludeMode := true } with
    | .value _ m => .ok m
    | .uncaught exc m =>
      let cls := className m.heap (classOf m.heap exc)
      .error s!"prelude raised {cls}"
    | .unsupported r _ => .error s!"prelude gated: {r}"
    | .outOfFuel _ => .error "prelude out of fuel"
    | .stuck msg _ => .error s!"prelude stuck: {msg}"

/-- Initial machine for `prog` on the booted (prelude-loaded) heap. The heap
    and globals carry over from phase 1; frames/kont/stdout/`$!` are fresh, and
    `preludeMode` is back to `false` so program `def`s are ordinary. -/
def initWithPrelude (prog : Expr) : Except String Machine :=
  boot.map fun mp =>
    { Machine.initOn mp.heap prog with
      globals := mp.globals }

end Prelude
end RubyCore
