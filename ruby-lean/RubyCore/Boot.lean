/-
Booting the core library.

Much of Ruby's core library is written in Ruby here too: `prelude/prelude.rb`
defines `Enumerable`, `Comparable` and many other methods. Boot has two
phases. The first runs the prelude (the term `Prelude.program`) on the initial
heap with `preludeMode := true`, so that the methods it defines are marked as
the model's own. The second runs the user's program on the heap that leaves.

A prelude that raises, is declined or runs out of fuel is a bug in the model,
not an outcome of the user's program: it is reported as an error and `rubycore`
exits with status 1.
-/
import RubyCore.Generated.Prelude
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
    -- main's native singleton macros have their own place in lookup; they are
    -- not instance methods on every Object.
    let (e, initial) := Interp.eigenclassOf { Machine.init p with preludeMode := true } Boot.mainId
    let h := crubyMainSingletonNames.foldl (fun h name =>
      let repr := name == "inspect" || name == "to_s"
      defineMethod h e name
        { params := [], body := .nil, owner := e,
          visibility := if repr then .pub else .priv,
          builtin := some ((if repr then "Object#" else "Main#") ++ name) }) initial.heap
    let initial := { initial with heap := h }
    let (exceptionEigen, initial) := Interp.eigenclassOf initial Boot.exceptionId
    let h := defineMethod initial.heap exceptionEigen "exception"
      { params := [], body := .nil, owner := exceptionEigen, builtin := some "Exception.exception" }
    let initial := { initial with heap := h }
    -- Boot classes also inherit Exception's singleton constructor before any
    -- Ruby class body has had a chance to realize their eigenclass chains.
    let initial := Boot.classTable.foldl (fun m entry =>
      if (ancestors m.heap entry.1).contains Boot.exceptionId then
        (Interp.eigenclassOf m entry.1).2 else m) initial
    match Interp.run bootFuel initial with
    | .value _ m => .ok m
    | .uncaught exc m =>
      let cls := className m.heap (realClassOf m.heap exc)
      .error s!"prelude raised {cls}"
    | .unsupported r _ => .error s!"prelude gated: {r}"
    | .outOfFuel _ => .error "prelude out of fuel"
    | .stuck msg _ => .error s!"prelude stuck: {msg}"

/-- Initial machine for `prog` on the booted (prelude-loaded) heap. The heap
    and globals carry over from phase 1; frames/kont/stdout/`$!` are fresh, and
    `preludeMode` is back to `false` so program `def`s are ordinary. -/
def initWithPrelude (prog : Expr) : Except String Machine := do
  let mp ← boot
  let featurePrograms ← features
  return { Machine.initOn mp.heap prog with
    globals := mp.globals, numericLiterals := mp.numericLiterals, featurePrograms }

end Prelude
end RubyCore
