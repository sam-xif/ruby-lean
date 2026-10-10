/-
Starting from the booted heap without booting.

`Prelude.initWithPrelude` runs the prelude and then places the program on the
heap that leaves. `Prelude.initOnBooted` places the program on
`Booted.heap`, a literal that *is* that heap
(`RubyCore/Generated/BootedHeap.lean`), and runs nothing.

The two are equal: `Books/Metatheory/Heap/BootedHeap.lean` proves
`initWithPrelude_eq_initOnBooted`. The boot remains the definition; this is a
form of its result that costs nothing to start from, which matters to a proof,
where the kernel would otherwise re-run the boot for every statement it checks.

`Generated/BootedHeap.lean` is a build artifact: it is not in the repository,
and `make` writes it (`lake exe genbootedheap`) before anything that needs it is
built. That is why `RubyCore.lean` does not import this module — the model
itself builds without the literal.
-/
import RubyCore.Boot
import RubyCore.Generated.BootedHeap

namespace RubyCore
namespace Prelude

/-- The initial machine for `prog` on the booted heap, taken from the literal. -/
def initOnBooted (prog : Expr) : Except String Machine := do
  let featurePrograms ← features
  return { Machine.initOn Booted.heap prog with
    globals := Booted.globals, numericLiterals := Booted.numericLiterals, featurePrograms }

end Prelude
end RubyCore
