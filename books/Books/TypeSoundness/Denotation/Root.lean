import RubyCore.Machine

/-! Required boundary invariant for stack-only composition: the active execution
is the root and no external Enumerator fibers are retained. Admission and
preservation proofs must establish it; intermediate runs need not satisfy it. -/
set_option autoImplicit false
namespace Checker.Soundness
open RubyCore

def RootClean (m : Machine) : Prop :=
  m.activeEnumerator = none ∧ m.enumerators = []

def rootCleanB (m : Machine) : Bool :=
  m.activeEnumerator.isNone && m.enumerators.isEmpty

theorem rootCleanB_sound {m : Machine} (h : rootCleanB m = true) : RootClean m := by
  simpa [rootCleanB, RootClean] using h

end Checker.Soundness
