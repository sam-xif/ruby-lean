import RubyCore.Machine
import RubyCore.Builtins.Objects

/-
The axiomatized builtin methods (artifact 01 §2 `origin = builtin`): primitive
rules keyed by bid = "Owner#name", registered into H₀'s method tables by
Boot.builtinMethods so that lookup/inheritance/shadowing are uniform — a user
`def to_s` on Object shadows the builtin through the ordinary dispatch rule.

Error messages are byte-for-byte from CRuby 4.0.5 probes (2026-07-07); the
difftest engine is the enforcement mechanism.

Anything not modeled answers `unsupported` (never a guessed value) — the
fragment gate, not an error.
-/

namespace RubyCore

namespace Builtins

/-- Run builtin `bid` ("Owner#name"). `implicitSelf` is whether the send had
    no explicit receiver (needed by nothing yet; visibility is deferred). -/
def run (bid : String) (recv : Value) (args : List Value) (m : Machine) : BRes :=
  let h := m.heap
  if zeroArgBids.contains bid && !args.isEmpty then
    .err Boot.argumentErrorId
      s!"wrong number of arguments (given {args.length}, expected 0)" m
  else if dupBids.contains bid || cloneBids.contains bid then
    -- One rule for every class (L66): copies the payload *and* the instance
    -- variables (`str.dup` keeps `@ivar` [V]); `dup` drops the frozen bit,
    -- `clone` keeps it. Gates where a copy would need more than the object:
    -- a singleton class (clone copies it) or a class/module payload (a duped
    -- class is anonymous, which our `name` field cannot express).
    match recv with
    | .ref o =>
      if (h.get o).eigen.isSome then
        .unsupported "dup/clone of an object with a singleton class"
      else match (h.get o).payload with
        | .cls _ => .unsupported "dup/clone of a class/module"
        | .rng _ => .unsupported "dup/clone of a Random (state identity)"
        | _ => let (v, m) := dupObj m o (cloneBids.contains bid); .ok v m
    | _ => .ok recv m   -- immediates dup/clone to themselves [V]
  else
  runObjects bid recv args m

end Builtins

end RubyCore
