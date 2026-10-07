import RubyCore.Machine
import RubyCore.Builtins.Objects

/-
The builtin methods (Semantics 01 §2, `origin = builtin`).

A builtin is a method whose behavior is a primitive rule and not a Ruby body:
`Integer#+`, `String#<<`, `Array#[]`. Each is keyed by an id of the form
`"Owner#name"` and registered in the initial heap's method tables, so lookup,
inheritance and shadowing treat it like any other method. A user `def to_s` on
`Object` shadows the builtin through the ordinary dispatch rule.

The rules are in `Builtins/`, one file per group of classes. Each file matches
its own ids and passes anything else to the next file.

Error messages match CRuby 4.0.5 character for character. Anything not
modeled answers `unsupported`, never a guessed value.
-/

namespace RubyCore

namespace Builtins

/-- Run builtin `bid` ("Owner#name"). `implicitSelf` is whether the send had
    no explicit receiver (needed by nothing yet; visibility is deferred). -/
def run (bid : String) (recv : Value) (args : List Value) (m : Machine) : BRes :=
  let h := m.heap
  if (recv :: args).any (unrepresentableByteStr h)
     && !byteStrAwareBids.contains bid
     -- `dup`/`clone` are the one *class-generic* rule below, and `dupObj` copies
     -- the tag, so they are admitted by list membership rather than by name
     && !dupBids.contains bid && !cloneBids.contains bid then
    -- The byte-string safety net. A binary String holding a byte ≥ 0x80
    -- is the one value a rule can silently *mis-read*: our payload keeps it as a
    -- one-byte character, so a rule that neither propagates the tag nor refuses
    -- hands back a UTF-8 String whose `inspect` renders `È` where CRuby renders
    -- `\xC8`. That is a wrong answer, not a gate, and it is unreachable by
    -- inspection of 60-odd rules — so admission is a *list*: a rule is reached
    -- with such an operand only if it is named in `byteStrAwareBids`.
    .unsupported s!"{bid} with a byte-string operand holding a byte ≥ 0x80"
  else if bid != "Complex#eql?" && (bid.endsWith "#==" || bid.endsWith "#eql?" || bid.endsWith "#!=" ||
      pureEqualityBids.contains bid) && (recv :: args).any (complexEqualityImpure h 100) then
    .unsupported "Complex equality requires effectful component/collection dispatch"
  else if zeroArgBids.contains bid && !args.isEmpty then
    .err Boot.argumentErrorId
      s!"wrong number of arguments (given {args.length}, expected 0)" m
  else if dupBids.contains bid || cloneBids.contains bid then
    -- One rule for every class: copies the payload *and* the instance
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
