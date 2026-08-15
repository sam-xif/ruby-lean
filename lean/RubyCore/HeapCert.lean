import RubyCore.Interp.Support

/-!
# The heap certificate — `HeapOk` as a `Bool`

F0 (`homebrew/widening-the-fragment.md` §3/§4). `Proof/StaticSoundness.lean`'s
invariant has two conjuncts that are facts about the heap alone — `TableOk` (the
three tabulated `Integer` builtins still resolve, live, public, unshadowed, not
`fromPrelude`) and `NoHook` (`Object` has no `method_added`). Static soundness at
the **prelude-booted** heap needs them there, and they cannot be decided in the
kernel: `Prelude.program` is `Lean.Json.parse Prelude.json` and `Lean.Json.parse`
does not kernel-reduce even on the input `"1"` (measured), while L94 bans the
`native_decide` escape.

So they are decided by *running* this function, and
`Proof/PreludeInv.heapOkB_sound` is the bridge: `heapOkB h = true → HeapOk h`.
The hypothesis of `check_sound_withPrelude` is then one `Bool` about the machine
actually in hand, which `scripts/heapok_probe.lean` computes and
`scripts/check-proofs.sh` fails on.

**This lives outside `Proof/` on purpose.** The alternative — defining it next to
the soundness lemma — means the probe cannot see it (`Proof/` is off the default
target, and an executable must not depend on the metatheory), so the probe would
end up re-implementing the predicate and could silently drift from the one the
theorem is about. One definition, two readers.

It is deliberately **not** wired into `Prelude.boot`: a prelude that redefined
`Integer#+` would be a legitimate model change that breaks the *static* route
only, and refusing to execute would be the wrong response to it. The check
belongs where the proofs are checked.
-/

namespace RubyCore

open Interp

/-- Executable form of `Proof.Static.IntBuiltinResolves`
    (`Proof/BuiltinConformance.lean`). Clause order matches that definition. -/
def intResolvesB (h : Heap) (mname bid : String) : Bool :=
  match lookup h (.int 0) mname with
  | none => false
  | some (owner, md) =>
      (md.builtin == some bid) && !md.undefined && (md.visibility == .pub) &&
        !md.fromPrelude &&
        (crubyShadow h ((ancestors h Boot.integerId).takeWhile (· != owner)) mname).isNone

/-- Executable form of `Proof.Static.HeapOk` — `TableOk` and `NoHook`. -/
def heapOkB (h : Heap) : Bool :=
  intResolvesB h "+" "Integer#+" && intResolvesB h "-" "Integer#-" &&
    intResolvesB h "*" "Integer#*" &&
    (lookup h (.ref Boot.objectId) "method_added").isNone

end RubyCore
