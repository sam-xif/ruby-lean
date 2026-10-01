import Denote.Clink.Registration
import Denote.Clink.Target

/-! The gate mechanism checked independently of Ruby proof providers. The fixture
uses the syntactic family as its target; it makes no semantic safety claim. -/
set_option autoImplicit false
open Lean Meta Elab Command
namespace Ratchet.Denote.Typed

namespace GateFixture
def target := dsynFam
abbrev intProof := @Ratchet.DJudge.intLit
abbrev disabledProof := @Ratchet.DJudge.seq
def enabled (rule : String) : Bool := ["intLit", "fltLit"].contains rule
def onlyJudge : String := "Ratchet.Denote.Typed.DFam.judge"
abbrev primitiveProof := @Ratchet.DJudge.prim
end GateFixture

elab "register_gate_fixture " id:ident " using " proof:ident : command =>
  registerDClink (`Ratchet ++ id.getId) ``GateFixture.target
    (`Ratchet.Denote.Typed.GateFixture ++ proof.getId)
    (`Ratchet.Denote.Typed.GateFixture.Clink ++ dRuleSuffix (`Ratchet ++ id.getId))
    GateFixture.enabled "gate-controls" none

register_gate_fixture DJudge.intLit using intProof

-- Having an imported proof never revives a disabled clink.
/-- error: register_dclink: Ratchet.DJudge.seq is gated out by the gate-controls profile -/
#guard_msgs in
register_gate_fixture DJudge.seq using disabledProof

/-- error: register_dclink: Ratchet.DJudge.fltLit has no answer-typed proof.
Write `theorem Ratchet.Denote.Typed.GateFixture.absent : SemJudgeA …` in Denote/Judgment/JudgeA.lean first.
A rule with no proof is not a rule (Denote/Clink/Spec.lean).
-/
#guard_msgs in
register_gate_fixture DJudge.fltLit using absent

-- Correct types are still demanded for an enabled clink.
/-- error: register_dclink: Ratchet.DJudge.fltLit's semantic proof has the wrong constructor-derived type -/
#guard_msgs in
register_gate_fixture DJudge.fltLit using intProof

-- An unavailable interpretation in a premise must not act as False, making the
-- active rule's semantic obligation vacuous. Exercise the actual refusal path.
elab "register_missing_field_fixture" : command =>
  registerDClink ``Ratchet.DJudge.prim ``GateFixture.target
    ``GateFixture.primitiveProof `Ratchet.Denote.Typed.GateFixture.missingField
    (fun _ => true) "gate-controls" (some ``GateFixture.onlyJudge)

/-- error: register_dclink: Ratchet.DJudge.prim needs unavailable semantic fields: [Ratchet.Denote.Typed.DFam.all] -/
#guard_msgs in
register_missing_field_fixture

#guard clinkPolicyErrors ["intLit"] (some ["typo"]) == ["unknown clink: typo"]
#guard clinkPolicyErrors ["intLit"] (some ["intLit", "intLit"]) == ["duplicate clinks in profile"]
#guard clinkPolicyErrors ["intLit"] none == []
#guard GateFixture.enabled "intLit"
#guard !GateFixture.enabled "DJudgeAll.cons"

#print axioms GateFixture.Clink.intLit
end Ratchet.Denote.Typed
