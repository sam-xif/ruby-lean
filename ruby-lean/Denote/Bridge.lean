import Ratchet.Check.Check
import Denote.Clink.Registry
import Denote.Sem.Core.Boot

/-! The actual validator's end-to-end safety theorem under the active clink
registry. validateD carries enabled-rule evidence, so this bridge needs only
active clinks and their dependencies. The current rebuilt evidence covers direct
literals; the complete raw-DJudge bridge is retained in Bridge/Full.lean. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

-- Generate only active-clink references. Kernel checking still verifies every
-- selected closure proof and the contradiction used for each gated case.
macro "certify_active_literal" hF:ident : tactic => do
  let mut result ← `(tacticSeq| simp_all [clinkEnabled, clinkProfile])
  for rule in ["intLit", "fltLit", "strLit", "symLit", "truLit", "flsLit", "nilLit"].reverse do
    if clinkEnabled rule then
      let clink := Lean.mkIdent ((`Ratchet.Denote.Typed.DClink).str rule)
      result ← `(tacticSeq| first
        | apply $hF $clink (by simp [dclinks])
        | $result)
  `(tactic| ($result))

/-- The source literal evidence crosses the current registry only when its
exact rule is enabled. No completeness claim about unrestricted DJudge is used. -/
theorem literal_certified {p : Ratchet.Expr} {τ : Ty} {rule : String}
    (hj : LiteralJudge p τ rule) (he : clinkEnabled rule = true)
    {Γ : Env} {κ : Ctx} {I : Ty} :
    (DJudgeC dclinks).judge Γ p τ Γ κ I := by
  cases hj <;> intro F hF <;> certify_active_literal hF

theorem validateD_certified {p : Ratchet.Expr} {d : Deriv}
    (h : validateD p d = true) :
    ∃ τ, (DJudgeC dclinks).judge [] p τ [] ctx0 .ivar0 := by
  obtain ⟨τ, _, hj, he, _⟩ := validateD_enabled h
  exact ⟨τ, literal_certified hj he⟩

/-- Every accepted active literal is safe at every fuel from any conformant
top-level machine. The acceptance hypothesis is the executable validator. -/
theorem validateD_safe {p : Ratchet.Expr} {d : Deriv}
    (h : validateD p d = true)
    {m : Machine} (hm : StateOk ctx0 [] .ivar0 m) : StuckFree m p := by
  obtain ⟨_, hj⟩ := validateD_certified h
  exact dregistry_safe hj hm

theorem validateD_safe_boot {p : Ratchet.Expr} {d : Deriv}
    (h : validateD p d = true) (hb : bootOkB = true) :
    StuckFree bootMachine p := validateD_safe h (stateOk_boot hb)

/-- The final theorem concerns the actual model runner, for arbitrary fuel. -/
theorem validateD_safe_run {p : Ratchet.Expr} {d : Deriv}
    (h : validateD p d = true) (hb : bootOkB = true) (fuel : Nat) :
    Semantics.typeStuck (Semantics.run fuel (toRuby p)) = false := by
  have hs := validateD_safe_boot h hb fuel
  cases hboot : Semantics.bootedMachine with
  | error msg => simp only [Semantics.run, hboot, Semantics.typeStuck]
  | ok m => simpa only [Semantics.run, bootMachine, hboot, evalFrom, Machine.initOn] using hs

#print axioms literal_certified
#print axioms validateD_certified
#print axioms validateD_safe
#print axioms validateD_safe_boot
#print axioms validateD_safe_run
end Ratchet.Denote.Typed
