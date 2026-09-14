import Denote.Typed.Clink
import Denote.Typed.PrimitiveControls
import Denote.Typed.MethodEntryControls
import Denote.Typed.MethodStateControls
import Denote.Typed.MethodDispatchControls
import Denote.Typed.MethodInstallControls

/-!
# `Denote/Typed/Controls.lean` — derivations in the certified judgment, and the gate

A separate module from `Denote/Typed/Clink.lean` for a mundane reason worth recording: the
registry `dclinks` is declared *by a command* in that file, and `simp` cannot realize a
same-module generated constant's equations (`enableRealizationsForConst`). From here it is an
ordinary import and `simp [dclinks]` decides membership.

`Denote/Clink/Controls.lean` held the old registry's versions of these and went with it
(clink 68). They matter more here, because the soundness theorem is now about a statement
with progress content.
-/

set_option autoImplicit false

namespace Ratchet.Denote.Typed

open RubyCore Ratchet Ratchet.Denote

/-- The context-general composition path still discharges the existing invariant target. -/
example : SemSafeA [] (.seq [.vasgn .lvar "x" (.int 3), .var .lvar "x"])
    .int [("x", .int)] :=
  semSafeA_iff_context.mpr
    ((SemSafeCtxA.intLit.vasgn (by rfl) (by rfl) (by rfl)).seq
      (SemSafeCtxA.var (by rfl) (by rfl)))

/-- Writes outside `ctx0` retain the explicit context guard and transformed ivar spine. -/
example {κ : Ctx} {Γ : Env} {I : Ty} (hctx : capStaleCtx "x" .int κ = false) :
    SemSafeCtxA κ Γ I (.vasgn .lvar "x" (.int 3)) .int κ (envAfter Γ "x" .int)
      (killClosOverSpine I "x" .int) :=
  SemSafeCtxA.intLit.vasgn (by rfl) (by rfl) hctx

/-- An annotated body with allocation before a branch, proved independently of call values.
Both branches return Integer and preserve the parameter environment and method context. -/
theorem context_branch_body {κ : Ctx} {I : Ty}
    (hlt : nameFreeN κ "<" = true) (hsub : nameFreeN κ "-" = true) :
    SemSafeCtxA κ [("x", .int)] I
      (.seq [.str "ignored", .if'
        (.send (some (.var .lvar "x")) "<" [.int 0] none)
        (.send (some (.int 0)) "-" [.var .lvar "x"] none) (some (.var .lvar "x"))])
      .int κ [("x", .int)] I := by
  have hc : SemSafeCtxA κ [("x", .int)] I
      (.send (some (.var .lvar "x")) "<" [.int 0] none) .bool κ [("x", .int)] I :=
    (SemSafeCtxA.var rfl rfl).prim (.cons SemSafeCtxA.intLit .nil rfl)
      .intLt hlt (by intro h; cases h)
  have ht : SemSafeCtxA κ [("x", .int)] I
      (.send (some (.int 0)) "-" [.var .lvar "x"] none) .int κ [("x", .int)] I :=
    SemSafeCtxA.intLit.prim (.cons (SemSafeCtxA.var rfl rfl) .nil rfl)
      .intSub hsub (by intro h; cases h)
  exact SemSafeCtxA.strLit.seq (hc.if' ht (SemSafeCtxA.var (τ := .int) (x := "x") rfl rfl))

/-- The false path of an omitted else keeps the condition's state, with a nullable result. -/
example {κ : Ctx} {I : Ty} : SemSafeCtxA κ [("x", .bool)] I
    (.if' (.var .lvar "x") (.int 1) none) (.nilable .int) κ [("x", .bool)] I :=
  (SemSafeCtxA.var rfl rfl).ifNoElse SemSafeCtxA.intLit

-- All statements, including ignored literals, have context-indexed proofs.
example {κ : Ctx} {Γ : Env} {I : Ty} : SemSafeCtxA κ Γ I
    (.seq [.flt 0, .sym "ok", .tru, .fls, .nil]) .nilT κ Γ I :=
  SemSafeCtxA.sequence (.cons SemSafeCtxA.fltLit (.cons SemSafeCtxA.symLit
    (.cons SemSafeCtxA.truLit (.cons SemSafeCtxA.flsLit (.last SemSafeCtxA.nilLit)))))

#print axioms context_branch_body

/-- Collection-valued bodies retain the annotated parameter through both allocations. -/
theorem context_collection_body {κ : Ctx} {I : Ty} : SemSafeCtxA κ [("x", .int)] I
    (.hash [(.sym "values", .array [.var .lvar "x", .var .lvar "x"])])
    (.hashOf .sym (.arrayOf .int)) κ [("x", .int)] I := by
  have ha : SemSafeCtxA κ [("x", .int)] I
      (.array [.var .lvar "x", .var .lvar "x"]) (.arrayOf .int) κ [("x", .int)] I :=
    SemSafeCtxA.arrayLit (tys := [.int, .int])
      (.cons (SemSafeCtxA.var rfl rfl) (.cons (SemSafeCtxA.var rfl rfl) .nil rfl) rfl) rfl
  exact SemSafeCtxA.hashLit (ks := [.sym]) (vs := [.arrayOf .int])
    (.cons SemSafeCtxA.symLit ha .nil) rfl rfl

-- A key's outgoing local binding is available to the value, including outside ctx0.
example {κ : Ctx} (hk : capStaleCtx "x" .int κ = false) : SemSafeCtxA κ [] .ivar0
    (.hash [(.vasgn .lvar "x" (.int 1), .var .lvar "x")])
    (.hashOf .int .int) κ [("x", .int)] .ivar0 :=
  SemSafeCtxA.hashLit (ks := [.int]) (vs := [.int])
    (.cons (SemSafeCtxA.intLit.vasgn rfl rfl hk) (SemSafeCtxA.var rfl rfl) .nil) rfl rfl

example {κ : Ctx} {Γ : Env} {I : Ty} (hx : nameFreeN κ "x" = true)
    (hm : nameFreeN κ "method_missing" = true) (hs : κ.selfTy = none) :
    SemSafeCtxA κ Γ I (.vcall "x") .any κ Γ I := SemSafeCtxA.bareName hx hm hs

#guard !nameFreeN { ctx0 with neg := { ctx0.neg with declared := ["x"] } } "x"
#guard !nameFreeN { ctx0 with neg := { ctx0.neg with declared := ["method_missing"] } } "method_missing"
#print axioms context_collection_body

/-! ## Derivations

A derivation is a term polymorphic in the family, so it never mentions `DJudgeC`'s definition
and never needs a closure lemma (`Denote/Clink/Spec.lean` §3). Membership in the registry is
the only side condition, and `simp` decides it against the list. -/

/-- The leaf: `hF c hc` *is* the rule, at whatever family the consumer picked. -/
theorem derivD_intLit {Γ : Env} {n : Int} :
    (DJudgeC dclinks).judge Γ (.int n) .int Γ := by
  intro F hF
  exact hF DClink.intLit (by simp [dclinks])

/-- **The loop, closed, on a statement with progress content.** A derivation using only
registered rules is answer-typed semantically true: for *every* run that reaches an answer —
value or escape — the answer is in the type or the escape is not type-stuck. -/
theorem derivD_intLit_sem {Γ : Env} {n : Int} : SemJudgeA Γ (.int n) .int Γ :=
  dregistry_semJudge derivD_intLit

/-- …and the **safety** half, which is the end of the chain: from any conformant machine, the
program never reaches a type-stuck outcome, at any fuel. -/
theorem derivD_intLit_safe {Γ : Env} {n : Int} {m : Machine}
    (hm : StateOk Ratchet.ctx0 Γ .ivar0 m) : StuckFree m (.int n) :=
  dregistry_safe derivD_intLit hm

/-- The invariant form the safety above is an instance of — and the thing the old
whole-program `SafeJudge` could not say: safety at a machine whose continuation is **not**
empty is available as soon as `DKontOk` has a frame clause for it. Stated here at the one
continuation `DKontOk` admits today, so the shape is on file before the frames arrive. -/
theorem derivD_intLit_safeUnder {Γ : Env} {n : Int} :
    SafeUnder Γ (.int n) .int Γ := dregistry_safeUnder derivD_intLit

/-- And a local read, which is the rule whose premise the certificate cannot supply. -/
theorem derivD_var_sem {Γ : Env} {x : String} {τ : Ty} (hget : envGet? Γ x = some τ)
    (halias : isAliasTy τ = false) : SemJudgeA Γ (.var .lvar x) τ Γ :=
  dregistry_semJudge (by intro F hF; exact hF DClink.var (by simp [dclinks]) hget halias)

/-! ### The family boundary remains enforced

All judgment constructors now have proofs. A constructor outside the family is still
refused; the sequence and argument forms below also check that their premises are semantic
family projections, rather than raw syntactic derivations. -/

/-- error: register_dclink: Ratchet.DPrim.intAdd belongs to Ratchet.DPrim, which is not in DFam.
The list companions join when a rule concluding about them acquires a proof (Denote/Typed/Clink.lean, header).
-/
#guard_msgs in
register_dclink DPrim.intAdd

example : DClink.seq.form dsemFam =
    (∀ {Γ Γ' : Env} {es : List Ratchet.Expr} {τ : Ty},
      SemSeqA Γ es τ Γ' → SemSafeA Γ (.seq es) τ Γ') := rfl

example : DClink.DJudgeAll.cons.form dsemFam =
    (∀ {Γ Γ₁ Γ₂ : Env} {e : Ratchet.Expr} {es : List Ratchet.Expr} {τ : Ty} {tys : List Ty},
      SemSafeA Γ e τ Γ₁ → SemAllA Γ₁ es tys Γ₂ → plainArgB e = true →
        SemAllA Γ (e :: es) (τ :: tys) Γ₂) := rfl

#guard dUncarriedJudgments.isEmpty

example : DClink.DJudgePairs.cons.form dsemFam =
    (∀ {Γ Γk Γv Γ' : Env} {k v : Ratchet.Expr} {ps : List (Ratchet.Expr × Ratchet.Expr)}
      {σ τ : Ty} {ks vs : List Ty},
      SemSafeA Γ k σ Γk → SemSafeA Γk v τ Γv → SemPairsA Γv ps ks vs Γ' →
        SemPairsA Γ ((k, v) :: ps) (σ :: ks) (τ :: vs) Γ') := rfl

#guard dUnregisteredRules.isEmpty

/-! ### …and a proof of a different rule does not stand in for it

The two `rfl`s say what the kernel enforces at the point of registration: both field types are
**computed from the rule**, so `sem := SemA.truLit` in `intLit`'s position is a type error.
Stated as `rfl` rather than as a captured type error on purpose — an error message carries
metavariable numbers and elaborator phrasing, and a control that goes red when Lean rewords a
diagnostic is a control that gets deleted. -/

example : DClink.intLit.form dsemFam =
    (∀ {Γ : Env} {n : Int}, SemSafeA Γ (.int n) .int Γ) := rfl

/-- …and `SemSafeA` really is the pair, so "registered" means both obligations were proved. -/
example {Γ : Env} {n : Int} :
    SemSafeA Γ (.int n) .int Γ = (SemJudgeA Γ (.int n) .int Γ ∧ SafeUnder Γ (.int n) .int Γ) :=
  rfl

example : DClink.intLit.form dsynFam =
    (∀ {Γ : Env} {n : Int}, DJudge Γ (.int n) .int Γ) := rfl

#print axioms derivD_intLit
#print axioms derivD_intLit_sem
#print axioms derivD_intLit_safe
#print axioms derivD_intLit_safeUnder
#print axioms derivD_var_sem


end Ratchet.Denote.Typed
