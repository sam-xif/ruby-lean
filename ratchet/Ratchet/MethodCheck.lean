import Ratchet.Check

/-! Annotation-checked method bodies, before installing a callable signature. This artifact
stores a body derivation, not a promise to re-infer it at a call. It says nothing about whether
the method has been installed; dispatch must establish that separately.
-/

set_option autoImplicit false
namespace Ratchet

/-- The required-positional, first-order method boundary currently proved by the semantics.
The outgoing locals may change, but the context and ivar spine must be preserved. -/
structure CheckedBody (κ : Ctx) (I : Ty) (decl : Defn) where
  params : List SigParam
  ret : Ty
  out : Env
  paramShape : decl.params = params.map (fun p => Param.req p.1)
  paramsFO : ∀ p ∈ params, FirstOrder p.2 = true ∧ isAliasTy p.2 = false
  returnFO : FirstOrder ret = true
  judged : DJudge params decl.body ret out κ I κ I

/-- Check the declaration's body once in its annotation environment. Caller locals and
argument values are deliberately not inputs. Return compatibility is exact for now;
subtyping needs a proved denotation-inclusion rule, not the legacy unchecked `subTy`. -/
def checkMethodBody (fuel : Nat) (κ : Ctx) (I : Ty) (decl : Defn) :
    Deriv → Option (CheckedBody κ I decl)
  | .defDecl name ps ret db => do
    if name != decl.name then none else do
    if hp : paramEqAll decl.params (ps.map (fun p => Param.req p.1)) = true then do
      if ht : ps.all (fun p => FirstOrder p.2 && !isAliasTy p.2) = true then do
        if hr : FirstOrder ret = true then do
          let c ← check fuel ps decl.body db κ I
          if hret : c.ty = ret then do
            let ⟨hctx⟩ ← ctxEq? c.ctx κ
            if hspine : c.spine = I then
              some ⟨ps, ret, c.out, paramEqAll_sound hp,
                by simpa only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] using ht,
                hr, by simpa only [hret, hctx, hspine] using c.judged⟩
            else none
          else none
        else none
      else none
    else none
  | _ => none

end Ratchet
