import Ratchet.Check.MethodFlowCertificate
import Ratchet.Check.CheckCallbackBody

/-! Definition-side method flow checking. No actual callback code, argument value or
capture environment is an input. Every successful result carries an all-code derivation. -/
set_option autoImplicit false
namespace Ratchet

mutual
def checkMethodFlowExpr (fuel : Nat) (κ : Ctx) (I : Ty) (fr : Frame) (ps : List Ty) (ret : Ty)
    (Γ : MethodLocalEnv) (facts : CallbackFacts) (e : Expr) (d : Deriv) :
    Option (CertifiedMethodFlow κ I fr ps ret Γ facts e) :=
  match fuel with
  | 0 => none
  | n + 1 => do
    if hΓ : Γ.validB = true then do
    if hI : FirstOrder I = true then do
    if hs : κ.selfTy = none then do
    if hc : κ.consts = [] then do
    match he : e, d with
    | .int a, .intLit b =>
      if a == b then some ⟨.fixed .int, Γ, false, facts, rfl, hΓ, fun _ => by cases he; exact .intLit⟩ else none
    | .nil, .nilLit => some ⟨.fixed .nilT, Γ, false, facts, rfl, hΓ, fun _ => by cases he; exact .nilLit⟩
    | .var .lvar x, .var .lvar y => do
      if x != y then none else do
      match hg : Γ.get? x with
      | none => none
      | some τ =>
        let hv := Γ.get_valid hΓ hg
        some ⟨τ, Γ, facts.aliases.contains x, facts, hv, hΓ, fun code => by
          cases he
          exact .var (by rw [Γ.get_instantiate, hg]; rfl) (τ.noAlias hv code)⟩
    | .vasgn .lvar x rhs, .vasgn .lvar y dr => do
      if x != y then none else do
      let c ← checkMethodFlowExpr n κ I fr ps ret Γ facts rhs dr
      if ht : c.ty.staleB x c.ty = false then do
      if hi : killClosOverSpine I x (c.ty.instantiate default) = I then do
      if ho : (c.out.after x c.ty).validB = true then
        some ⟨c.ty, c.out.after x c.ty, c.callback, c.outFacts.write x c.callback,
          c.typeValid, ho, fun code => by
            cases he
            rw [MethodLocalEnv.after_instantiate c.envValid]
            exact .vasgn (c.judged code) ((c.ty.stale_instantiate c.typeValid x c.ty code).trans ht)
              (c.ty.noAlias c.typeValid code) (callback_context_noStale hs hc fr x _)
              ((c.ty.spine_instantiate code hI x).trans hi)⟩
      else none
      else none
      else none
    | .seq es, .seq ds => do
      let c ← checkMethodFlowSeq n κ I fr ps ret Γ facts es ds
      some ⟨c.ty, c.out, c.callback, c.outFacts, c.typeValid, c.envValid,
        fun code => by cases he; exact .sequence (c.judged code)⟩
    | .send (some recv) name [arg] none, .callbackCall dr [da] => do
      match hps : ps with
      | [σ] => do
        let r ← checkMethodFlowExpr n κ I fr ps ret Γ facts recv dr
        if hr : r.callback = true then do
        let a ← checkMethodFlowExpr n κ I fr ps ret r.out r.outFacts arg da
        if ht : a.ty = .fixed σ then do
        if hp : plainArgB arg = true then do
        if hf : nameFreeN κ name = true then do
        if hn : procCallNameB name = true then do
        if hv : MethodLocalTy.validB (.fixed ret) = true then
          some ⟨.fixed ret, a.out, false, a.outFacts, hv, a.envValid, fun code => by
            cases he
            simpa only [hps, MethodLocalTy.instantiate] using DMethodFlow.call
              (by simpa only [hps, hr] using r.judged code)
              (by simpa only [hps, ht, MethodLocalTy.instantiate] using a.judged code)
              (a.out.activation a.envValid code) hp hf hn⟩
        else none
        else none
        else none
        else none
        else none
        else none
      | _ => none
    | _, _ => do
      if hf : Γ.fixedB = true then do
        let c ← checkCallbackExpr n κ I fr ps ret (Γ.instantiate default) e d
        if ht : MethodLocalTy.validB (.fixed c.ty) = true then do
        if ho : (MethodLocalEnv.ofEnv c.out).validB = true then
          some ⟨.fixed c.ty, .ofEnv c.out, false, .empty, ht, ho, fun code => by
            rw [MethodLocalEnv.fixed_instantiate hf, MethodLocalEnv.instantiate_ofEnv]
            exact .embed c.judged⟩
        else none
        else none
      else none
    else none
    else none
    else none
    else none

def checkMethodFlowSeq (fuel : Nat) (κ : Ctx) (I : Ty) (fr : Frame) (ps : List Ty) (ret : Ty)
    (Γ : MethodLocalEnv) (facts : CallbackFacts) (es : List Expr) (ds : List Deriv) :
    Option (CertifiedMethodFlowSeq κ I fr ps ret Γ facts es) :=
  match fuel with
  | 0 => none
  | n + 1 => match es, ds with
    | [e], [d] => do
      let c ← checkMethodFlowExpr n κ I fr ps ret Γ facts e d
      some ⟨c.ty, c.out, c.callback, c.outFacts, c.typeValid, c.envValid,
        fun code => .last (c.judged code)⟩
    | e :: e' :: es, d :: d' :: ds => do
      let h ← checkMethodFlowExpr n κ I fr ps ret Γ facts e d
      let t ← checkMethodFlowSeq n κ I fr ps ret h.out h.outFacts (e' :: es) (d' :: ds)
      some ⟨t.ty, t.out, t.callback, t.outFacts, t.typeValid, t.envValid,
        fun code => .cons (h.judged code) (t.judged code)⟩
    | _, _ => none
end

def checkBoundCallbackBody (fuel : Nat) (κ : Ctx) (I : Ty) (decl : Defn) (hint : Deriv) :
    Option (CheckedBoundCallbackBody κ I decl) := do
  match hp : decl.params, hint with
  | [.block (some localName)], .defBlock name [] bs br ret body => do
    if name != decl.name then none else do
    if hb : bs.all (fun τ => FirstOrder τ && !isAliasTy τ) = true then do
    if hbr : FirstOrder br = true then do
    if hr : FirstOrder ret = true then do
      let c ← checkMethodFlowExpr fuel κ I ⟨"Object", "Object", decl.name, false⟩ bs br
        [(localName, .callback)] ⟨[localName]⟩ decl.body body
      if ht : c.ty = .fixed ret then
        some ⟨localName, bs, br, ret, c.out, c.callback, c.outFacts, hp, hb, hbr, hr,
          fun code => by simpa only [ht, MethodLocalTy.instantiate, MethodLocalEnv.instantiate,
            List.map_cons, List.map_nil] using c.judged code⟩
      else none
    else none
    else none
    else none
  | _, _ => none

end Ratchet
