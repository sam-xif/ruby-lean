-- Generated from Checker/Check/BodyCache.lean by books/scripts/generate_audited_checker.py.
-- Edit the raw source and regenerate; Lean checks the indexed proof and trace.
import Books.TypeSoundness.Checker.Audit.Erase
import Books.TypeSoundness.Checker.Judgment.DJudge
import Books.TypeSoundness.Checker.Audit.CheckInit
import Books.TypeSoundness.Checker.Guards.MemberRoute
import Books.TypeSoundness.Checker.Audit.MethodCertificate
import Books.TypeSoundness.Checker.Audit.MethodFlowCertificate

/-! Annotation-checked body artifacts. Lookup proves code membership and exact context;
neither cached signatures nor a receiver's call-site shape can stand in for a body proof. -/
set_option autoImplicit false
namespace Checker.Audit
open Checker

/-- A result checked over the entire parameter domain, with its own outgoing locals.
This proof can retain information that the declared return annotation forgets. -/
structure CheckedResult (κ : Ctx) (I : Ty) (decl : Defn) (params : List SigParam) (ty : Ty) where
  out : Env
  firstOrder : FirstOrder ty = true
  {rulesUsed : List String}
  judged : DJudge (used := rulesUsed) params decl.body ty out κ I κ I

structure CheckedBody (κ : Ctx) (I : Ty) (decl : Defn) where
  params : List SigParam
  ret : Ty
  out : Env
  paramShape : decl.params = params.map (fun p => Param.req p.1)
  paramsFO : ∀ p ∈ params, FirstOrder p.2 = true ∧ isAliasTy p.2 = false
  returnFO : FirstOrder ret = true
  {rulesUsed : List String}
  judged : DJudge (used := rulesUsed) params decl.body ret out κ I κ I
  refined : Option ((ty : Ty) × CheckedResult κ I decl params ty) := none

/-- Call hints choose only between two body proofs; a nominal annotation grants no fields. -/
def CheckedBody.resultAt {κ : Ctx} {I : Ty} {decl : Defn}
    (b : CheckedBody κ I decl) (ty : Ty) : Option (CheckedResult κ I decl b.params ty) := do
  if he : b.ret = ty then
    some ⟨b.out, he ▸ b.returnFO, he ▸ b.judged⟩
  else do
    let ⟨actual, result⟩ ← b.refined
    if he : actual = ty then some (he ▸ result) else none

structure CachedBody where
  ctx : Ctx
  spine : Ty
  decl : Defn
  body : CheckedBody ctx spine decl
  deriv : Deriv

abbrev BodyCache := List CachedBody

structure CachedMember extends CachedBody where
  owner : String
  receiver : String

structure CachedSingleton extends CachedBody where
  owner : String

structure CachedInitializer where
  ctx : Ctx
  owner : String
  receiver : String
  decl : Defn
  body : CheckedInitializer ctx decl
  deriv : Deriv

structure CachedCallback where
  ctx : Ctx
  spine : Ty
  decl : Defn
  body : CheckedCallbackBody ctx spine decl
  deriv : Deriv

structure CachedBoundCallback where
  ctx : Ctx
  spine : Ty
  decl : Defn
  body : CheckedBoundCallbackBody ctx spine decl
  deriv : Deriv

structure CheckedCache where
  top : BodyCache := []
  members : List CachedMember := []
  initializers : List CachedInitializer := []
  singletons : List CachedSingleton := []
  callbacks : List CachedCallback := []
  boundCallbacks : List CachedBoundCallback := []

/-- Retain definition annotations for parent replay, independent of receiver-specific
cached output fields. Each super use rechecks the actual selected code in its new context. -/
def initializerSources (cache : CheckedCache) : List InitializerSource :=
  (cache.initializers.filter fun c => c.receiver == c.owner).map fun c =>
    ⟨c.owner, c.decl, c.body.params, c.body.ret, c.deriv⟩

/-- Equal code tables alone do not pin annotations. Branches must also agree on cached
signatures, rather than silently selecting one branch's declared parameter/field types. -/
def cacheSignaturesB (a b : CheckedCache) : Bool :=
  (a.boundCallbacks.map fun c => (c.decl.name, c.body.localName, c.body.blockArgs, c.body.blockRet, c.body.ret, c.spine)) ==
    (b.boundCallbacks.map fun c => (c.decl.name, c.body.localName, c.body.blockArgs, c.body.blockRet, c.body.ret, c.spine)) &&
  (a.callbacks.map fun c => (c.decl.name, c.body.params, c.body.blockArgs, c.body.blockRet, c.body.ret, c.spine)) ==
    (b.callbacks.map fun c => (c.decl.name, c.body.params, c.body.blockArgs, c.body.blockRet, c.body.ret, c.spine)) &&
  (a.singletons.map fun c => (c.owner, c.decl.name, c.body.params, c.body.ret, c.body.refined.map (·.1))) ==
    (b.singletons.map fun c => (c.owner, c.decl.name, c.body.params, c.body.ret, c.body.refined.map (·.1))) &&
  (a.top.map fun c => (c.decl.name, c.body.params, c.body.ret, c.spine, c.body.refined.map (·.1))) ==
    (b.top.map fun c => (c.decl.name, c.body.params, c.body.ret, c.spine, c.body.refined.map (·.1))) &&
  (a.members.map fun c => (c.receiver, c.owner, c.decl.name, c.body.params, c.body.ret, c.spine, c.body.refined.map (·.1))) ==
    (b.members.map fun c => (c.receiver, c.owner, c.decl.name, c.body.params, c.body.ret, c.spine, c.body.refined.map (·.1))) &&
  (a.initializers.map fun c => (c.receiver, c.owner, c.decl.name, c.body.params, c.body.ret, c.body.fields)) ==
    (b.initializers.map fun c => (c.receiver, c.owner, c.decl.name, c.body.params, c.body.ret, c.body.fields))

structure CallableBody (κ : Ctx) (I : Ty) (name : String) where
  decl : Defn
  nameOk : decl.name = name
  body : CheckedBody (κ.withFrame (some ⟨"Object", "Object", decl.name, false⟩)) I decl
  installed : decl ∈ κ.defs

def findBody (κ : Ctx) (I : Ty) (name : String) : BodyCache → Option (CallableBody κ I name)
  | [] => none
  | c :: cs =>
    let found : Option (CallableBody κ I name) := do
      if hn : c.decl.name = name then do
        let ⟨hc⟩ ← ctxEq? c.ctx (κ.withFrame (some ⟨"Object", "Object", c.decl.name, false⟩))
        if hi : c.spine = I then do
          let ⟨hd⟩ ← defnMem? c.decl κ.defs
          some ⟨c.decl, hn, by simpa only [hc, hi] using c.body, hd⟩
        else none
      else none
    found.orElse (fun _ => findBody κ I name cs)

structure CallableInitializer (κ : Ctx) (c : Cls) where
  decl : Defn
  nameOk : decl.name = "initialize"
  installed : decl ∈ c.methods
  body : CheckedInitializer (initializerBodyCtx κ c.name) decl

def findInitializer (κ : Ctx) (c : Cls) : List CachedInitializer → Option (CallableInitializer κ c)
  | [] => none
  | b :: bs =>
    let found : Option (CallableInitializer κ c) := do
      if b.owner != c.name || b.receiver != c.name then none else do
      if hn : b.decl.name = "initialize" then do
        let ⟨hc⟩ ← ctxEq? b.ctx (initializerBodyCtx κ c.name)
        let ⟨hd⟩ ← defnMem? b.decl c.methods
        some ⟨b.decl, hn, hd, by simpa only [hc] using b.body⟩
      else none
    found.orElse (fun _ => findInitializer κ c bs)

structure CallableMember (κ : Ctx) (c : Cls) (name : String) where
  decl : Defn
  nameOk : decl.name = name
  installed : decl ∈ c.methods
  fields : Ty
  fieldsFO : FirstOrder fields = true
  body : CheckedBody (instanceBodyCtx κ ⟨c.name, c.name, decl.name, false⟩ fields) fields decl

def findMember (κ : Ctx) (c : Cls) (name : String) : List CachedMember → Option (CallableMember κ c name)
  | [] => none
  | b :: bs =>
    let found : Option (CallableMember κ c name) := do
      if b.owner != c.name || b.receiver != c.name then none else do
      if hn : b.decl.name = name then do
      if hf : FirstOrder b.spine = true then do
        let ⟨hc⟩ ← ctxEq? b.ctx (instanceBodyCtx κ ⟨c.name, c.name, b.decl.name, false⟩ b.spine)
        let ⟨hd⟩ ← defnMem? b.decl c.methods
        some ⟨b.decl, hn, hd, b.spine, hf, by simpa only [hc] using b.body⟩
      else none
      else none
    found.orElse (fun _ => findMember κ c name bs)

/-- No initializer means only an open empty annotation, never a default constructor. -/
def memberFields (κ : Ctx) (c : Cls) (cache : CheckedCache) : Ty :=
  ((findInitializer κ c cache.initializers).map (·.body.fields)).getD .ivar0

end Checker.Audit
