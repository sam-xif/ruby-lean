import Ratchet.DJudge
import Ratchet.CheckInit

/-! Annotation-checked body artifacts. Lookup proves code membership and exact context;
neither cached signatures nor a receiver's call-site shape can stand in for a body proof. -/
set_option autoImplicit false
namespace Ratchet

structure CheckedBody (κ : Ctx) (I : Ty) (decl : Defn) where
  params : List SigParam
  ret : Ty
  out : Env
  paramShape : decl.params = params.map (fun p => Param.req p.1)
  paramsFO : ∀ p ∈ params, FirstOrder p.2 = true ∧ isAliasTy p.2 = false
  returnFO : FirstOrder ret = true
  judged : DJudge params decl.body ret out κ I κ I

structure CachedBody where
  ctx : Ctx
  spine : Ty
  decl : Defn
  body : CheckedBody ctx spine decl
  deriv : Deriv

abbrev BodyCache := List CachedBody

structure CachedMember extends CachedBody where
  owner : String

structure CachedInitializer where
  ctx : Ctx
  owner : String
  decl : Defn
  body : CheckedInitializer ctx decl
  deriv : Deriv

structure CheckedCache where
  top : BodyCache := []
  members : List CachedMember := []
  initializers : List CachedInitializer := []

/-- Equal code tables alone do not pin annotations. Branches must also agree on cached
signatures, rather than silently selecting one branch's declared parameter/field types. -/
def cacheSignaturesB (a b : CheckedCache) : Bool :=
  (a.top.map fun c => (c.decl.name, c.body.params, c.body.ret, c.spine)) ==
    (b.top.map fun c => (c.decl.name, c.body.params, c.body.ret, c.spine)) &&
  (a.members.map fun c => (c.owner, c.decl.name, c.body.params, c.body.ret, c.spine)) ==
    (b.members.map fun c => (c.owner, c.decl.name, c.body.params, c.body.ret, c.spine)) &&
  (a.initializers.map fun c => (c.owner, c.decl.name, c.body.params, c.body.ret, c.body.fields)) ==
    (b.initializers.map fun c => (c.owner, c.decl.name, c.body.params, c.body.ret, c.body.fields))

structure CallableBody (κ : Ctx) (I : Ty) (name : String) where
  decl : Defn
  nameOk : decl.name = name
  body : CheckedBody (κ.withFrame (some ⟨"Object", "Object", decl.name⟩)) I decl
  installed : decl ∈ κ.defs

def findBody (κ : Ctx) (I : Ty) (name : String) : BodyCache → Option (CallableBody κ I name)
  | [] => none
  | c :: cs =>
    let found : Option (CallableBody κ I name) := do
      if hn : c.decl.name = name then do
        let ⟨hc⟩ ← ctxEq? c.ctx (κ.withFrame (some ⟨"Object", "Object", c.decl.name⟩))
        if hi : c.spine = I then do
          let ⟨hd⟩ ← defnMem? c.decl κ.defs
          some ⟨c.decl, hn, by simpa only [hc, hi] using c.body, hd⟩
        else none
      else none
    found.orElse (fun _ => findBody κ I name cs)

structure FoundClass (C : CTable) (name : String) where
  cls : Cls
  member : cls ∈ C
  nameOk : cls.name = name

/-- First matching positive record, with both membership and identity evidence. -/
def findClass (name : String) : (C : CTable) → Option (FoundClass C name)
  | [] => none
  | c :: cs => if hn : c.name = name then some ⟨c, by simp, hn⟩ else do
      let f ← findClass name cs
      some ⟨f.cls, List.mem_cons.mpr (Or.inr f.member), f.nameOk⟩

structure CallableInitializer (κ : Ctx) (c : Cls) where
  decl : Defn
  nameOk : decl.name = "initialize"
  installed : decl ∈ c.methods
  body : CheckedInitializer (initializerBodyCtx κ c.name) decl

def findInitializer (κ : Ctx) (c : Cls) : List CachedInitializer → Option (CallableInitializer κ c)
  | [] => none
  | b :: bs =>
    let found : Option (CallableInitializer κ c) := do
      if b.owner != c.name then none else do
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
  body : CheckedBody (instanceBodyCtx κ ⟨c.name, c.name, decl.name⟩ fields) fields decl

def findMember (κ : Ctx) (c : Cls) (name : String) : List CachedMember → Option (CallableMember κ c name)
  | [] => none
  | b :: bs =>
    let found : Option (CallableMember κ c name) := do
      if b.owner != c.name then none else do
      if hn : b.decl.name = name then do
      if hf : FirstOrder b.spine = true then do
        let ⟨hc⟩ ← ctxEq? b.ctx (instanceBodyCtx κ ⟨c.name, c.name, b.decl.name⟩ b.spine)
        let ⟨hd⟩ ← defnMem? b.decl c.methods
        some ⟨b.decl, hn, hd, b.spine, hf, by simpa only [hc] using b.body⟩
      else none
      else none
    found.orElse (fun _ => findMember κ c name bs)

/-- No initializer means only an open empty annotation, never a default constructor. -/
def memberFields (κ : Ctx) (c : Cls) (cache : CheckedCache) : Ty :=
  ((findInitializer κ c cache.initializers).map (·.body.fields)).getD .ivar0

end Ratchet
