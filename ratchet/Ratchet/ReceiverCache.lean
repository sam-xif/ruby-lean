import Ratchet.BodyCache

/-! Receiver-aware cached bodies carry both an actual static lookup route and a proof
in the exact receiver/owner context. A parent-body proof cannot be cast to a child. -/
set_option autoImplicit false
namespace Ratchet

structure CallableInitializerAt (κ : Ctx) (c : Cls) where
  owner : String
  decl : Defn
  nameOk : decl.name = "initialize"
  route : MemberRoute κ.classes c.name owner decl
  body : CheckedInitializer (initializerBodyCtxAt κ c.name owner) decl

def findInitializerAt (κ : Ctx) (c : Cls) : List CachedInitializer → Option (CallableInitializerAt κ c)
  | [] => none
  | b :: bs =>
    let found : Option (CallableInitializerAt κ c) := do
      if b.receiver != c.name then none else do
      if hn : b.decl.name = "initialize" then do
        let route ← memberRoute? κ.classes c.name b.owner b.decl
        let ⟨hc⟩ ← ctxEq? b.ctx (initializerBodyCtxAt κ c.name b.owner)
        some ⟨b.owner, b.decl, hn, route, by simpa only [hc] using b.body⟩
      else none
    found.orElse (fun _ => findInitializerAt κ c bs)

structure CallableMemberAt (κ : Ctx) (c : Cls) (name : String) where
  owner : String
  decl : Defn
  nameOk : decl.name = name
  route : MemberRoute κ.classes c.name owner decl
  fields : Ty
  fieldsFO : FirstOrder fields = true
  body : CheckedBody (instanceBodyCtx κ ⟨c.name, owner, decl.name⟩ fields) fields decl

def findMemberAt (κ : Ctx) (c : Cls) (name : String) : List CachedMember → Option (CallableMemberAt κ c name)
  | [] => none
  | b :: bs =>
    let found : Option (CallableMemberAt κ c name) := do
      if b.receiver != c.name then none else do
      if hn : b.decl.name = name then do
      if hf : FirstOrder b.spine = true then do
        let route ← memberRoute? κ.classes c.name b.owner b.decl
        let ⟨hc⟩ ← ctxEq? b.ctx (instanceBodyCtx κ ⟨c.name, b.owner, b.decl.name⟩ b.spine)
        some ⟨b.owner, b.decl, hn, route, b.spine, hf, by simpa only [hc] using b.body⟩
      else none
      else none
    found.orElse (fun _ => findMemberAt κ c name bs)

def receiverFields (κ : Ctx) (c : Cls) (cache : CheckedCache) : Ty :=
  ((findInitializerAt κ c cache.initializers).map (·.body.fields)).getD .ivar0

/-- Completeness is checked over declared selectors, not merely over entries the cache
happens to contain. No initializer still means no constructor admission. -/
def receiverCacheCompleteB (κ : Ctx) (cache : CheckedCache) : Bool :=
  (κ.classes.map (·.name)).eraseDups.all fun cn =>
    match findClass cn κ.classes, ancestors? κ.classes cn with
    | some c, some chain =>
      (chain.flatMap (ownNames κ.classes)).eraseDups.all fun name =>
        if name == "initialize" then (findInitializerAt κ c.cls cache.initializers).isSome
        else (findMemberAt κ c.cls name cache.members).isSome
    | _, _ => false

theorem receiverCacheCompleteB_selectors {κ : Ctx} {cache : CheckedCache} {cn : String}
    {c : FoundClass κ.classes cn} {chain : List String}
    (h : receiverCacheCompleteB κ cache = true)
    (hc : findClass cn κ.classes = some c) (ha : ancestors? κ.classes cn = some chain) :
    (chain.flatMap (ownNames κ.classes)).eraseDups.all (fun name =>
      if name == "initialize" then (findInitializerAt κ c.cls cache.initializers).isSome
      else (findMemberAt κ c.cls name cache.members).isSome) = true := by
  have hn : cn ∈ κ.classes.map (·.name) := List.mem_map.mpr ⟨c.cls, c.member, c.nameOk⟩
  have hs := List.all_eq_true.mp h cn (by simpa using hn)
  simpa only [hc, ha] using hs

/-- Completeness produces a full receiver-aware body artifact, not only a signature. -/
theorem receiverCacheCompleteB_member {κ : Ctx} {cache : CheckedCache} {cn name : String}
    {c : FoundClass κ.classes cn} {chain : List String}
    (h : receiverCacheCompleteB κ cache = true)
    (hc : findClass cn κ.classes = some c) (ha : ancestors? κ.classes cn = some chain)
    (hm : name ∈ chain.flatMap (ownNames κ.classes)) (hn : name ≠ "initialize") :
    ∃ b, findMemberAt κ c.cls name cache.members = some b := by
  have hs := List.all_eq_true.mp (receiverCacheCompleteB_selectors h hc ha) name (by simpa using hm)
  have hs : (findMemberAt κ c.cls name cache.members).isSome = true := by simpa [hn] using hs
  cases he : findMemberAt κ c.cls name cache.members with
  | none => rw [he] at hs; cases hs
  | some b => exact ⟨b, rfl⟩

theorem receiverCacheCompleteB_initializer {κ : Ctx} {cache : CheckedCache} {cn : String}
    {c : FoundClass κ.classes cn} {chain : List String}
    (h : receiverCacheCompleteB κ cache = true)
    (hc : findClass cn κ.classes = some c) (ha : ancestors? κ.classes cn = some chain)
    (hm : "initialize" ∈ chain.flatMap (ownNames κ.classes)) :
    ∃ b, findInitializerAt κ c.cls cache.initializers = some b := by
  have hs := List.all_eq_true.mp (receiverCacheCompleteB_selectors h hc ha) "initialize" (by simpa using hm)
  have hs : (findInitializerAt κ c.cls cache.initializers).isSome = true := hs
  cases he : findInitializerAt κ c.cls cache.initializers with
  | none => rw [he] at hs; cases hs
  | some b => exact ⟨b, rfl⟩

#print axioms receiverCacheCompleteB_member
#print axioms receiverCacheCompleteB_initializer
end Ratchet
