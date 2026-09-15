import Ratchet.ClassCheckControls
import Ratchet.SubclassHeader

/-! Receiver-cache pilots do not claim whole-program subclass admission. They check every
inherited body from the source annotation and reject field changes before any call. -/
set_option autoImplicit false
namespace Ratchet.ReceiverCacheControls
open ClassCheckControls

def parent : Certified [] (cls "LabelBox") :=
  (check 80 [] (cls "LabelBox") (clsHint "LabelBox" (.cls "String"))).get (by decide +kernel)
def child : Cls := subclassHeader "LabelChild" "LabelBox"
def childBodyCtx : Ctx := subclassHeaderCtx (classBodyCtx parent.ctx child.name) child.name "LabelBox"
def callerCtx : Ctx := returnScopeCtx parent.ctx childBodyCtx
def refreshed : CheckedCache := (refreshBodies 80 callerCtx .ivar0 parent.cache).get (by decide +kernel)
def init : CallableInitializerAt callerCtx child :=
  (findInitializerAt callerCtx child refreshed.initializers).get (by decide +kernel)
def get : CallableMemberAt callerCtx child "get" :=
  (findMemberAt callerCtx child "get" refreshed.members).get (by decide +kernel)

#guard init.owner == "LabelBox" && get.owner == "LabelBox"
#guard init.body.params == [("value", .cls "String")]
#guard init.body.fields == fields (.cls "String") && get.fields == fields (.cls "String")
#guard get.body.ret == .cls "String"
#guard receiverCacheCompleteB callerCtx refreshed
#guard (findInitializer callerCtx child refreshed.initializers).isNone
#guard (findMember callerCtx child "get" refreshed.members).isNone
#guard (refreshBodies 0 callerCtx .ivar0 parent.cache).isNone

-- Retagging a parent row cannot replace the exact-context body proof.
#guard (findInitializerAt callerCtx child
  (parent.cache.initializers.map fun c => { c with receiver := child.name })).isNone
#guard (findMemberAt callerCtx child "get"
  (parent.cache.members.map fun c => { c with receiver := child.name })).isNone
-- Completeness examines declared selectors, so dropping an inherited row cannot pass.
#guard !receiverCacheCompleteB callerCtx { refreshed with
  members := refreshed.members.filter fun c => c.receiver == c.owner }
#guard !receiverCacheCompleteB callerCtx { refreshed with
  initializers := refreshed.initializers.filter fun c => c.receiver == c.owner }
#guard !cacheSignaturesB refreshed { refreshed with
  members := refreshed.members.map fun c => { c with receiver := c.owner } }

-- No call occurs: changing the child's fields must recheck the inherited String getter.
#guard (check 150 [] initDecl (initHint (.cls "String")) childBodyCtx .ivar0 parent.cache).isSome
#guard (check 150 [] initDecl (initHint .int) childBodyCtx .ivar0 parent.cache).isNone
#guard (check 150 [] initDecl (initHint (.nilable (.cls "String"))) childBodyCtx .ivar0 parent.cache).isNone

private def overrideGetter : Defn := ⟨"get", [], .tru⟩
private def shadowCtx : Ctx := instanceDeclCtx callerCtx child overrideGetter
-- A real earlier own selector blocks a later cached owner, despite matching names.
#guard (memberRoute? shadowCtx.classes child.name "LabelBox" get.decl).isNone
#guard (memberRoute? callerCtx.classes "Missing" "LabelBox" get.decl).isNone
#guard (memberRoute? callerCtx.classes child.name "Missing" get.decl).isNone
-- A stale newest record cannot hide a method retained in the owner-local bound.
private def stale : CTable := child :: shadowCtx.classes
#guard (memberRoute? stale child.name "LabelBox" get.decl).isNone

def leaf : Cls := subclassHeader "LabelLeaf" child.name
def leafCtx : Ctx := returnScopeCtx callerCtx
  (subclassHeaderCtx (classBodyCtx callerCtx leaf.name) leaf.name child.name)
def leafCache : CheckedCache := (refreshBodies 80 leafCtx .ivar0 refreshed).get (by decide +kernel)
#guard receiverCacheCompleteB leafCtx leafCache
#guard (findInitializerAt leafCtx leaf leafCache.initializers).any (fun b =>
  b.owner == "LabelBox" && b.body.params == init.body.params)
#guard (findMemberAt leafCtx leaf "get" leafCache.members).any (fun b =>
  b.owner == "LabelBox" && b.body.ret == .cls "String")

end Ratchet.ReceiverCacheControls
