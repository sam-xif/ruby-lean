import Denote.Sem.ClassHeap
import Denote.Sem.SubclassDispatch

/-! Dispatch after fresh class creation. Old chains stay fixed; the two fresh chains
inherit from Object and Object's eigenclass. Native-name shadow checks remain explicit. -/
set_option autoImplicit false
namespace Ratchet.Denote.FreshClass
open RubyCore Ratchet
open RubyCore.Proof.Judgment (freshClsHeap)

variable {h : Heap} {name : String} {e : ObjId}
local notation "h₁" => freshClsHeap h Boot.objectId name name e

theorem lookup_go_old {ks : List ObjId} (hl : ∀ k ∈ ks, k < h.objs.size) (mn : String) :
    lookup.go h₁ mn ks = lookup.go h mn ks := Subclass.lookup_go_old hl mn

theorem method_old (hc : Proof.ChainsIn h) (hs : Proof.Saturated h)
    {k : ObjId} (hk : k < h.objs.size) (mn : String) :
    Interp.methodOn h₁ k mn = Interp.methodOn h k mn := Subclass.method_old hc hs hk mn

theorem method_class (hc : Proof.ChainsIn h) (hs : Proof.Saturated h) (mn : String) :
    Interp.methodOn h₁ h.objs.size mn = Interp.methodOn h Boot.objectId mn :=
  Subclass.method_class hc hs hc.boot.2.2.2.2 mn

theorem method_eigen (hc : Proof.ChainsIn h) (hs : Proof.Saturated h)
    (he : e < h.objs.size) (mn : String) :
    Interp.methodOn h₁ (h.objs.size + 1) mn = Interp.methodOn h e mn := Subclass.method_eigen hc hs he mn

/-- The old dispatch site whose method table the new site inherits. -/
def parent (h : Heap) (e k : ObjId) : ObjId :=
  if k = h.objs.size then Boot.objectId else if k = h.objs.size + 1 then e else k

theorem parent_old {k : ObjId} (hk : k < h.objs.size) : parent h e k = k := by
  simp only [parent, if_neg (Nat.ne_of_lt hk), if_neg (Nat.ne_of_lt (Nat.lt_succ_of_lt hk))]

theorem method_parent (hc : Proof.ChainsIn h) (hs : Proof.Saturated h)
    (he : e < h.objs.size) (k : ObjId) (mn : String) :
    Interp.methodOn h₁ k mn = Interp.methodOn h (parent h e k) mn :=
  Subclass.method_source hc hs hc.boot.2.2.2.2 he k mn

theorem shadow_old {ks : List ObjId} (hl : ∀ k ∈ ks, k < h.objs.size) (mn : String) :
    Interp.crubyShadow h₁ ks mn = Interp.crubyShadow h ks mn := Subclass.shadow_old hl mn

theorem shadow_before_old (hc : Proof.ChainsIn h) (hs : Proof.Saturated h)
    {k : ObjId} (hk : k < h.objs.size) (owner : ObjId) (mn : String) :
    Interp.crubyShadow h₁ ((ancestors h₁ k).takeWhile (· != owner)) mn =
      Interp.crubyShadow h ((ancestors h k).takeWhile (· != owner)) mn :=
  Subclass.shadow_before_old hc hs hk owner mn

/-- Fresh class names must not introduce an unmodeled native method before the old owner. -/
theorem shadow_before_parent (hc : Proof.ChainsIn h) (hs : Proof.Saturated h)
    (he : e < h.objs.size) (hne : name.isEmpty = false) {mn : String}
    (hn : crubyClassDefines name mn = false)
    (hen : crubyClassDefines ("#<Class:" ++ name ++ ">") mn = false)
    (k owner : ObjId)
    (hp : Interp.crubyShadow h ((ancestors h (parent h e k)).takeWhile (· != owner)) mn = none) :
    Interp.crubyShadow h₁ ((ancestors h₁ k).takeWhile (· != owner)) mn = none :=
  Subclass.shadow_before_source hc hs hc.boot.2.2.2.2 he hne hn hen k owner hp

#print axioms method_parent
#print axioms shadow_before_parent
end Ratchet.Denote.FreshClass
