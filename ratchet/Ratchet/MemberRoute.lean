import Ratchet.OwnNames
import Ratchet.CtxEq

/-! Proof-carrying static dispatch routes. Owner membership alone is not inheritance:
the declared chain must reach that owner with no earlier own selector. -/
set_option autoImplicit false
namespace Ratchet

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

def prefixClearB (C : CTable) (pre : List String) (name : String) : Bool :=
  pre.all fun cn => C.any fun c => c.name == cn && !(ownNames C cn).contains name

/-- No declared owner before the implicit Object tail defines this selector. This is
not absence at Object itself, and therefore not a default-constructor certificate. -/
def noDeclaredSelectorB (C : CTable) (receiver name : String) : Bool :=
  match ancestors? C receiver with
  | none => false
  | some ns => prefixClearB C ns name

theorem prefixClearB_sound {C : CTable} {pre : List String} {name : String}
    (h : prefixClearB C pre name = true) :
    ∀ cn ∈ pre, ∃ old ∈ C, old.name = cn ∧ name ∉ ownNames C cn := by
  simpa [prefixClearB] using h

structure MemberRoute (C : CTable) (receiver owner : String) (d : Defn) where
  cls : Cls
  member : cls ∈ C
  nameOk : cls.name = owner
  installed : d ∈ cls.methods
  pre : List String
  post : List String
  chain : ancestors? C receiver = some (pre ++ cls.name :: post)
  clear : ∀ cn ∈ pre, ∃ old ∈ C, old.name = cn ∧ d.name ∉ ownNames C cn

def memberRoute? (C : CTable) (receiver owner : String) (d : Defn) :
    Option (MemberRoute C receiver owner d) := do
  let f ← findClass owner C
  let ⟨hd⟩ ← defnMem? d f.cls.methods
  let ns ← ancestors? C receiver
  let pre := ns.takeWhile (· != owner)
  let post := ns.drop (pre.length + 1)
  if hc : ancestors? C receiver = some (pre ++ f.cls.name :: post) then do
    if hp : prefixClearB C pre d.name = true then
      some ⟨f.cls, f.member, f.nameOk, hd, pre, post, hc, prefixClearB_sound hp⟩
    else none
  else none

#print axioms prefixClearB_sound
end Ratchet
