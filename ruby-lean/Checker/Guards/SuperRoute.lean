import Checker.Guards.MemberRoute

/-! Super lookup starts after the current defining owner, not after the receiver class.
Only the intervening owners must lack the selector; earlier overrides are irrelevant. -/
set_option autoImplicit false
namespace Checker

structure SuperRoute (C : CTable) (receiver current owner : String) (d : Defn) where
  cls : Cls
  member : cls ∈ C
  nameOk : cls.name = owner
  installed : d ∈ cls.methods
  before : List String
  between : List String
  after : List String
  chain : ancestors? C receiver = some (before ++ current :: (between ++ cls.name :: after))
  clear : ∀ cn ∈ between, ∃ old ∈ C, old.name = cn ∧ d.name ∉ ownNames C cn
  /-- The owner is the current definee's direct parent: no program class lies between,
  so super's CRuby-shadow scan is empty. -/
  direct : between = []

def superRoute? (C : CTable) (receiver current owner : String) (d : Defn) :
    Option (SuperRoute C receiver current owner d) := do
  let f ← findClass owner C
  let ⟨hd⟩ ← defnMem? d f.cls.methods
  let ns ← ancestors? C receiver
  let before := ns.takeWhile (· != current)
  let tail := ns.drop (before.length + 1)
  let between := tail.takeWhile (· != owner)
  let after := tail.drop (between.length + 1)
  if hc : ancestors? C receiver = some (before ++ current :: (between ++ f.cls.name :: after)) then do
    if hp : prefixClearB C between d.name = true then
      if hb : between = [] then
        some ⟨f.cls, f.member, f.nameOk, hd, before, between, after, hc, prefixClearB_sound hp, hb⟩
      else none
    else none
  else none

end Checker
