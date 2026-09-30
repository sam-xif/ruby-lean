import Ratchet.Check.Check

namespace Ratchet

-- The actual verdict follows the shared clink policy for every supported rule.
#guard validateD (.int 7) (.intLit 7) == clinkEnabled "intLit"
#guard validateD (.flt 0) (.fltLit 0) == clinkEnabled "fltLit"
#guard validateD (.str "ok") (.strLit "ok") == clinkEnabled "strLit"
#guard validateD (.sym "ok") (.symLit "ok") == clinkEnabled "symLit"
#guard validateD .tru .truLit == clinkEnabled "truLit"
#guard validateD .fls .flsLit == clinkEnabled "flsLit"
#guard validateD .nil .nilLit == clinkEnabled "nilLit"

-- An enabled rule still checks the program against the exact certificate.
#guard !validateD (.int 7) (.intLit 8)
#guard !validateD (.int 7) .nilLit
#guard !validateD (.flt 0) (.fltLit 1)
#guard !validateD (.str "ok") (.strLit "bad")
#guard !validateD (.sym "ok") (.symLit "bad")

-- Raw syntactic checking remains available to internal body/cache checks.
-- Its success cannot bypass the actual validator's current restricted evidence.
#guard (check fuelD [] (.seq [.int 7]) (.seq [.intLit 7])).isSome
#guard !validateD (.seq [.int 7]) (.seq [.intLit 7])
#guard (check fuelD [] (.int 7) (.flow (.intLit 7))).isSome
#guard !validateD (.int 7) (.flow (.intLit 7))

#print axioms validateD_enabled
#print axioms validateD_typed
end Ratchet
