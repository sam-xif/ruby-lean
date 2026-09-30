import Ratchet.Check.Literal

namespace Ratchet
private def literalsOnly (rule : String) : Bool := rule == "intLit"

-- An allowed rule still checks the program against the exact certificate.
#guard validateLiteralD literalsOnly (.int 7) (.intLit 7)
#guard !validateLiteralD literalsOnly (.int 7) (.intLit 8)
#guard !validateLiteralD literalsOnly (.int 7) (.nilLit)

-- A well-typed literal cannot cross a disabled rule; enabling is rule-specific.
#guard validateD (.str "ok") (.strLit "ok")
#guard !validateLiteralD literalsOnly (.str "ok") (.strLit "ok")
#guard !validateLiteralD (fun _ => false) (.int 7) (.intLit 7)
#guard validateLiteralD (fun _ => true) (.flt 0) (.fltLit 0)
#guard validateLiteralD (fun _ => true) (.str "ok") (.strLit "ok")
#guard validateLiteralD (fun _ => true) (.sym "ok") (.symLit "ok")
#guard validateLiteralD (fun _ => true) .tru .truLit
#guard validateLiteralD (fun _ => true) .fls .flsLit
#guard validateLiteralD (fun _ => true) .nil .nilLit
#guard !validateLiteralD (fun _ => true) (.flt 0) (.fltLit 1)
#guard !validateLiteralD (fun _ => true) (.str "ok") (.strLit "bad")
#guard !validateLiteralD (fun _ => true) (.sym "ok") (.symLit "bad")

-- Ordinary acceptance of a compound program or flow wrapper grants no literal
-- acceptance, even if every leaf uses an allowed rule.
#guard validateD (.seq [.int 7]) (.seq [.intLit 7])
#guard !validateLiteralD (fun _ => true) (.seq [.int 7]) (.seq [.intLit 7])
#guard validateD (.int 7) (.flow (.intLit 7))
#guard !validateLiteralD literalsOnly (.int 7) (.flow (.intLit 7))

#print axioms validateLiteralD_typed
#print axioms validateLiteralD_validated
end Ratchet
