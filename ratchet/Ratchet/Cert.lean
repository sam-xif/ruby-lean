import Ratchet.Ty
import Ratchet.Expr

/-!
The certificate, redesigned around the real `Expr`'s own `BEq` instance rather than a
parallel type-annotated shadow tree: a `Cert` is a flat list of **claims**, each pairing
a subterm (an actual `Expr`, matched against the program by structural `==`) with the
`Ty` it claims that subterm has. This mirrors why `Expr`/`Param`/`KwEntry` derive `BEq`
at all in the real model (`../lean/RubyCore/Syntax.lean`'s docstring: "added for the
certificate language... keyed on the subterm a claim is about") — porting `Expr`
essentially invites this design, and it scales better than a shadow AST would: a claim
is needed only where `Ratchet/Validate.lean`'s `chk` cannot *synthesize* a subterm's
type structurally (an arithmetic literal never needs one; an unmodeled builtin method or
a declared function signature does).

A claim's `expr` field is decoded with the exact same `Decode.expr` used for whole
programs (`Ratchet/Expr.lean`) — one wire format for both, since a claim's `expr` is
literally a fragment of real RubyCore JSON.
-/

namespace Ratchet

open Lean (Json)

structure Claim where
  expr : Expr
  ty : Ty
deriving Repr

def Claim.ofJson? (j : Json) : Except String Claim := do
  let e ← Decode.expr (← j.getObjVal? "expr")
  let ty ← Ty.ofJson? (← j.getObjVal? "ty")
  return { expr := e, ty := ty }

structure Cert where
  claims : List Claim
deriving Repr

def Cert.ofJson? (j : Json) : Except String Cert := do
  let claims ← jList j "claims" Claim.ofJson?
  return { claims := claims }

/-- Does `c` claim a type for exactly this subterm? Structural equality (`Expr`'s
`BEq`), not position: two syntactically identical subterms occurring at different
places in the program share a claim, which is the intended behaviour (the claim is
*about the term*, not about a tree address). -/
def Cert.lookup (c : Cert) (e : Expr) : Option Ty :=
  (c.claims.find? (fun cl => cl.expr == e)).map (·.ty)

end Ratchet
