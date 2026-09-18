import Denote.Clink.Spec
import Lean.Elab.Command

/-!
# `Denote/Clink/Form.lean` — deriving a rule's `form` from its constructor

The one piece of metaprogramming the clink mechanism needs, and the reason
`Denote/Clink/Spec.lean` §2 can say "authored once": given a constructor of the judgment's
inductive, replace every occurrence of a family head with a **projection of a `Fam`-like
parameter** and abstract it. One authored rule, two readings, no possibility of drift.

This is `Denote/Sem/Obligations.lean`'s substitution made first-class. That file (now deleted)
replaced one *constant* with another to derive `Obl.<Family>.<rule>` from
`Ratchet.<Family>.<rule>`; here the replacement is a projection, which is what lets the same
`form` be instantiated at both the syntactic and the semantic family instead of producing a
third transcription of the rule.

Parameterised by the family record and its field table, so any judgment can use it:
`Denote/Clink/Registry.lean` supplies `DFam` and a one-row table.
-/

set_option autoImplicit false

open Lean Meta

namespace Ratchet.Denote

/-- The rule, with the family abstracted: `fun F : <famTy> => <ctor type>[<head> := F.<field>, …]`.

`withLocalDeclD` rather than a raw `bvar`, because `Expr.replace` visits subterms under
binders and a de Bruijn index would be correct at the outermost depth and wrong at every
other. An `fvar` is depth-independent, and `mkLambdaFVars` puts the binder back. (Same class
of mistake as clink 63's `generalize`-abstracts-nothing, and the same fix: name the thing
rather than count to it.) -/
def ruleForm (famTy : Name) (table : List (Name × Name)) (ctorType : Lean.Expr) :
    MetaM Lean.Expr :=
  withLocalDeclD `F (mkConst famTy) fun f => do
    let body := Lean.Expr.replace (fun x =>
      match x with
      | .const n _ => (table.lookup n).map (fun fld => mkApp (mkConst fld) f)
      | _ => none) ctorType
    mkLambdaFVars #[f] body

end Ratchet.Denote
