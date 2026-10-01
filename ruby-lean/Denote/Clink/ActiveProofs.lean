import Denote.Judgment.Context
import Denote.Rules.Expr.Sequence
import Denote.Rules.Primitive.Primitive
import Denote.Rules.Expr.Branch
import Denote.Rules.Expr.BranchMissing
import Denote.Rules.Expr.BareName
import Denote.Rules.Expr.Array
import Denote.Rules.Expr.Hash
import Denote.Rules.Method.MethodDefine
import Denote.Rules.Method.MethodCall

/-! Proof providers for the active rebuild profile: literals, locals, sequences
and primitive sends, branches, guarded bare names, Array/Hash literals, definitions and ordinary calls.
Add providers when re-enabling their clinks. For the complete
profile, import Denote.Clink.FullProofs here. Disabled providers are not imported. -/
