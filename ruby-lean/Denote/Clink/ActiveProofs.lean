import Denote.Judgment.Context
import Denote.Rules.Expr.Sequence
import Denote.Rules.Primitive.Primitive
import Denote.Rules.Expr.Branch
import Denote.Rules.Expr.BranchMissing
import Denote.Rules.Expr.BareName

/-! Proof providers for the active rebuild profile: literals, locals, sequences
and primitive sends with checked argument lists, branches and guarded bare names.
Add providers when re-enabling their clinks. For the complete
profile, import Denote.Clink.FullProofs here. Disabled providers are not imported. -/
