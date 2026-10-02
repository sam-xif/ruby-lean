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
import Denote.Rules.Bounded.Recursive
import Denote.Rules.Class.ClassDeclActual
import Denote.Rules.Class.ClassConstant
import Denote.Rules.Class.MemberDefActual
import Denote.Rules.Constructor.DefaultNew
import Denote.Rules.Class.CallMethodSigActual
import Denote.Rules.Instance.InstanceRead
import Denote.Rules.Constructor.NewInstActual

/-! Proof providers for the active rebuild profile: literals, locals, sequences
and primitive sends, branches, guarded bare names, Array/Hash literals, definitions and ordinary/recursive calls.
Add providers when re-enabling their clinks. For the complete
profile, import Denote.Clink.FullProofs here. Disabled providers are not imported. -/
