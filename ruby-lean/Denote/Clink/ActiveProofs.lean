import Denote.Judgment.Context
import Denote.Rules.Expr.Sequence
import Denote.Rules.Primitive.Primitive
import Denote.Rules.Expr.Branch
import Denote.Rules.Expr.BranchNarrow
import Denote.Rules.Expr.BranchNilQuery
import Denote.Rules.Expr.While
import Denote.Rules.Expr.ConstAssign
import Denote.Rules.Expr.Regexp
import Denote.Rules.Method.MethodRest
import Denote.Rules.Expr.BranchMissing
import Denote.Rules.Expr.BareName
import Denote.Rules.Expr.Array
import Denote.Rules.Expr.Hash
import Denote.Rules.Method.MethodDefine
import Denote.Rules.Method.MethodCall
import Denote.Rules.Bounded.Recursive
import Denote.Rules.Class.ClassDeclActual
import Denote.Rules.Class.ClassReopen
import Denote.Rules.Subclass.SubclassDeclActual
import Denote.Rules.Inherited.InheritedRules
import Denote.Rules.Init.SuperInitRules
import Denote.Rules.Class.ClassConstant
import Denote.Rules.Class.MemberDefActual
import Denote.Rules.Constructor.DefaultNew
import Denote.Rules.Class.CallMethodSigActual
import Denote.Rules.Instance.InstanceRead
import Denote.Rules.Constructor.NewInstActual
import Denote.Rules.Class.VcallMethodSigActual
import Denote.Rules.Module.ModuleDeclActual
import Denote.Rules.Singleton.SingletonRulesActual
import Denote.Rules.Singleton.SingletonRules
import Denote.Rules.Instance.ScalarWrite
import Denote.Judgment.FlowRules
import Denote.Rules.Method.FlowDefine
import Denote.Rules.Method.FlowCallRule
import Denote.Rules.Method.BodyDefine
import Denote.Rules.Method.BodyCallRule

/-! Proof providers for the active rebuild profile: literals, locals, sequences
and primitive sends, branches, guarded bare names, Array/Hash literals, definitions and ordinary/recursive calls.
Add providers when re-enabling their clinks. For the complete
profile, import Denote.Clink.FullProofs here. Disabled providers are not imported. -/
