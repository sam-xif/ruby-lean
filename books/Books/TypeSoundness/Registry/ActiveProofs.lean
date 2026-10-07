import Books.TypeSoundness.Judgment.Context
import Books.TypeSoundness.Rules.Expr.Sequence
import Books.TypeSoundness.Rules.Primitive.Primitive
import Books.TypeSoundness.Rules.Expr.Branch
import Books.TypeSoundness.Rules.Expr.BranchNarrow
import Books.TypeSoundness.Rules.Expr.BranchNilQuery
import Books.TypeSoundness.Rules.Expr.BranchNilQ
import Books.TypeSoundness.Rules.Expr.While
import Books.TypeSoundness.Rules.Expr.ConstAssign
import Books.TypeSoundness.Rules.Expr.Regexp
import Books.TypeSoundness.Rules.Method.MethodRest
import Books.TypeSoundness.Rules.Expr.BranchIsA
import Books.TypeSoundness.Rules.Expr.BranchIsAIvar
import Books.TypeSoundness.Rules.Expr.CaseEq
import Books.TypeSoundness.Rules.Expr.CaseEqVar
import Books.TypeSoundness.Rules.Expr.AndGuard
import Books.TypeSoundness.Rules.Method.MethodKwOpt
import Books.TypeSoundness.Rules.Expr.SendUnion
import Books.TypeSoundness.Rules.Expr.BranchMissing
import Books.TypeSoundness.Rules.Expr.BareName
import Books.TypeSoundness.Rules.Expr.Array
import Books.TypeSoundness.Rules.Expr.Hash
import Books.TypeSoundness.Rules.Method.MethodDefine
import Books.TypeSoundness.Rules.Method.MethodCall
import Books.TypeSoundness.Rules.Bounded.Recursive
import Books.TypeSoundness.Rules.Class.ClassDeclActual
import Books.TypeSoundness.Rules.Class.ClassReopen
import Books.TypeSoundness.Rules.Subclass.SubclassDeclActual
import Books.TypeSoundness.Rules.Inherited.InheritedRules
import Books.TypeSoundness.Rules.Init.SuperInitRules
import Books.TypeSoundness.Rules.Class.ClassConstant
import Books.TypeSoundness.Rules.Class.MemberDefActual
import Books.TypeSoundness.Rules.Constructor.DefaultNew
import Books.TypeSoundness.Rules.Class.CallMethodSigActual
import Books.TypeSoundness.Rules.Instance.InstanceRead
import Books.TypeSoundness.Rules.Constructor.NewInstActual
import Books.TypeSoundness.Rules.Class.VcallMethodSigActual
import Books.TypeSoundness.Rules.Module.ModuleDeclActual
import Books.TypeSoundness.Rules.Singleton.SingletonRulesActual
import Books.TypeSoundness.Rules.Singleton.SingletonRules
import Books.TypeSoundness.Rules.Instance.ScalarWrite
import Books.TypeSoundness.Judgment.FlowRules
import Books.TypeSoundness.Rules.Method.FlowDefine
import Books.TypeSoundness.Rules.Method.FlowCallRule
import Books.TypeSoundness.Rules.Method.BodyDefine
import Books.TypeSoundness.Rules.Method.BodyCallRule

/-! Proof providers for the active rebuild profile: literals, locals, sequences
and primitive sends, branches, guarded bare names, Array/Hash literals, definitions and ordinary/recursive calls.
Add providers when re-enabling their clinks. For the complete
profile, import Books.TypeSoundness.Registry.FullProofs here. Disabled providers are not imported. -/
