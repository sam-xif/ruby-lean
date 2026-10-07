import Books.TypeSoundness.Rules.Method.FlowDefine
import Books.TypeSoundness.Rules.Method.FlowCallRule
import Books.TypeSoundness.Rules.Expr.Sequence
import Books.TypeSoundness.Rules.Expr.Branch
import Books.TypeSoundness.Rules.Expr.BranchMissing
import Books.TypeSoundness.Rules.Expr.BareName
import Books.TypeSoundness.Rules.Primitive.Primitive
import Books.TypeSoundness.Rules.Expr.Array
import Books.TypeSoundness.Rules.Expr.Hash
import Books.TypeSoundness.Judgment.RulesCtx
import Books.TypeSoundness.Rules.Method.MethodDefine
import Books.TypeSoundness.Rules.Method.MethodCall
import Books.TypeSoundness.Rules.Bounded.Recursive
import Books.TypeSoundness.Rules.Class.ClassRules
import Books.TypeSoundness.Rules.Module.ModuleRule
import Books.TypeSoundness.Rules.Class.ClassConstant
import Books.TypeSoundness.Rules.Init.InitRules
import Books.TypeSoundness.Rules.Init.SuperInitRules
import Books.TypeSoundness.Rules.Subclass.SubclassDeclActual
import Books.TypeSoundness.Rules.Inherited.InheritedRules
import Books.TypeSoundness.Rules.Constructor.DefaultConstructorExpr
import Books.TypeSoundness.Rules.Singleton.SingletonRules
import Books.TypeSoundness.Rules.Instance.ScalarWrite
import Books.TypeSoundness.Judgment.FlowRules
import Books.TypeSoundness.Rules.Method.BodyDefine
import Books.TypeSoundness.Rules.Method.BodyCallRule


/-! All proof providers for the complete registry. The rebuild profile imports
only its active providers through ActiveProofs.lean. -/
