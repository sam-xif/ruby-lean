import Denote.Rules.Method.FlowDefine
import Denote.Rules.Method.FlowCallRule
import Denote.Rules.Expr.Sequence
import Denote.Rules.Expr.Branch
import Denote.Rules.Expr.BranchMissing
import Denote.Rules.Expr.BareName
import Denote.Rules.Primitive.Primitive
import Denote.Rules.Expr.Array
import Denote.Rules.Expr.Hash
import Denote.Judgment.RulesCtx
import Denote.Rules.Method.MethodDefine
import Denote.Rules.Method.MethodCall
import Denote.Rules.Bounded.Recursive
import Denote.Rules.Class.ClassRules
import Denote.Rules.Module.ModuleRule
import Denote.Rules.Class.ClassConstant
import Denote.Rules.Init.InitRules
import Denote.Rules.Init.SuperInitRules
import Denote.Rules.Subclass.SubclassDeclActual
import Denote.Rules.Inherited.InheritedRules
import Denote.Rules.Constructor.DefaultConstructorExpr
import Denote.Rules.Singleton.SingletonRules
import Denote.Rules.Instance.ScalarWrite
import Denote.Judgment.FlowRules
import Denote.Rules.Method.BodyDefine
import Denote.Rules.Method.BodyCallRule


/-! All proof providers for the complete registry. The rebuild profile imports
only its active providers through ActiveProofs.lean. -/
