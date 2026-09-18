import Denote.Controls.BoundedControls
import Denote.Controls.ClassAliasControls
import Denote.Controls.ClassBaseControls
import Denote.Controls.ClassControls
import Denote.Controls.ClassCoreControls
import Denote.Controls.ClassCtorControls
import Denote.Controls.ClassDeclaredControls
import Denote.Controls.ClassFrameControls
import Denote.Controls.ClassFreshnessControls
import Denote.Controls.ClassHeaderControls
import Denote.Controls.ClassNameControls
import Denote.Controls.ClassQueryControls
import Denote.Controls.ClassReturnControls
import Denote.Controls.ClassRootControls
import Denote.Controls.ClassRootNameControls
import Denote.Controls.ClassRuleControls
import Denote.Controls.ClassScopeControls
import Denote.Controls.ClassSitesControls
import Denote.Controls.ClassStateControls
import Denote.Controls.ConstructorControls
import Denote.Controls.ConstructorGeneralControls
import Denote.Controls.ConstructorRunControls
import Denote.Controls.DefaultConstructorControls
import Denote.Controls.InheritedCallControls
import Denote.Controls.InheritedConstructorControls
import Denote.Controls.InitBodyControls
import Denote.Controls.InitControls
import Denote.Controls.InstanceCallerControls
import Denote.Controls.InstanceCodeControls
import Denote.Controls.InstanceControls
import Denote.Controls.InstanceDispatchControls
import Denote.Controls.InstanceResolveControls
import Denote.Controls.InstanceReturnControls
import Denote.Controls.InstanceSiteWriteControls
import Denote.Controls.InstanceSpineControls
import Denote.Controls.InstanceStateControls
import Denote.Controls.InstanceTableControls
import Denote.Controls.MainSiteControls
import Denote.Controls.MemberDefineControls
import Denote.Controls.MethodDispatchControls
import Denote.Controls.MethodEntryControls
import Denote.Controls.MethodInstallControls
import Denote.Controls.MethodRuleControls
import Denote.Controls.MethodStateControls
import Denote.Controls.OwnNamesControls
import Denote.Controls.PointClassControls
import Denote.Controls.PointConstructorControls
import Denote.Controls.PointConstructorExprControls
import Denote.Controls.PointProgramControls
import Denote.Controls.PrimitiveControls
import Denote.Controls.ReceiverCacheControls
import Denote.Controls.RootInitControls
import Denote.Controls.SubclassCoreControls
import Denote.Controls.SubclassDataControls
import Denote.Controls.SubclassDispatchControls
import Denote.Controls.SubclassEntryControls
import Denote.Controls.SubclassHeaderControls
import Denote.Controls.SubclassNameControls
import Denote.Controls.SubclassRunControls
import Denote.Controls.SubclassScopeControls
import Denote.Controls.SubclassStateControls
import Denote.Controls.SubclassTableControls
import Denote.Clink.Controls

/-!
# `Denote/Controls/All.lean` — the controls, aggregated on purpose

Every file under `Denote/Controls/` is a **negative control**: a `#guard`, a countermodel, or
a theorem that pins an obstruction. None of them is imported by a proof, so nothing pulls
them into a build by need — and the lakefile's `Denote.+` glob elaborates them only on a full
`lake build`, while `scripts/run_typed_ratchet.sh` builds *named targets*.

So they are named here, in one place, and the gate builds this module. That used to be
implicit: `ClassControls.lean` imported fifty-one of its siblings, `Safety.lean` imported
seven more, and a control's import list mixed "what I need" with "who I keep alive" —
indistinguishable by reading. Dropping a control from the gate was a one-line deletion in a
file that had every reason to be edited for other purposes.

**Adding a control means adding a line here.** If it is missing, the control still compiles
under `lake build`, but the commit-time gate stops checking it.
-/
