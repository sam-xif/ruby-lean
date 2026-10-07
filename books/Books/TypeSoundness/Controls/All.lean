import Books.TypeSoundness.Controls.AllocationReadyControls
import Books.TypeSoundness.Controls.BoundSourceControls
import Books.TypeSoundness.Controls.BoundedControls
import Books.TypeSoundness.Controls.CallbackSourceControls
import Books.TypeSoundness.Controls.ClassHookControls
import Books.TypeSoundness.Controls.ClosureFlowControls
import Books.TypeSoundness.Controls.ConstantReachControls
import Books.TypeSoundness.Controls.FrozenDefinitionControls
import Books.TypeSoundness.Controls.InitBodyControls
import Books.TypeSoundness.Controls.InstanceCallerControls
import Books.TypeSoundness.Controls.InstanceCodeControls
import Books.TypeSoundness.Controls.InstanceControls
import Books.TypeSoundness.Controls.InstanceDispatchControls
import Books.TypeSoundness.Controls.InstanceResolveControls
import Books.TypeSoundness.Controls.InstanceTableControls
import Books.TypeSoundness.Controls.IteratorEachControls
import Books.TypeSoundness.Controls.LexicalConstantRegression
import Books.TypeSoundness.Controls.MainSingletonRegression
import Books.TypeSoundness.Controls.MethodAliasControls
import Books.TypeSoundness.Controls.MethodCodeControls
import Books.TypeSoundness.Controls.MethodDefineeControls
import Books.TypeSoundness.Controls.MethodDefinitionControls
import Books.TypeSoundness.Controls.MethodDispatchControls
import Books.TypeSoundness.Controls.MethodEntryControls
import Books.TypeSoundness.Controls.MethodOriginControls
import Books.TypeSoundness.Controls.MethodPrefixControls
import Books.TypeSoundness.Controls.MethodRuleControls
import Books.TypeSoundness.Controls.MethodStateControls
import Books.TypeSoundness.Controls.NilFieldControls
import Books.TypeSoundness.Controls.OwnNamesControls
import Books.TypeSoundness.Controls.PrimitiveControls
import Books.TypeSoundness.Controls.ProcPresControls
import Books.TypeSoundness.Controls.RequiredFlowControls
import Books.TypeSoundness.Controls.ScalarWriteControls
import Books.TypeSoundness.Controls.SuperCheckControls
import Books.TypeSoundness.Controls.SuperInitControls

/-!
# `Books/TypeSoundness/Controls/All.lean` — the controls, aggregated on purpose

Every file under `Books/TypeSoundness/Controls/` is a **negative control**: a `#guard`, a
countermodel, or a theorem that pins an obstruction. None of them is imported by a proof, so
nothing pulls them into a build by need, and the gate (`scripts/run_typed_ratchet.sh`) builds
*named targets*.

So they are named here, in one place, and `scripts/check_controls.sh` builds this module and
names any control that has drifted. `lake build` builds every control as well, since the
`TypeSoundness` library is the whole directory.

**Adding a control means adding a line here.** Every control in the directory is listed. The
controls written against the earlier class-entry model, which do not build against the
current one, are in `books/Unrebuilt/TypeSoundness/Controls/`; move one back here, and add
its line, when it is rebuilt.
-/
