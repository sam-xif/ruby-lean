import Ratchet.Check.CheckInit
import Ratchet.Guards.ClassCtx

/-! Annotation-domain initializer checks, including uncalled bad bodies. These controls
are supplemented by the whole-program definition/call checks in ClassCheckControls. -/
namespace Ratchet.InitCheckControls

private def κ : Ctx := initializerBodyCtx ctx0 "Packet"
private def body : Expr := .vasgn .ivar "@payload" (.var .lvar "value")
private def decl : Defn := ⟨"initialize", [.req "value"], body⟩
private def hint : Deriv := .ivarAsgn "@payload" (.var .lvar "value")
private def annotation (input output : Ty) : Deriv := .defDecl "initialize" [("value", input)] output hint
private def accepts (input output : Ty) : Bool :=
  (checkInitializerBody 30 κ decl (annotation input output)).isSome

#guard accepts .bool .bool
#guard accepts .int .int
#guard accepts (.arrayOf .int) (.arrayOf .int)
#guard accepts (.nilable .int) (.nilable .int)
#guard accepts (.nilable .int) .any
#guard !accepts (.nilable .int) .int
#guard !accepts .bool .int
#guard !accepts .int .bool
#guard !accepts (.sameAs "outside" .int) .any
#guard (checkInitializerBody 30 κ decl (annotation .bool .bool)).map (·.fields) ==
  some (.ivarCons "@payload" .bool .ivar0)

-- Wrong declaration, required formal order/name, body hint, and exhausted fuel all reject.
#guard (checkInitializerBody 30 κ decl (.defDecl "different" [("value", .bool)] .bool hint)).isNone
#guard (checkInitializerBody 30 κ decl (.defDecl "initialize" [("other", .bool)] .bool hint)).isNone
#guard (checkInitializerBody 30 κ decl (.defDecl "initialize" [] .any hint)).isNone
#guard (checkInitializerBody 30 κ decl (.defDecl "initialize" [("value", .bool)] .bool
  (.ivarAsgn "@wrong" (.var .lvar "value")))).isNone
#guard (checkInitializerBody 30 κ decl (.defDecl "initialize" [("value", .bool)] .bool
  (.ivarAsgn "@payload" (.var .lvar "other")))).isNone
#guard (checkInitializerBody 0 κ decl (annotation .bool .bool)).isNone

-- Unknown locals are not supplied by a caller, and void cannot bypass an unchecked suffix.
private def badTail : Expr := .send none "missing" [] none
private def badDecl : Defn := { decl with body := .seq [body, badTail] }
#guard (checkInitializerBody 30 κ { decl with body := .var .lvar "caller" }
  (.defDecl "initialize" [("value", .bool)] .any (.var .lvar "caller"))).isNone
#guard (checkInitializerBody 30 κ badDecl (.defDecl "initialize" [("value", .bool)] .any
  (.seq [hint, .callSig "missing" [] .any]))).isNone
#guard (checkInitializerBody 30 κ badDecl (.defDecl "initialize" [("value", .bool)] .any
  (.seq [hint]))).isNone

-- The write guard covers context-sensitive aliasing even when the return is ignored.
private def aliased : Ctx := { κ with pos := { κ.pos with consts :=
  [("::ALIAS", .inst "Packet" (.ivarCons "@payload" .nilT .ivar0))] } }
#guard (checkInitializerBody 30 aliased decl (annotation .bool .any)).isNone
private def strengthened : Ctx := { κ with scope := { κ.scope with
  selfTy := some (.inst "Packet" (.ivarCons "@payload" .nilT .ivar0)) } }
#guard (checkInitializerBody 30 strengthened decl (annotation .bool .any)).isNone

private def checked : CheckedInitializer κ decl :=
  (checkInitializerBody 30 κ decl (annotation .bool .bool)).get (by rfl)
#guard (refreshInitializerBody 30 (initializerBodyCtx ctx0 "AnotherPacket") checked hint).isSome
#guard (refreshInitializerBody 30 κ checked hint).map (·.ret) == some .bool
#guard (refreshInitializerBody 30 aliased checked hint).isNone
#guard (refreshInitializerBody 30 strengthened checked hint).isNone
#guard (refreshInitializerBody 30 κ checked (annotation .any .any)).isNone

-- Repeated writes retain only the first-visible, updated field type.
private def twice : Defn := ⟨"initialize", [.req "a", .req "b"], .seq [
  .vasgn .ivar "@slot" (.var .lvar "a"), .vasgn .ivar "@slot" (.var .lvar "b")]⟩
private def twiceHint : Deriv := .defDecl "initialize" [("a", .int), ("b", .bool)] .any
  (.seq [.ivarAsgn "@slot" (.var .lvar "a"), .ivarAsgn "@slot" (.var .lvar "b")])
#guard (checkInitializerBody 30 κ twice twiceHint).map (·.fields) ==
  some (.ivarCons "@slot" .bool .ivar0)
#guard (checkInit 10 κ [] .ivar0 (.seq []) (.seq [])).isNone

end Ratchet.InitCheckControls
