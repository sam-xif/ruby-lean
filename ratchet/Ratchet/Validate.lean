import Ratchet.Cert

/-!
The trusted checker: `validate : Cert → Expr → Bool`, over the **real** `Expr`. `chk`
handles a small, explicitly-scoped fragment of real desugared Ruby structurally
(literals, `var`/`vasgn`/`vcall`, `seq`, `if'`, a small hardcoded arithmetic/string/bool
`send` table, `array`, `hash`, and top-level `def'`-declared functions dispatched by
name); anything else falls through to `Cert.lookup` — an explicit claim is required, or
the program is rejected. No soundness theorem is proved here (see `AGENTS.md`).

**Known, documented simplifications** (not bugs — see `AGENTS.md` §Frontier for the
full list): `var`/`vasgn` do not distinguish `VarKind` (ivars/cvars/gvars share the same
flat environment as locals); an `if`'s branches do not propagate variable
reassignments into the following code (the environment after an `if` is the
environment *before* it); an `if` condition must have exact type `Bool`, not just be
"truthy" (Ruby only treats `nil`/`false` as falsy); a `send` carrying a block is always
rejected regardless of claims (blocks are semantics, deferred per `AGENTS.md`); and any
`def'` whose parameters are not all `Param.req` is rejected (no optional/splat/keyword
params yet).
-/

namespace Ratchet

/-- A hardcoded fragment of Ruby's actual builtin dispatch table — the "declarations"
this package doesn't yet have a mechanism to state as data (contrast the real project's
`Types/Decls.lean`). Extend this, not `Cert.lookup`, for anything that should type-check
without a per-program claim. -/
def builtinSendTy? (recvTy : Ty) (m : String) (argTys : List Ty) : Option Ty :=
  match recvTy, m, argTys with
  | .int, "+", [.int] => some .int
  | .int, "-", [.int] => some .int
  | .int, "*", [.int] => some .int
  | .int, "/", [.int] => some .int
  | .int, "<", [.int] => some .bool
  | .int, "<=", [.int] => some .bool
  | .int, ">", [.int] => some .bool
  | .int, ">=", [.int] => some .bool
  | .cls "String", "+", [.cls "String"] => some (.cls "String")
  | .bool, "!", [] => some .bool
  -- `Object#to_s` is universal in the fragment this package can even represent (nothing
  -- here models an override), so it costs nothing to hardcode.
  | _, "to_s", [] => some (.cls "String")
  | _, "==", [argTy] => if recvTy == argTy then some .bool else none
  | _, "!=", [argTy] => if recvTy == argTy then some .bool else none
  | _, _, _ => none

structure FunSig where
  name : String
  paramTys : List Ty
  retTy : Ty

/-- Flatten a (possibly nested) `seq` into its top-level `def'` statements. Does not
walk into `if'`/`block`/etc. bodies — this package only supports functions declared as
direct top-level statements. -/
partial def collectTopDefs : Expr → List Expr
  | .seq es => es.flatMap collectTopDefs
  | e@(.def' ..) => [e]
  | _ => []

/-- `Param.req` only — `none` if any parameter is optional/rest/keyword/block/forward/
destructured (not yet supported). -/
def paramNames (params : List Param) : Option (List String) :=
  params.mapM fun
    | .req name => some name
    | _ => none

/-- One `FunSig` per top-level `def'`, each read off the certificate's own claim for
that exact `def'` node (an arrow spine `paramTys → retTy`) — the certificate is this
package's only mechanism for declaring a function's signature, there being no separate
`FunCert`/declaration format. `none` if any top-level function has no such claim, or its
claim isn't a well-formed arrow spine. -/
def buildFunSigs (c : Cert) (p : Expr) : Option (List FunSig) :=
  (collectTopDefs p).mapM fun d => do
    let arr ← c.lookup d
    let (ps, r) ← arrowParts? arr
    match d with
    | .def' name _ _ => some { name := name, paramTys := ps, retTy := r }
    | _ => none

mutual

/-- Check a list of subexpressions left to right, threading the environment through
(so `vasgn`s earlier in the list are visible to later ones — real Ruby scoping, not the
lexical `let` of a from-scratch toy language). -/
partial def chkList (c : Cert) (funSigs : List FunSig) (env : Env) :
    List Expr → Option (List Ty × Env)
  | [] => some ([], env)
  | e :: rest => do
    let (t, env') ← chk c funSigs env e
    let (ts, env'') ← chkList c funSigs env' rest
    some (t :: ts, env'')

/-- The one-pass local type-checker. Returns the subterm's type *and* the environment
as updated by any assignment inside it (see the module docstring for what does and does
not thread through an `if`). -/
partial def chk (c : Cert) (funSigs : List FunSig) (env : Env) : Expr → Option (Ty × Env)
  | .int _ => some (.int, env)
  | .flt _ => some (.float, env)
  | .str _ => some (.cls "String", env)
  | .sym _ => some (.sym, env)
  | .tru => some (.bool, env)
  | .fls => some (.bool, env)
  | .nil => some (.nilT, env)
  | .var _ name => do
    let t ← envGet? env name
    some (t, env)
  | .vasgn _ name e => do
    let (t, env') ← chk c funSigs env e
    some (t, envSet env' name t)
  | .vcall name =>
    match funSigs.find? (·.name == name) with
    | some sig => if sig.paramTys.isEmpty then some (sig.retTy, env) else none
    | none => (c.lookup (.vcall name)).map (·, env)
  | .if' cond thenE elseE => do
    let (ct, env1) ← chk c funSigs env cond
    if ct != .bool then none else do
    let (tt, _) ← chk c funSigs env1 thenE
    match elseE with
    | some e => do
      let (et, _) ← chk c funSigs env1 e
      let joined ← joinTy tt et
      some (joined, env1)
    | none => some (mkNilable tt, env1)
  | .seq [] => some (.nilT, env)
  | .seq es => do
    let (tys, env') ← chkList c funSigs env es
    some (tys.getLast!, env')
  | .array elems => do
    let (tys, env') ← chkList c funSigs env elems
    match tys with
    | [] => some (.arrayOf .any, env')
    | t0 :: rest => if rest.all (· == t0) then some (.arrayOf t0, env') else none
  | .hash pairs => do
    let env' ← pairs.foldlM (fun env (k, v) => do
        let (_, env1) ← chk c funSigs env k
        let (_, env2) ← chk c funSigs env1 v
        pure env2) env
    some (.cls "Hash", env')
  | .send _ _ _ (some _) => none  -- blocks: deferred, see the module docstring
  | .send none m args none => do
    let (argTys, env') ← chkList c funSigs env args
    match funSigs.find? (·.name == m) with
    | some sig => if subTys argTys sig.paramTys then some (sig.retTy, env') else none
    | none => (c.lookup (.send none m args none)).map (·, env')
  | .send (some r) m args none => do
    let (rt, env1) ← chk c funSigs env r
    let (argTys, env2) ← chkList c funSigs env1 args
    match builtinSendTy? rt m argTys with
    | some t => some (t, env2)
    | none => (c.lookup (.send (some r) m args none)).map (·, env2)
  | e => (c.lookup e).map (·, env)

end

/-- Does every top-level `def'` body actually type-check against the signature its own
claim declares? -/
def defsOk (c : Cert) (funSigs : List FunSig) (p : Expr) : Bool :=
  (collectTopDefs p).all fun d =>
    match d with
    | .def' name params body =>
      match funSigs.find? (·.name == name), paramNames params with
      | some sig, some names =>
        names.length == sig.paramTys.length &&
          (chk c funSigs (names.zip sig.paramTys) body).map (·.1) == some sig.retTy
      | _, _ => false
    | _ => true

/-- The one entry point this harness exists to grow: does `c` certify `p` as
type-safe? `p` plays the role the "program" plays elsewhere in this project — real
desugared Ruby, decoded straight from `harness/desugar-dt`'s wire format
(`Ratchet/Corpus.lean`). -/
def validate (c : Cert) (p : Expr) : Bool :=
  match buildFunSigs c p with
  | none => false
  | some funSigs =>
    defsOk c funSigs p && (chk c funSigs [] p).isSome

end Ratchet
