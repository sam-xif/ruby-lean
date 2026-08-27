import RubyCore.Judgment.Frag
import RubyCore.Cert.Validate

/-!
# `Deriv` and its local checker (J25) — judgment-layer.md §4(3), J2

A certificate is a **derivation**: a first-order tree mirroring `Judge`'s
constructors, emitted by any untrusted tool, verified by the trusted `Deriv.check`
— which records nothing global, computes no joins, and searches for nothing: every
non-deterministic choice a rule makes (a join bound, a continuation environment, a
loop-head stackmap, a declared signature) is a *field of the node*, and the checker
only tests the rule's side conditions and threads the deterministic data
(environments, tables) between children. The soundness lemma
(`Proof/Judgment/Adequacy.lean`) is one induction because the constructors mirror
`Judge`'s one-to-one.

Fuel-recursive by the L73 discipline: the whole point is that a certificate check
is a `decide` (norm 5), and a well-founded mutual block does not kernel-reduce.
The node set covers the machine-typed fragment (`MFrag`, J20–J23); a node for a
rule outside it would type-check the *judgment* fine but leave `judge_sound_cert`
without a preservation case, so the checker grows in step with the fragment.
-/

namespace RubyCore.Judgment

open RubyCore.Types
open RubyCore.Cert

/-! ## The derivation tree

Each constructor is one `Judge` rule; fields are the rule's chosen data —
everything a checker cannot recompute deterministically. -/
mutual
inductive Deriv where
  | int | flt | str | sym | tru | fls | nil
  | self
  | varLvar
  | vasgnLvar (rhs : Deriv)
  | seq (ds : DerivSeq)
  | ifElse (cond t els : Deriv) (τj : Ty) (Γc : Env)
  | ifNone (cond t : Deriv) (τj : Ty) (Γc : Env)
  | while' (Γl : Env) (cond body : Deriv)
  | vcall
  | const
  | varIvar
  | varGvar
  | vasgnIvar (rhs : Deriv)
  | vasgnGvar (rhs : Deriv)
  | array (elems : DerivArgs)
  | send (recv : DerivRecv) (args : DerivArgs)
  | defDecl (τs : List Ty) (σ : Ty) (bs : Option BlockSig) (body : Deriv)
  | defPromote (body : Deriv)
  | classTop (body : Deriv)
  | sub (d : Deriv) (σ : Ty) (Γ'' : Env)
deriving Repr

inductive DerivRecv where
  | self | expl (d : Deriv)
deriving Repr

inductive DerivSeq where
  | nil | single (d : Deriv) | cons (d : Deriv) (rest : DerivSeq)
deriving Repr

inductive DerivArgs where
  | nil | cons (d : Deriv) (rest : DerivArgs)
deriving Repr
end

/-- `defFree`, on fuel — the original is well-founded (`termination_by sizeOf`),
    which does not kernel-reduce (L73), and the promotion node's check runs under
    `decide`. Sound against the original (`Proof/Judgment/Adequacy.lean`). -/
def defFreeB : Nat → Expr → Bool
  | 0, _ => false
  | n + 1, e =>
    match e with
    | .def' _ _ _ => false
    | .class' _ _ _ => false
    | .seq es => es.all (defFreeB n)
    | .if' c t els =>
      defFreeB n c && defFreeB n t &&
        (match els with | some e' => defFreeB n e' | none => true)
    | .while' c b => defFreeB n c && defFreeB n b
    | .vasgn _ _ rhs => defFreeB n rhs
    | .send r _ args blk =>
      (match r with | some r' => defFreeB n r' | none => true) &&
        args.all (defFreeB n) &&
        (match blk with | some b => defFreeB n b | none => true)
    | .block _ _ b => defFreeB n b
    | .array es => es.all (defFreeB n)
    | .ret e => (match e with | some e' => defFreeB n e' | none => true)
    | .cpath base _ => (match base with | some b => defFreeB n b | none => true)
    | .super' args blk =>
      args.all (defFreeB n) && (match blk with | some b => defFreeB n b | none => true)
    | .splat e => (match e with | some e' => defFreeB n e' | none => true)
    | .zsuper blk => (match blk with | some b => defFreeB n b | none => true)
    | _ => true

/-- A structural size for fuel bounds (the derived `SizeOf` does not compile to
    executable code here, and the checker must). -/
def tySize : Ty → Nat
  | .nilable s => tySize s + 1
  | .union a b => tySize a + tySize b + 1
  | .arrayOf e => tySize e + 1
  | .arrow0 r => tySize r + 1
  | .arrowCons q r => tySize q + tySize r + 1
  | _ => 1

/-- Enough `subJb` fuel for a pair: every step of `subJb` structurally shrinks one
    side, so the summed sizes bound the depth. -/
def tyFuel (σ τ : Ty) : Nat := tySize σ + tySize τ + 1

/-- The list form, for `subJsb`. -/
def tysFuel (σs τs : List Ty) : Nat :=
  σs.foldl (fun a t => a + tySize t) (τs.foldl (fun a t => a + tySize t) 1)

/-- The narrowing rung's shape gate: the plain `if` nodes refuse a bare local
    read as condition (those are `ifNarrow*` derivations, not yet nodes). -/
def notBareLvar : Expr → Bool
  | .var .lvar _ => false
  | _ => true

mutual

/-- **The local checker.** `check n d D Γ e top ctx = some (τ, Γ', D')` reads:
    the derivation `d` establishes `Judge D Γ e top ctx τ Γ' D'`. Fuel decreases
    on every call. -/
def check : Nat → Deriv → Decls → Env → Expr → Bool → JCtx →
    Option (Ty × Env × Decls)
  | 0, _, _, _, _, _, _ => none
  | n + 1, d, D, Γ, e, top, ctx =>
    match d, e with
    | .int, .int _ => some (.int, Γ, D)
    | .flt, .flt _ => some (.float, Γ, D)
    | .str, .str _ => some (.cls "String", Γ, D)
    | .sym, .sym _ => some (.sym, Γ, D)
    | .tru, .tru => some (.bool, Γ, D)
    | .fls, .fls => some (.bool, Γ, D)
    | .nil, .nil => some (.nilT, Γ, D)
    | .self, .self' =>
      match ctx.selfCls with
      | some cc => some (.cls cc, Γ, D)
      | none => none
    | .varLvar, .var .lvar x =>
      match envGet? Γ x with
      | some τ => some (τ, Γ, D)
      | none => none
    | .vasgnLvar rhs, .vasgn .lvar x e' =>
      if ctx.inBlock then none
      else
        match check n rhs D Γ e' top ctx with
        | some (τ, Γ₁, D₁) => some (τ, envSet Γ₁ x τ, D₁)
        | none => none
    | .seq ds, .seq es => checkSeq n ds D Γ es top ctx
    | .const, .const nm =>
      match constTy? D nm with
      | some τ => some (τ, Γ, D)
      | none => none
    | .varIvar, .var .ivar x =>
      match ctx.selfCls with
      | some cc =>
        match ivarTy? D cc x with
        | some σ => some (mkNilable σ, Γ, D)
        | none => none
      | none => none
    | .varGvar, .var .gvar x =>
      if plainGlobal x then
        match globalTy? D x with
        | some σ => some (mkNilable σ, Γ, D)
        | none => none
      else none
    | .vasgnIvar rhs, .vasgn .ivar x e' =>
      match ctx.selfCls with
      | some cc =>
        match check n rhs D Γ e' top ctx with
        | some (τ, Γ₁, D₁) =>
          match ivarTy? D₁ cc x with
          | some σ => if subJb (tyFuel τ σ) τ σ then some (τ, Γ₁, D₁) else none
          | none => some (τ, Γ₁, D₁)
        | none => none
      | none => none
    | .vasgnGvar rhs, .vasgn .gvar x e' =>
      if plainGlobal x then
        match check n rhs D Γ e' top ctx with
        | some (τ, Γ₁, D₁) =>
          match globalTy? D₁ x with
          | some σ => if subJb (tyFuel τ σ) τ σ then some (τ, Γ₁, D₁) else none
          | none => none
        | none => none
      else none
    | .array ds, .array es =>
      match checkElems n ds D Γ es top ctx with
      | some (Γ', D') => some (.cls "Array", Γ', D')
      | none => none
    | .ifElse dc dt de τj Γc, .if' cond t (some els) =>
      -- The plain rule only — a bare-lvar condition is the narrowing rung's node.
      if notBareLvar cond then
      match check n dc D Γ cond top ctx with
      | some (_, Γ₁, D₁) =>
        match check n dt D₁ Γ₁ t top ctx with
        | some (τt, Γt, Dt) =>
          match check n de D₁ Γ₁ els top ctx with
          | some (τe, Γe, Dt') =>
            if Dt' == Dt && subJb (tyFuel τt τj) τt τj && subJb (tyFuel τe τj) τe τj
                && subEnvB Γc Γt && subEnvB Γc Γe then
              some (τj, Γc, Dt)
            else none
          | none => none
        | none => none
      | none => none
      else none
    | .ifNone dc dt τj Γc, .if' cond t none =>
      if notBareLvar cond then
      match check n dc D Γ cond top ctx with
      | some (_, Γ₁, D₁) =>
        match check n dt D₁ Γ₁ t top ctx with
        | some (τt, Γt, Dt) =>
          if Dt == D₁ && subJb (tyFuel τt τj) τt τj
              && subJb (tyFuel .nilT τj) .nilT τj
              && subEnvB Γc Γt && subEnvB Γc Γ₁ then
            some (τj, Γc, D₁)
          else none
        | none => none
      | none => none
      else none
    | .while' Γl dc db, .while' cond body =>
      if subEnvB Γl Γ then
        match check n dc D Γl cond top (loopCtx ctx Γl) with
        | some (_, Γ₁, Dc) =>
          if Dc == D && subEnvB Γl Γ₁ then
            match check n db D Γl body top (loopCtx ctx Γl) with
            | some (_, Γ₂, Db) =>
              if Db == D && subEnvB Γl Γ₂ then some (.nilT, Γl, D) else none
            | none => none
          else none
        | none => none
      else none
    | .vcall, .vcall mname =>
      match ctx.selfCls with
      | some cc =>
        match sigOf D (.cls cc) mname with
        | some ([], τret) => some (τret, Γ, D)
        | _ => none
      | none => none
    | .send dr da, .send recvO mname args none =>
      match checkRecv n dr D Γ recvO top ctx with
      | some (τr, Γ₁, D₁) =>
        match checkArgs n da D₁ Γ₁ args top ctx with
        | some (τs, Γ₂, D₂) =>
          match sigOf D₂ τr mname with
          | some (ps, τret) =>
            if subJsb (tysFuel τs ps) τs ps then
              some (τret, Γ₂, D₂)
            else none
          | none => none
        | none => none
      | none => none
    | .defDecl τs σ bs db, .def' name ps body =>
      if declaresName D name || name == "method_added"
          || decide (τs.length ≠ ps.length) then none
      else
        match check n db D (bindParamsJ ps τs [])
            body false (methodCtx ctx name τs (some σ) bs) with
        | some (τb, _, Db) =>
          if Db == D && subJb (tyFuel τb σ) τb σ then some (.sym, Γ, D) else none
        | none => none
    | .defPromote db, .def' name [] body =>
      if declaresName D name || name == "method_added" || top
          || name == "initialize"
          || !(reopenableClasses.contains ctx.cls)
          || groundClassNames.contains ctx.cls
          || !(defFreeB n body)
          || !(ctx.ret == none) || !(ctx.inLoop == none) || ctx.inBlock then none
      else
        match check n db D [] body false (methodCtx ctx name [] none none) with
        | some (τb, _, Db) =>
          if Db == D then
            some (.sym, Γ, addRow D ctx.cls name { params := [], ret := τb })
          else none
        | none => none
    | .classTop db, .class' name none body =>
      if reopenableClasses.contains name && top then
        match check n db D [] body false ({ cls := name } : JCtx) with
        | some (τ, _, Db) => some (τ, Γ, Db)
        | none => none
      else none
    | .sub d' σ Γ'', e =>
      match check n d' D Γ e top ctx with
      | some (τ, Γ', D') =>
        if subJb (tyFuel τ σ) τ σ && subEnvB Γ'' Γ' then some (σ, Γ'', D')
        else none
      | none => none
    | _, _ => none

def checkRecv : Nat → DerivRecv → Decls → Env → Option Expr → Bool → JCtx →
    Option (Ty × Env × Decls)
  | 0, _, _, _, _, _, _ => none
  | n + 1, dr, D, Γ, ro, top, ctx =>
    match dr, ro with
    | .self, none =>
      match ctx.selfCls with
      | some cc => some (.cls cc, Γ, D)
      | none => none
    | .expl d, some r => check n d D Γ r top ctx
    | _, _ => none

def checkSeq : Nat → DerivSeq → Decls → Env → List Expr → Bool → JCtx →
    Option (Ty × Env × Decls)
  | 0, _, _, _, _, _, _ => none
  | n + 1, ds, D, Γ, es, top, ctx =>
    match ds, es with
    | .nil, [] => some (.nilT, Γ, D)
    | .single d, [e] => check n d D Γ e top ctx
    | .cons d rest, e :: e₂ :: es' =>
      match check n d D Γ e top ctx with
      | some (_, Γ₁, D₁) => checkSeq n rest D₁ Γ₁ (e₂ :: es') top ctx
      | none => none
    | _, _ => none

def checkArgs : Nat → DerivArgs → Decls → Env → List Expr → Bool → JCtx →
    Option (List Ty × Env × Decls)
  | 0, _, _, _, _, _, _ => none
  | n + 1, da, D, Γ, es, top, ctx =>
    match da, es with
    | .nil, [] => some ([], Γ, D)
    | .cons d rest, e :: es' =>
      match check n d D Γ e top ctx with
      | some (τ, Γ₁, D₁) =>
        match checkArgs n rest D₁ Γ₁ es' top ctx with
        | some (τs, Γ', D') => some (τ :: τs, Γ', D')
        | none => none
      | none => none
    | _, _ => none

def checkElems : Nat → DerivArgs → Decls → Env → List Expr → Bool → JCtx →
    Option (Env × Decls)
  | 0, _, _, _, _, _, _ => none
  | n + 1, da, D, Γ, es, top, ctx =>
    match da, es with
    | .nil, [] => some (Γ, D)
    | .cons d rest, e :: es' =>
      match check n d D Γ e top ctx with
      | some (_, Γ₁, D₁) => checkElems n rest D₁ Γ₁ es' top ctx
      | none => none
    | _, _ => none

end

/-- The toplevel context, as the judgment sees it — the shape `Machine.init`'s
    activation is judged in. -/
def topJCtx : JCtx := { cls := "Object" }

/-- A judgment-layer certificate: the table half (claimed rows, as the C-ladder's
    `RowClaim`s) and the derivation. -/
structure JCert where
  deltaRows : List RowClaim := []
  deriv : Deriv
deriving Repr

/-- The table a J-certificate names — the same fold `Cert.table` uses. -/
def JCert.table (c : JCert) (p : Expr) : Decls :=
  c.deltaRows.foldl (fun D r => addRow D r.cls r.name r.sig) (declsOf p)

/-- The claimed rows' parameters, checked ground (J22's dispatch-boundary bill). -/
def rowsGroundB (rows : List RowClaim) : Bool :=
  rows.all fun r => r.sig.params.all groundTy

/-- **The J-validator**: the table guards, the fragment gate, and the checked
    derivation. `fuel` bounds both the fragment scan and the derivation walk; any
    value at least the program's size works, and the checker is total either way. -/
def validateJ (c : JCert) (p : Expr) (fuel : Nat) : Bool :=
  rowsGuarded (declsOf p) c.deltaRows &&
  rowsGroundB c.deltaRows &&
  mfragB fuel p &&
  (check fuel c.deriv (c.table p) [] p true topJCtx).isSome

end RubyCore.Judgment
