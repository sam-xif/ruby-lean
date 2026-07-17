/-
RubyCore abstract syntax (artifact 00 §4), mirroring the harness's S-expr node
set (`harness/desugar-dt/lib/rubycore.rb` HEADS) one-for-one, plus the JSON
decoder for the versioned harness↔Lean interface (`lib/export.rb`, v1).

Decoding is positional per head; a head outside the known set is a decode
error (the harness's `is_core?` should have rejected it upstream).
-/
import Lean.Data.Json

namespace RubyCore

/-- The four assignable variable namespaces of `var`/`vasgn`
    (constants have their own scoped forms). -/
inductive VarKind where
  | lvar | ivar | cvar | gvar
deriving Repr, DecidableEq, Inhabited

/-- Rescue `=> target` / massign targets: `[kind, name]` pairs, kind may also
    be `const` (rubycore.rb TARGET_KINDS). -/
inductive TargetKind where
  | lvar | ivar | cvar | gvar | const
deriving Repr, DecidableEq, Inhabited

inductive Expr where
  | int (n : Int)
  | flt (x : Float)
  | str (s : String)
  | sym (s : String)
  | tru
  | fls
  | nil
  | self'
  | var (k : VarKind) (name : String)
  | vasgn (k : VarKind) (name : String) (e : Expr)
  | const (name : String)
  | casgn (name : String) (e : Expr)
  /-- `A::B` (base `some A`) or `::B` (base `none`, absolute toplevel). -/
  | cpath (base : Option Expr) (name : String)
  /-- `A::B = e` / `::B = e`. -/
  | cpathAsgn (base : Option Expr) (name : String) (e : Expr)
  /-- `recv = none` is an implicit-self send (private methods admissible). -/
  | send (recv : Option Expr) (m : String) (args : List Expr) (blk : Option Expr)
  /-- Only occurs as a send's `blk` child. `locals` are `|params; locals|`
      block-locals (fresh, shadowing outer names). -/
  | block (params : List String) (locals : List String) (body : Expr)
  /-- `yield args` — invoke the enclosing method's block (artifact 04 §2). -/
  | yield' (args : List Expr)
  /-- Block-pass `&e` — only occurs as a send/super `blk` child. `none` is an
      anonymous `&` forward of the enclosing method's block. -/
  | blockpass (e : Option Expr)
  | if' (c t : Expr) (e : Option Expr)
  | while' (c body : Expr)
  /-- `begin body end while cond` — body runs once, then loops while `cond`
      (M6/M7 `dowhile`). Distinct head so the run-once flag survives. -/
  | dowhile (body cond : Expr)
  /-- `for tgts in coll; body; end` — `tgts` bind in the *enclosing* scope (no
      block frame; the loop variable leaks) [V]. -/
  | for' (targets : List (TargetKind × String)) (coll body : Expr)
  | def' (name : String) (params : List String) (body : Expr)
  | array (elems : List Expr)
  | hash (pairs : List (Expr × Expr))
  /-- Only valid as a send-arg / array element. -/
  | splat (e : Option Expr)
  | ret (e : Option Expr)
  | brk (e : Option Expr)
  | nxt (e : Option Expr)
  | retry'
  | class' (name : String) (sup : Option Expr) (body : Expr)
  | module' (name : String) (body : Expr)
  /-- `class A::B … end` — `base` is the namespace (`none` = absolute `::B`).
      Scoped defs with an explicit superclass gate at decode (rare). -/
  | scopedClass (base : Option Expr) (name : String) (body : Expr)
  | scopedModule (base : Option Expr) (name : String) (body : Expr)
  | sclass (obj : Expr) (body : Expr)
  | defs (recv : Expr) (name : String) (params : List String) (body : Expr)
  | begin' (body : Expr)
      (rescues : List (List Expr × Option (TargetKind × String) × Expr))
      (els : Option Expr) (ens : Option Expr)
  | super' (args : List Expr) (blk : Option Expr)
  | zsuper (blk : Option Expr)
  /-- `undef n₁, n₂, …` — remove methods from the current definee. -/
  | undef (names : List String)
  /-- `alias new old` — bind `new` to the current definition of `old`. -/
  | alias' (newName oldName : String)
  | seq (es : List Expr)
deriving Repr, Inhabited

namespace Decode

open Lean (Json)

abbrev M := Except String

def fail {α} (msg : String) (j : Json) : M α :=
  .error s!"{msg}: {j.compress.take 200}"

/-- Deliberate out-of-fragment gate at decode time (v4 forms the stepper does
    not model yet: five new param kinds + additive heads). The `UNSUPPORTED: `
    prefix is recognized by `Main` and mapped to engine exit 3 (Unsupported),
    distinct from a genuine malformation, which stays a `fail` → exit 1. -/
def unsupported {α} (msg : String) : M α :=
  .error s!"UNSUPPORTED: {msg}"

def asArr (j : Json) : M (Array Json) :=
  match j with
  | .arr a => .ok a
  | _ => fail "expected array" j

def asStr (j : Json) : M String :=
  match j with
  | .str s => .ok s
  | _ => fail "expected string" j

def asInt (j : Json) : M Int :=
  match j with
  | .num n => if n.exponent == 0 then .ok n.mantissa else fail "expected integer" j
  | _ => fail "expected integer" j

def asFloat (j : Json) : M Float :=
  match j with
  | .num n => .ok n.toFloat
  | _ => fail "expected number" j

def varKind : String → M VarKind
  | "local" => .ok .lvar
  | "ivar"  => .ok .ivar
  | "cvar"  => .ok .cvar
  | "gvar"  => .ok .gvar
  | k => .error s!"bad var kind {k}"

def targetKind : String → M TargetKind
  | "local" => .ok .lvar
  | "ivar"  => .ok .ivar
  | "cvar"  => .ok .cvar
  | "gvar"  => .ok .gvar
  | "const" => .ok .const
  | k => .error s!"bad target kind {k}"

/-- v4 param nodes (rubycore.rb `PARAM_HEADS`). Phase 0 lowers the three
    already-modeled kinds back to the legacy sigil-string convention the
    stepper's `parseParams` consumes (`a` / `*a` / `*` / `&b` / `&`), and gates
    the five genuinely-new binding kinds as Unsupported. Non-mutual with
    `expr`: gated kinds don't recurse into their default sub-expressions. -/
def param (j : Json) : M String := do
  let a ← asArr j
  let some hd := a[0]? | fail "empty param node" j
  let head ← asStr hd
  match head, a with
  | "preq",   #[_, n] => asStr n
  | "prest",  #[_, n] => match n with
      | .null => .ok "*"
      | _ => ("*" ++ ·) <$> asStr n
  | "pblock", #[_, n] => match n with
      | .null => .ok "&"
      | _ => ("&" ++ ·) <$> asStr n
  | "popt",    _ => unsupported "optional param (popt)"
  | "pkey",    _ => unsupported "keyword param (pkey)"
  | "pkwrest", _ => unsupported "keyword-rest param (pkwrest)"
  | "pfwd",    _ => unsupported "argument-forwarding param (pfwd)"
  | "pdestr",  _ => unsupported "destructuring param (pdestr)"
  | _, _ => fail s!"unknown or malformed param head :{head}" j

def params (j : Json) : M (List String) := do
  (← asArr j).toList.mapM param

mutual

partial def opt (j : Json) : M (Option Expr) :=
  match j with
  | .null => .ok none
  | _ => .some <$> expr j

partial def exprs (js : Array Json) : M (List Expr) :=
  js.toList.mapM expr

partial def pair (j : Json) : M (Expr × Expr) := do
  match ← asArr j with
  | #[k, v] => return (← expr k, ← expr v)
  | _ => fail "hash pair" j

/-- Decode a `["cpath", base_or_null, name]` node into `(base?, name)` (used
    both as an expression and as a scoped class/module definition name). -/
partial def cpathParts (j : Json) : M (Option Expr × String) := do
  match ← asArr j with
  | #[_, base, nm] => return (← opt base, ← asStr nm)
  | _ => fail "cpath node" j

partial def rescueClause (j : Json) :
    M (List Expr × Option (TargetKind × String) × Expr) := do
  match ← asArr j with
  | #[excs, ref, handler] =>
    let excs ← exprs (← asArr excs)
    let ref ← match ref with
      | .null => pure none
      | _ => do
        match ← asArr ref with
        | #[k, n] => pure (some (← targetKind (← asStr k), ← asStr n))
        | _ => fail "rescue ref" ref
    return (excs, ref, ← expr handler)
  | _ => fail "rescue clause" j

partial def expr (j : Json) : M Expr := do
  let a ← asArr j
  let some hd := a[0]? | fail "empty node" j
  let head ← asStr hd
  match head, a with
  | "int",   #[_, n] => .int <$> asInt n
  | "flt",   #[_, x] => .flt <$> asFloat x
  | "str",   #[_, s] => .str <$> asStr s
  | "sym",   #[_, s] => .sym <$> asStr s
  | "true",  #[_] => return .tru
  | "false", #[_] => return .fls
  | "nil",   #[_] => return .nil
  | "self",  #[_] => return .self'
  | "var",   #[_, k, n] => return .var (← varKind (← asStr k)) (← asStr n)
  | "vasgn", #[_, k, n, e] =>
      return .vasgn (← varKind (← asStr k)) (← asStr n) (← expr e)
  | "const", #[_, n] => .const <$> asStr n
  | "casgn", #[_, n, e] => return .casgn (← asStr n) (← expr e)
  | "cpath", #[_, base, nm] => return .cpath (← opt base) (← asStr nm)
  | "cpath_asgn", #[_, base, nm, e] =>
      return .cpathAsgn (← opt base) (← asStr nm) (← expr e)
  | "send",  #[_, recv, m, args, blk] =>
      return .send (← opt recv) (← asStr m) (← exprs (← asArr args)) (← opt blk)
  | "block", #[_, ps, ls, body] =>
      return .block (← params ps) (← params ls) (← expr body)
  | "yield", #[_, args] => .yield' <$> exprs (← asArr args)
  | "blockpass", #[_, e] => .blockpass <$> opt e
  | "if",    #[_, c, t, e] => return .if' (← expr c) (← expr t) (← opt e)
  | "while", #[_, c, b] => return .while' (← expr c) (← expr b)
  | "dowhile", #[_, body, cond] => return .dowhile (← expr body) (← expr cond)
  | "for", #[_, tgts, coll, body] =>
      let targets ← (← asArr tgts).toList.mapM fun t => do
        match ← asArr t with
        | #[k, n] => return (← targetKind (← asStr k), ← asStr n)
        | _ => fail "for target" t
      return .for' targets (← expr coll) (← expr body)
  | "def",   #[_, n, ps, body] =>
      return .def' (← asStr n) (← params ps) (← expr body)
  | "array", #[_, elems] => .array <$> exprs (← asArr elems)
  | "hash",  #[_, pairs] => .hash <$> (← asArr pairs).toList.mapM pair
  | "splat", #[_, e] => .splat <$> opt e
  | "return", #[_, e] => .ret <$> opt e
  | "break", #[_, e] => .brk <$> opt e
  | "next",  #[_, e] => .nxt <$> opt e
  | "retry", #[_] => return .retry'
  | "class", #[_, n, sup, body] =>
      match n with
      | .str s => return .class' s (← opt sup) (← expr body)
      | _ =>
        match sup with
        | .null =>
          let (base, nm) ← cpathParts n
          return .scopedClass base nm (← expr body)
        | _ => unsupported "scoped class definition with explicit superclass"
  | "module", #[_, n, body] =>
      match n with
      | .str s => return .module' s (← expr body)
      | _ =>
        let (base, nm) ← cpathParts n
        return .scopedModule base nm (← expr body)
  | "sclass", #[_, obj, body] => return .sclass (← expr obj) (← expr body)
  | "defs",  #[_, recv, n, ps, body] =>
      return .defs (← expr recv) (← asStr n) (← params ps) (← expr body)
  | "begin", #[_, body, rescues, els, ens] =>
      return .begin' (← expr body) (← (← asArr rescues).toList.mapM rescueClause)
        (← opt els) (← opt ens)
  | "super", #[_, args, blk] =>
      return .super' (← exprs (← asArr args)) (← opt blk)
  | "zsuper", #[_, blk] => .zsuper <$> opt blk
  | "undef", #[_, names] => .undef <$> (← asArr names).toList.mapM asStr
  | "alias", #[_, n, o] => return .alias' (← asStr n) (← asStr o)
  | "seq", _ =>
      if a.size ≥ 2 then .seq <$> exprs (a.extract 1 a.size)
      else fail "empty seq" j
  -- v4 additive heads not yet modeled by the stepper: gate as Unsupported
  -- (exit 3) rather than a hard decode failure. Some appear as arg markers
  -- (`kwargs`/`fwd`), the rest as statements.
  | "kwargs",     _ => unsupported "keyword args (kwargs)"
  | "fwd",        _ => unsupported "argument-forwarding marker (fwd)"
  | "defined",    _ => unsupported "defined?"
  | "redo",       _ => unsupported "redo"
  | _, _ => fail s!"unknown or malformed head :{head}" j

end

/-- Decode the full export document `{ "v": 4, "ast": ... }` (export.rb v4:
    structured param nodes + additive heads; see `param` and the `unsupported`
    gates for the forms the Phase-0 stepper does not model yet). -/
def program (j : Json) : M Expr := do
  let v := (j.getObjVal? "v").toOption
  unless v == some (.num 4) do
    .error s!"unsupported rubycore export version: {v.map (·.compress)}"
  match j.getObjVal? "ast" with
  | .ok ast => expr ast
  | .error e => .error s!"missing ast: {e}"

end Decode

end RubyCore
