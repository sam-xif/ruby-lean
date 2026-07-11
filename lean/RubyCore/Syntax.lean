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
  | sclass (obj : Expr) (body : Expr)
  | defs (recv : Expr) (name : String) (params : List String) (body : Expr)
  | begin' (body : Expr)
      (rescues : List (List Expr × Option (TargetKind × String) × Expr))
      (els : Option Expr) (ens : Option Expr)
  | super' (args : List Expr) (blk : Option Expr)
  | zsuper (blk : Option Expr)
  | seq (es : List Expr)
deriving Repr, Inhabited

namespace Decode

open Lean (Json)

abbrev M := Except String

def fail {α} (msg : String) (j : Json) : M α :=
  .error s!"{msg}: {j.compress.take 200}"

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

def params (j : Json) : M (List String) := do
  (← asArr j).toList.mapM asStr

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
  | "send",  #[_, recv, m, args, blk] =>
      return .send (← opt recv) (← asStr m) (← exprs (← asArr args)) (← opt blk)
  | "block", #[_, ps, ls, body] =>
      return .block (← params ps) (← params ls) (← expr body)
  | "yield", #[_, args] => .yield' <$> exprs (← asArr args)
  | "blockpass", #[_, e] => .blockpass <$> opt e
  | "if",    #[_, c, t, e] => return .if' (← expr c) (← expr t) (← opt e)
  | "while", #[_, c, b] => return .while' (← expr c) (← expr b)
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
      return .class' (← asStr n) (← opt sup) (← expr body)
  | "module", #[_, n, body] => return .module' (← asStr n) (← expr body)
  | "sclass", #[_, obj, body] => return .sclass (← expr obj) (← expr body)
  | "defs",  #[_, recv, n, ps, body] =>
      return .defs (← expr recv) (← asStr n) (← params ps) (← expr body)
  | "begin", #[_, body, rescues, els, ens] =>
      return .begin' (← expr body) (← (← asArr rescues).toList.mapM rescueClause)
        (← opt els) (← opt ens)
  | "super", #[_, args, blk] =>
      return .super' (← exprs (← asArr args)) (← opt blk)
  | "zsuper", #[_, blk] => .zsuper <$> opt blk
  | "seq", _ =>
      if a.size ≥ 2 then .seq <$> exprs (a.extract 1 a.size)
      else fail "empty seq" j
  | _, _ => fail s!"unknown or malformed head :{head}" j

end

/-- Decode the full export document `{ "v": 3, "ast": ... }` (export.rb v3:
    block-locals slot, `yield`/`blockpass` heads, `&blk` capture params). -/
def program (j : Json) : M Expr := do
  let v := (j.getObjVal? "v").toOption
  unless v == some (.num 3) do
    .error s!"unsupported rubycore export version: {v.map (·.compress)}"
  match j.getObjVal? "ast" with
  | .ok ast => expr ast
  | .error e => .error s!"missing ast: {e}"

end Decode

end RubyCore
