import Lean.Data.Json

/-!
`Expr`/`Param`/`KwEntry` and the JSON `Decode` namespace, **ported verbatim** from
`RubyCore/Syntax.lean` (the real RubyCore AST + its decoder for the versioned
harness↔Lean wire format, `Export::VERSION` 4/5, `harness/desugar-dt/lib/export.rb`).
Constructors, field shapes, and decode logic are unchanged; only the deep
implementation-history commentary (L-numbers, J-numbers, references to proof files that
don't exist in this package) has been trimmed. This means corpus programs in `../corpus/`
are **real desugared Ruby**, produced by the real `harness/desugar-dt/bin/export-json`
pipeline, not hand-authored ASTs — see `scripts/generate_corpus.py`.

Namespaced `Ratchet` rather than `RubyCore` to keep this package's isolation from
`RubyCore/` visible at every use site — nothing here imports that tree.
-/

namespace Ratchet

/-- The four assignable variable namespaces of `var`/`vasgn` (constants have their own
scoped forms: `const`/`casgn`/`cpath`). -/
inductive VarKind where
  | lvar | ivar | cvar | gvar
deriving Repr, DecidableEq, Inhabited

/-- Rescue `=> target` / massign targets: `[kind, name]` pairs; `kind` may also be
`const`. -/
inductive TargetKind where
  | lvar | ivar | cvar | gvar | const
deriving Repr, DecidableEq, Inhabited

mutual
inductive Expr where
  | int (n : Int)
  /-- A regexp literal `/src/opts` — CRuby compiles it at parse time (no `::Regexp`
      lookup at runtime), so it gets its own head rather than desugaring to
      `::Regexp.new(...)`. -/
  | regexpLit (src : String) (opts : Nat)
  /-- A float literal, carried as its IEEE-754 bit pattern: `Float` has no
      `DecidableEq`/useful `BEq`, so the syntax layer (which needs structural equality
      for certificate claim lookup) stores the bits and only makes a `Float` at
      evaluation time. -/
  | flt (bits : UInt64)
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
  /-- A **vcall**: a bare identifier (`foo`) that is not a local variable (Prism's
      `variable_call`). Semantically an implicit-self, zero-arg, block-less send; kept
      as its own head (rather than folded into `send`) because CRuby distinguishes the
      dispatch-miss message: a bare `foo` misses with `NameError` ("undefined local
      variable or method"), while `foo()`/`self.foo`/`foo(1)` miss with `NoMethodError`. -/
  | vcall (m : String)
  /-- Brace-less keyword arguments at a call site (`f(k: 1, **h)`) — only occurs as the
      last element of a send/super `args` list. -/
  | kwargs (entries : List KwEntry)
  /-- `...` argument-forwarding marker at a call site (`g(...)`). -/
  | fwd
  /-- Only occurs as a send's `blk` child. `locals` are `|params; locals|` block-locals
      (fresh, shadowing outer names). -/
  | block (params : List Param) (locals : List String) (body : Expr)
  /-- `yield args` — invoke the enclosing method's block. -/
  | yield' (args : List Expr)
  /-- Block-pass `&e` — only occurs as a send/super `blk` child. `none` is an anonymous
      `&` forward of the enclosing method's block. -/
  | blockpass (e : Option Expr)
  | if' (c t : Expr) (e : Option Expr)
  | while' (c body : Expr)
  /-- `begin body end while cond` — body runs once, then loops while `cond`. -/
  | dowhile (body cond : Expr)
  /-- `for tgts in coll; body; end` — `tgts` bind in the *enclosing* scope (no block
      frame; the loop variable leaks). -/
  | for' (targets : List (TargetKind × String)) (coll body : Expr)
  | def' (name : String) (params : List Param) (body : Expr)
  | array (elems : List Expr)
  | hash (pairs : List (Expr × Expr))
  /-- Only valid as a send-arg / array element. -/
  | splat (e : Option Expr)
  | ret (e : Option Expr)
  | brk (e : Option Expr)
  | nxt (e : Option Expr)
  | retry'
  | redo'
  | class' (name : String) (sup : Option Expr) (body : Expr)
  | module' (name : String) (body : Expr)
  /-- `class A::B … end` — `base` is the namespace (`none` = absolute `::B`). -/
  | scopedClass (base : Option Expr) (name : String) (body : Expr)
  | scopedModule (base : Option Expr) (name : String) (body : Expr)
  | sclass (obj : Expr) (body : Expr)
  | defs (recv : Expr) (name : String) (params : List Param) (body : Expr)
  | begin' (body : Expr)
      (rescues : List (List Expr × Option (TargetKind × String) × Expr))
      (els : Option Expr) (ens : Option Expr)
  | super' (args : List Expr) (blk : Option Expr)
  | zsuper (blk : Option Expr)
  /-- `undef n₁, n₂, …`. -/
  | undef (names : List String)
  /-- `alias new old`. -/
  | alias' (newName oldName : String)
  /-- `defined?(e)` — a String naming what `e` is, or nil. The operand is *not*
      evaluated, except a send's receiver / a cpath's base. -/
  | defined (e : Expr)
  | seq (es : List Expr)

/-- Method/block/lambda formal parameters. Mutual with `Expr` because `popt`/`pkey`
carry default expressions. -/
inductive Param where
  /-- `a` (required; includes post-rest required params). -/
  | req (name : String)
  /-- `a = E` (optional; default evaluated lazily in the callee frame). -/
  | opt (name : String) (dflt : Expr)
  /-- `*a` / `*` (rest; `none` = anonymous). -/
  | rest (name : Option String)
  /-- `k:` (required keyword, `dflt = none`) / `k: E` (default). -/
  | key (name : String) (dflt : Option Expr)
  /-- `**o` / `**` (keyword-rest; `none` = anonymous). -/
  | kwrest (name : Option String)
  /-- `&b` / `&` (block capture; `none` = anonymous). -/
  | block (name : Option String)
  /-- `...` (argument forwarding). -/
  | fwd
  /-- `(a, b)` (destructuring; nests, may hold a rest). -/
  | destr (subs : List Param)

/-- One entry of a call-site `kwargs` marker: a `k: v` pair (static symbol key), a
`kExpr => v` pair whose key is an arbitrary expression, or a `**h` double-splat. -/
inductive KwEntry where
  | pair (key : String) (val : Expr)
  | dyn (key : Expr) (val : Expr)
  | splat (e : Expr)
end

deriving instance Repr for Expr, Param, KwEntry
deriving instance Inhabited for Expr, Param
/-! Structural equality on syntax. Originally added for certificate-claim lookup (a
claim was keyed on the subterm it was about); claims are gone (`AGENTS.md` §Claim-free),
but `==` is still what `Check13.lean` uses to pin each hand-written `Expr` to the
committed corpus JSON. `BEq`, not `DecidableEq`: `flt` carries a `Float`, which has no
`DecidableEq` — comparing two `NaN`-bit-pattern literals with `==` answers `false`, the
safe direction for a comparison that should refuse on a miss rather than assert a
spurious match. -/
deriving instance BEq for Expr, Param, KwEntry

namespace Decode

open Lean (Json)

abbrev M := Except String

def fail {α} (msg : String) (j : Json) : M α :=
  .error s!"{msg}: {j.compress.take 200}"

/-- A deliberate out-of-fragment gate at decode time, distinct from a genuine
malformation (`fail`). Nothing in this package currently produces `unsupported`, but
it's kept so a future extension (e.g. decoding a v4/v5 form this package doesn't yet
model) can gate honestly instead of hard-failing. -/
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

/-- A JSON array of plain strings (block-locals `|…; x, y|`, `undef` names). -/
def strList (j : Json) : M (List String) := do
  (← asArr j).toList.mapM asStr

mutual

partial def opt (j : Json) : M (Option Expr) :=
  match j with
  | .null => .ok none
  | _ => .some <$> expr j

/-- Optional name slot: a JSON string, or `null` (anonymous `*`/`**`/`&`). -/
partial def nameOpt (j : Json) : M (Option String) :=
  match j with
  | .null => .ok none
  | _ => .some <$> asStr j

/-- Decode one param node. Mutual with `expr` (`popt`/`pkey` carry default
expressions) and with `params` (`pdestr` nests). -/
partial def param (j : Json) : M Param := do
  let a ← asArr j
  let some hd := a[0]? | fail "empty param node" j
  let head ← asStr hd
  match head, a with
  | "preq",    #[_, n] => .req <$> asStr n
  | "popt",    #[_, n, d] => return .opt (← asStr n) (← expr d)
  | "prest",   #[_, n] => .rest <$> nameOpt n
  | "pkey",    #[_, n, d] => return .key (← asStr n) (← opt d)
  | "pkwrest", #[_, n] => .kwrest <$> nameOpt n
  | "pblock",  #[_, n] => .block <$> nameOpt n
  | "pfwd",    #[_] => return .fwd
  | "pdestr",  #[_, subs] => .destr <$> params subs
  | _, _ => fail s!"unknown or malformed param head :{head}" j

partial def params (j : Json) : M (List Param) := do
  (← asArr j).toList.mapM param

/-- One call-site keyword entry: `[[sym, k], v]` (static-symbol key), `["kwsplat", e]`,
or `[kExpr, v]` for a brace-less pair whose key is an arbitrary expression. -/
partial def kwEntry (j : Json) : M KwEntry := do
  match ← asArr j with
  | #[a, b] =>
    match a with
    | .str "kwsplat" => .splat <$> expr b
    | _ =>
      match ← asArr a with
      | #[hd, nm] =>
        match ← asStr hd with
        | "sym" => return .pair (← asStr nm) (← expr b)
        | _ => return .dyn (← expr a) (← expr b)
      | _ => return .dyn (← expr a) (← expr b)
  | _ => fail "kwargs entry" j

partial def exprs (js : Array Json) : M (List Expr) :=
  js.toList.mapM expr

partial def pair (j : Json) : M (Expr × Expr) := do
  match ← asArr j with
  | #[k, v] => return (← expr k, ← expr v)
  | _ => fail "hash pair" j

/-- Decode a `["cpath", base_or_null, name]` node into `(base?, name)` (used both as an
expression and as a scoped class/module definition name). -/
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
  | "flt",   #[_, x] => (fun f => Expr.flt f.toBits) <$> asFloat x
  | "regexp_lit", #[_, s, o] => return .regexpLit (← asStr s) (← asInt o).toNat
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
  | "vcall", #[_, m] => return .vcall (← asStr m)
  | "kwargs", #[_, entries] =>
      .kwargs <$> (← asArr entries).toList.mapM kwEntry
  | "fwd",   #[_] => return .fwd
  -- v5: a fourth slot before the body carries parse-time block-local names; merged
  -- with the explicit `|params; locals|` list (the block frame binds both the same
  -- way). The v4 four-slot shape still decodes.
  | "block", #[_, ps, ls, ds, body] =>
      return .block (← params ps) ((← strList ls) ++ (← strList ds)) (← expr body)
  | "block", #[_, ps, ls, body] =>
      return .block (← params ps) (← strList ls) (← expr body)
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
  | "redo",  #[_] => return .redo'
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
  | "defined", #[_, e] => .defined <$> expr e
  | _, _ => fail s!"unknown or malformed head :{head}" j

end

/-- Decode the full export document `{ "v": 4|5, "ast": ... }`. -/
def program (j : Json) : M Expr := do
  let v := (j.getObjVal? "v").toOption
  unless v == some (.num 5) || v == some (.num 4) do
    .error s!"unsupported rubycore export version: {v.map (·.compress)}"
  match j.getObjVal? "ast" with
  | .ok ast => expr ast
  | .error e => .error s!"missing ast: {e}"

end Decode

end Ratchet
