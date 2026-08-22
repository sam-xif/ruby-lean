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

mutual
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
  /-- A **vcall**: a bare identifier (`foo`) that is not a local variable — Prism's
      `variable_call` flag. Semantically an implicit-self, zero-arg, block-less send,
      and it is evaluated as exactly that; the reason it is a *separate* head is the
      dispatch-*miss* message, which CRuby distinguishes [V]:

        foo        (vcall)  → NameError:     undefined local variable or method 'foo'
        foo()      (fcall)  → NoMethodError: undefined method 'foo'
        self.foo / foo(1)   → NoMethodError: undefined method 'foo'

      RubyCore previously conflated the two (both exported as
      `["send",null,"foo",[],null]`), which forced `missNoMethod` to gate rather than
      answer. Keeping this additive — a new head rather than a field on `send` — means
      the v4 corpus and every existing `send` node are untouched. -/
  | vcall (m : String)
  /-- Brace-less keyword arguments at a call site (`f(k: 1, **h)`) — only occurs
      as the last element of a send/super `args` list (Ruby-3 separation). -/
  | kwargs (entries : List KwEntry)
  /-- `...` argument-forwarding marker at a call site (`g(...)`) — expands the
      enclosing `(...)`-method's captured positional/keyword/block args. -/
  | fwd
  /-- Only occurs as a send's `blk` child. `locals` are `|params; locals|`
      block-locals (fresh, shadowing outer names). -/
  | block (params : List Param) (locals : List String) (body : Expr)
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
  | def' (name : String) (params : List Param) (body : Expr)
  | array (elems : List Expr)
  | hash (pairs : List (Expr × Expr))
  /-- Only valid as a send-arg / array element. -/
  | splat (e : Option Expr)
  | ret (e : Option Expr)
  | brk (e : Option Expr)
  | nxt (e : Option Expr)
  | retry'
  /-- `redo` — restart the current loop iteration (artifact 04). -/
  | redo'
  | class' (name : String) (sup : Option Expr) (body : Expr)
  | module' (name : String) (body : Expr)
  /-- `class A::B … end` — `base` is the namespace (`none` = absolute `::B`).
      Scoped defs with an explicit superclass gate at decode (rare). -/
  | scopedClass (base : Option Expr) (name : String) (body : Expr)
  | scopedModule (base : Option Expr) (name : String) (body : Expr)
  | sclass (obj : Expr) (body : Expr)
  | defs (recv : Expr) (name : String) (params : List Param) (body : Expr)
  | begin' (body : Expr)
      (rescues : List (List Expr × Option (TargetKind × String) × Expr))
      (els : Option Expr) (ens : Option Expr)
  | super' (args : List Expr) (blk : Option Expr)
  | zsuper (blk : Option Expr)
  /-- `undef n₁, n₂, …` — remove methods from the current definee. -/
  | undef (names : List String)
  /-- `alias new old` — bind `new` to the current definition of `old`. -/
  | alias' (newName oldName : String)
  /-- `defined?(e)` — a String naming what `e` is, or nil (artifact 03 §6). The
      operand is *not* evaluated, except a send's receiver / a cpath's base. -/
  | defined (e : Expr)
  | seq (es : List Expr)

/-- Method/block/lambda formal parameters (rubycore.rb `PARAM_HEADS`; mutual
    with `Expr` because `popt`/`pkey` carry default expressions). -/
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

/-- One entry of a call-site `kwargs` marker: a `k: v` pair (static symbol key),
    a `kExpr => v` pair whose key is an arbitrary expression, or a `**h`
    double-splat. -/
inductive KwEntry where
  | pair (key : String) (val : Expr)
  | dyn (key : Expr) (val : Expr)
  | splat (e : Expr)
end

deriving instance Repr for Expr, Param, KwEntry
deriving instance Inhabited for Expr, Param

/-! ## The match-view global names

**Here, rather than in `Interp/Support.lean`, since L228.** They are pure string tests
on a *name*, and the type checker needs them for the same reason the interpreter does:
`Decls.globals` may only declare a global the machine actually stores in `m.globals`, and
`isMatchView` is the predicate that says which those are. `Types/` cannot import `Interp/`,
and a second copy of the test is exactly the drift `isMatchView`'s own docstring was
written to prevent — so the definition moves down to the layer both sides can see, keeping
its `Interp` namespace and every use site unchanged.
-/

namespace Interp

/-- `$1`…`$9`, `$&`, `` $` `` and `$'` are **views of `$~`**, not stored
    globals: CRuby derives them from the last `MatchData` on every read. Storing
    them instead would need every failed match to clear nine slots, and would
    still get `defined?($3)` wrong. Returns `none` for any other global name, so
    the ordinary path is untouched. (L101.) -/
def matchViewIdx? (x : String) : Option Nat :=
  if x.length == 2 then
    let c := x.get ⟨1⟩
    if c.isDigit && c != '0' then some (c.toNat - '0'.toNat)
    else if c == '&' then some 0
    else none
  else none

/-- Is `x` one of those views, rather than a stored global? **Purely syntactic** —
    the name decides, not the machine. Factored out and named so the metatheory's
    fragment predicate can exclude exactly these names and cannot drift from the
    rule `matchGlobal` implements: `Step.varGvar` said a gvar read is a plain
    `getGlobal`, which stopped being true when L101 put `matchGlobal` in front of
    it, and nothing noticed for 24 commits because `Proof/` is off the default
    build target (L119). -/
def isMatchView (x : String) : Bool :=
  (matchViewIdx? x).isSome || x == "$`" || x == "$'"

end Interp

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

/-- Decode one v4 param node (rubycore.rb `PARAM_HEADS`) into a `Param`.
    Mutual with `expr` (`popt`/`pkey` carry default expressions) and with
    `params` (`pdestr` nests). -/
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

/-- One call-site keyword entry: `[[sym, k], v]` (static-symbol key),
    `["kwsplat", e]`, or `[kExpr, v]` for a brace-less pair whose key is an
    arbitrary expression (`f("a" => 1)`, `delegate [:x] => :y`). -/
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
  | "vcall", #[_, m] => return .vcall (← asStr m)
  | "kwargs", #[_, entries] =>
      .kwargs <$> (← asArr entries).toList.mapM kwEntry
  | "fwd",   #[_] => return .fwd
  -- v5 (C35): a fourth slot before the body carries the names Ruby makes
  -- block-local *at parse time* — the ones whose first textual assignment is
  -- inside the block, which no runtime lookup can recover. They are merged with
  -- the explicit `|params; locals|` list because the block frame binds both the
  -- same way; the two differ only for `defined?`, and `defined?` is decided here
  -- from the *node shape* (a name the parser did not know is a vcall, not a
  -- `var local` — L72), never from what the frame binds. The v4 four-slot shape
  -- still decodes, so an AST exported before this change is not rejected.
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
  -- v4 additive heads not yet modeled by the stepper: gate as Unsupported
  -- (exit 3) rather than a hard decode failure. Some appear as arg markers
  -- (`kwargs`/`fwd`), the rest as statements.
  | _, _ => fail s!"unknown or malformed head :{head}" j

end

/-- Decode the full export document `{ "v": 5, "ast": ... }` (export.rb v5:
    structured param nodes, additive heads, and `block`'s parse-time `declared`
    slot; see `param` and the `unsupported` gates for the forms the Phase-0
    stepper does not model yet). v4 documents decode unchanged — the only
    difference is `block`'s arity, and both shapes are accepted. -/
def program (j : Json) : M Expr := do
  let v := (j.getObjVal? "v").toOption
  unless v == some (.num 5) || v == some (.num 4) do
    .error s!"unsupported rubycore export version: {v.map (·.compress)}"
  match j.getObjVal? "ast" with
  | .ok ast => expr ast
  | .error e => .error s!"missing ast: {e}"

end Decode

end RubyCore
