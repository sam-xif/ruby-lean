/-
The **Sorbet fragment**: which programs a soundness theorem can be about.

Sorbet is unsound by design, so "Sorbet is sound" is false and there is nothing
to prove. What *is* provable is a statement about a subset, and this file
defines that subset — syntactically, executably, and with a reason attached to
every exclusion, so the scope of any later theorem is a checkable artifact
rather than a paragraph of prose.

Two criteria carve it out. Both are principled; neither is "whatever we happen
to model" (that is the separate, already-existing `.unsupported` gate).

**(1) Every static-unsound construct must be runtime-checked.** This is §A.3 of
`../../docs/semantics/types-and-preservation.md` read as a specification:
"`T.unsafe` is the one form with no runtime check; everything else that is
static-unsound is at least runtime-checked." So `T.cast`/`T.let`/`T.must`/
`T.bind`/`T.assert_type!` are all **admitted** — they are trusted statically but
enforced dynamically, and a *runtime* soundness statement is happy with that.
Excluded are exactly the constructs with no runtime backstop:

  - `T.unsafe`                — checks nothing, by definition
  - `.checked(:never|:tests)` — removes the wrapper the sig would install
  - `T::Struct` / `T::Enum`   — getters are plain attr_readers, unchecked (§A.1)
  - `T::Array[X]` and friends — type *arguments* are erased at runtime (§A.6)

**(2) No untyped code.** The `# typed: strong` discipline: every method carries
a `sig`, and no `T.untyped` appears. Not because untyped code is *unsound* — an
untyped parameter makes no claim, so nothing can violate it — but because it
makes the interesting claim vacuous. `corpus/sorbet/untyped-boundary/000.rb` is
the demonstration: a program with no sigs at all, accepted by `srb`, reaching an
uncaught `NoMethodError`. A theorem that admitted it would say nothing.

Also excluded, under (2) in spirit: the reflective definition family
(`define_method`, `*_eval`, `alias_method`, `send`, `method_missing`, …). These
install or dispatch methods outside the sig discipline, so the method table
stops being described by the declarations — the "type `escape`" of §C.2.

What this file is NOT: a claim that in-fragment programs are safe. It is the
*hypothesis* of that claim. The theorem is separate work; this is its scope.
-/
import RubyCore.Syntax

namespace RubyCore
namespace Types

/-- Why a program is outside the fragment. `kind` groups the report; `what`
    names the offending construct. -/
structure Violation where
  kind : String
  what : String
deriving Repr, DecidableEq, Inhabited

namespace Violation

/-- One line of explanation per kind — the report is meant to be readable by
    someone who has not read this file. -/
def reason (v : Violation) : String :=
  match v.kind with
  | "unchecked" =>
    "static-unsound with no runtime check (criterion 1)"
  | "untyped" =>
    "untyped code: the claim would be vacuous (criterion 2)"
  | "reflective" =>
    "installs or dispatches methods outside the sig discipline (§C.2 type escape)"
  | "missing-sig" =>
    "method has no sig, so its parameters and return are T.untyped (§A.5)"
  | _ => "unclassified"

end Violation

/-- `T.foo(…)` — a send whose receiver is the bare constant `T`. -/
def tSend? (recv : Option Expr) : Bool :=
  match recv with
  | some (.const "T") => true
  | _ => false

/-- `T::Foo` — a constant path rooted at `T`. -/
def tConst? (e : Expr) : Option String :=
  match e with
  | .cpath (some (.const "T")) name => some name
  | _ => none

/-- The `sig { … }` header: an implicit-self send named `sig` carrying a block.
    `sig` chained with `.checked(…)` etc. still has `sig` at the bottom of the
    receiver chain, so this walks down. -/
def sigHeader? : Expr → Bool
  | .send none "sig" _ (some (.block _ _ _)) => true
  | .send (some recv) _ _ _ => sigHeader? recv
  | _ => false

/-- Reflective definition/dispatch: the family that makes the method table stop
    matching the declarations. `alias`/`undef` are heads, not sends, and are
    handled in the main scan. -/
def reflectiveSend : List String :=
  ["define_method", "define_singleton_method", "class_eval", "module_eval",
   "instance_eval", "instance_exec", "alias_method", "send", "public_send",
   "__send__", "method_missing", "respond_to_missing?", "instance_variable_set",
   "instance_variable_get", "const_set", "remove_method", "prepend"]

/-- The visibility modifiers that take a `def` as their **argument**.

    `private def m` and `private_class_method def self.m` are single statements, so
    a `sig { … }` above one precedes the `def` inside it — but the `def` reaches
    `scan` as a send *argument*, and arguments are scanned with
    `sigPrecedes := false`. That reported `missing-sig` for six methods on the
    Homebrew slice (`vulns/semver.rb` and `vulns/cvss.rb`, three each) that are
    fully annotated upstream, which made the report wrong rather than merely
    incomplete. L138. -/
def visibilityMod : List String :=
  ["private", "public", "protected", "private_class_method", "public_class_method",
   "module_function"]

/-- The checked-level arguments that *remove* the runtime wrapper. `:always` is
    the default and is fine. -/
def uncheckedLevels : List String := ["never", "tests"]

private def levelArg? (args : List Expr) : Option String :=
  match args with
  | [.sym s] => if uncheckedLevels.contains s then some s else none
  | _ => none

/-- Reported for a `def` with no preceding `sig`. -/
private def missingSig (what : String) : Violation :=
  { kind := "missing-sig", what := what }

/-- `attr_*` generates methods, so in `# typed: strict` it needs a sig above it
    exactly like a `def`. -/
private def attrNames : List String := ["attr_accessor", "attr_reader", "attr_writer"]

private def attrViolations (m : String) (args : List Expr) : List Violation :=
  args.map fun a =>
    match a with
    | .sym s => missingSig (m ++ " :" ++ s)
    | _ => missingSig m

mutual

/-- Every reason `e` falls outside the fragment (empty = in-fragment). A list
    rather than a Bool: "why not" is the useful output, and it is what makes the
    corpus report actionable.

    `sigPrecedes` is the one piece of context a single expression cannot supply:
    whether the statement immediately before this one was a `sig { … }`. It is
    threaded through the same function rather than split into a second traversal
    so that every recursive call lands on a strictly smaller expression (the
    alternative shape needs a same-size hop, which has no termination measure). -/
def scan (sigPrecedes : Bool) : Expr → List Violation
  | .send recv m args blk =>
    let here : List Violation :=
      if tSend? recv && m == "unsafe" then
        [{ kind := "unchecked", what := "T.unsafe" }]
      else if tSend? recv && m == "untyped" then
        [{ kind := "untyped", what := "T.untyped" }]
      else if let some lvl := (if m == "checked" then levelArg? args else none) then
        [{ kind := "unchecked", what := "sig.checked(:" ++ lvl ++ ")" }]
      else if let some gen := (if m == "[]" then recv.bind tConst? else none) then
        -- `T::Array[Integer]`: the element type is erased at runtime (§A.6), so
        -- the annotation is a static-only claim with no backstop.
        [{ kind := "unchecked", what := "T::" ++ gen ++ "[…] (erased type argument)" }]
      else if reflectiveSend.contains m then
        [{ kind := "reflective", what := m }]
      else if recv.isNone && attrNames.contains m && !sigPrecedes then
        attrViolations m args
      else []
    -- A visibility modifier passes `sigPrecedes` through to its argument; every
    -- other send scans arguments with `false`.
    let argVs :=
      if recv.isNone && visibilityMod.contains m then scanListSig sigPrecedes args
      else scanList args
    here ++ scanOpt recv ++ argVs ++ scanOpt blk
  | .vcall m =>
    if reflectiveSend.contains m then [{ kind := "reflective", what := m }] else []
  | .cpath base name =>
    let here : List Violation :=
      match base with
      | some (.const "T") =>
        if name == "Struct" || name == "Enum" then
          [{ kind := "unchecked", what := "T::" ++ name }]
        else []
      | _ => []
    here ++ scanOpt base
  | .cpathAsgn base _ e => scanOpt base ++ scan false e
  | .def' name params body =>
    (if sigPrecedes then [] else [missingSig name]) ++ scanParams params ++ scan false body
  | .defs recv name params body =>
    (if sigPrecedes then [] else [missingSig ("self." ++ name)])
      ++ scan false recv ++ scanParams params ++ scan false body
  | .class' _ sup body => scanOpt sup ++ scan false body
  | .module' _ body => scan false body
  | .scopedClass base _ body => scanOpt base ++ scan false body
  | .scopedModule base _ body => scanOpt base ++ scan false body
  | .sclass obj body => scan false obj ++ scan false body
  | .seq es => scanStmts es false
  | .alias' newN oldN => [{ kind := "reflective", what := "alias " ++ newN ++ " " ++ oldN }]
  | .undef names => names.map fun n => { kind := "reflective", what := "undef " ++ n }
  | .vasgn _ _ e => scan false e
  | .casgn _ e => scan false e
  | .if' c t e => scan false c ++ scan false t ++ scanOpt e
  | .while' c body => scan false c ++ scan false body
  | .dowhile body c => scan false body ++ scan false c
  | .for' _ coll body => scan false coll ++ scan false body
  | .block params _ body => scanParams params ++ scan false body
  | .yield' args => scanList args
  | .blockpass e => scanOpt e
  | .array elems => scanList elems
  | .hash pairs => scanPairs pairs
  | .splat e => scanOpt e
  | .ret e => scanOpt e
  | .brk e => scanOpt e
  | .nxt e => scanOpt e
  | .begin' body rescues els ens =>
    scan false body ++ scanRescues rescues ++ scanOpt els ++ scanOpt ens
  | .super' args blk => scanList args ++ scanOpt blk
  | .zsuper blk => scanOpt blk
  | .defined e => scan false e
  | .kwargs entries => scanKw entries
  | _ => []

/-- Statement-list scan: this is where "every method carries a sig" lives,
    because it is a property of a *sequence*. -/
def scanStmts : List Expr → Bool → List Violation
  | [], _ => []
  | e :: rest, sigPrecedes => scan sigPrecedes e ++ scanStmts rest (sigHeader? e)

def scanOpt : Option Expr → List Violation
  | none => []
  | some e => scan false e

def scanList : List Expr → List Violation
  | [] => []
  | e :: rest => scan false e ++ scanList rest

/-- `scanList` with the statement's `sigPrecedes` threaded into each argument —
    used only for a visibility modifier wrapping a `def` (L138). -/
def scanListSig (sigPrecedes : Bool) : List Expr → List Violation
  | [] => []
  | e :: rest => scan sigPrecedes e ++ scanListSig sigPrecedes rest

def scanPairs : List (Expr × Expr) → List Violation
  | [] => []
  | (k, v) :: rest => scan false k ++ scan false v ++ scanPairs rest

def scanKw : List KwEntry → List Violation
  | [] => []
  | .pair _ v :: rest => scan false v ++ scanKw rest
  | .dyn k v :: rest => scan false k ++ scan false v ++ scanKw rest
  | .splat e :: rest => scan false e ++ scanKw rest

def scanRescues :
    List (List Expr × Option (TargetKind × String) × Expr) → List Violation
  | [] => []
  | (classes, _, body) :: rest => scanList classes ++ scan false body ++ scanRescues rest

def scanParams : List Param → List Violation
  | [] => []
  | p :: rest => scanParam p ++ scanParams rest

def scanParam : Param → List Violation
  | .opt _ d => scan false d
  | .key _ (some d) => scan false d
  | .destr subs => scanParams subs
  | _ => []

end

/-- The fragment predicate. Decidable and executable on purpose: it is the
    hypothesis of a theorem *and* a tool that can be run over a corpus. -/
def inSorbetFragment (e : Expr) : Bool := (scan false e).isEmpty

/-- Violations with duplicates collapsed — the report wants "this program uses
    `T.unsafe`", not one line per occurrence. -/
def violationSummary (e : Expr) : List Violation :=
  (scan false e).foldl (fun acc v => if acc.contains v then acc else acc ++ [v]) []

end Types
end RubyCore
