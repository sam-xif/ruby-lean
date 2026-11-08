/-
The **Sorbet fragment**: which programs a soundness theorem can be about.

Sorbet is unsound by design, so "Sorbet is sound" is false and there is nothing
to prove. What *is* provable is a statement about a subset, and this file
defines that subset — syntactically, executably, and with a reason attached to
every exclusion, so the scope of any later theorem is a checkable artifact
rather than a paragraph of prose.

Two criteria carve it out. Both are principled; neither is "whatever we happen
to model" (that is the separate, already-existing `.unsupported` gate).

**(1) Every static-unsound construct must be runtime-checked.** This is
`../../AGENTS.md` §Sorbet §A.3 read as a specification:
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

**(3) The method table may grow, but not shrink** — `PLAN.md` **D10**. This
criterion *replaces* an earlier one that excluded the whole reflective family
(`define_method`, `alias_method`, `send`, `instance_variable_*`, …) on the
grounds that it makes the method table stop being described by the
declarations. That exclusion was correct about equality and wrong about what a
soundness statement needs, and it ruled out **every `sig` in the corpus**:
`sorbet-runtime` enforces a `sig` by *replacing* the method-table entry with a
validating wrapper — `alias_method` the original aside, `define_method` a
closure over the displaced entry, two `instance_variable_get`/`set` for the
pending sig — so a fragment that excluded those four could not type a single
annotated method. `prelude/prelude.rb`'s `T.__wrap` says so in as many words:
*"This IS the heap mutation of §C.2 — a method-table entry replaced by a
checking one."*

The invariant is therefore a **refinement** of the declarations rather than an
equality — *every method the declarations name resolves to something conforming
to its declared signature* — which is monotone in the table, because a
type-stuck outcome comes from a method being **missing** or **wrong-typed**,
never from one being present and unmentioned. So:

  - **addition is admitted unconditionally** — `def`, `define_method`,
    `attr_*`, `include`, a fresh `alias`/`alias_method`;
  - **a redefinition is admitted except for the one case this file can decide
    syntactically**: a `define_method`/`define_singleton_method` whose literal
    target already carries a `sig` in the same scope is refused, because nothing
    else checks that the displaced declaration is still conformed to. A
    redefinition through a computed name, or through `alias`/`alias_method`,
    remains admitted: its conformance is a question about types, not syntax;
  - **removal is the exclusion** — `undef`, `undef_method`, `remove_method`;
  - **renaming a class is excluded separately**, because it breaks the *key*
    declarations hang off rather than the table (`set_temporary_name`,
    `const_set`);
  - **dynamic dispatch and ivar access are excluded for their own reasons** —
    an unknown call target, and state outside the declared types — not as
    table escapes, which is what the old single "reflective" charge said.

Details, including the measurement on the Homebrew slice (three conforming
`alias`es, one `instance_variable_set`, **zero** removals) and the polarity
asymmetry of `respond_to?`: `homebrew/typing-a-mutable-method-table.md`.

**Two known gaps in criterion 3, named rather than hidden.** Renaming is caught
only at the two *named* operations: `K = Class.new` reaches the same hazard
through a plain constant assignment, and deciding that syntactically would mean
knowing the assigned value is an anonymous class. And a class that defines
`method_missing` is still admitted — a `method_missing`-served call cannot make
a conforming call fail to conform, it only makes the *result* untyped, so the
scheduling question (admit now, or exclude until occurrence typing can consume
an untyped value) is deliberately left open. Both are F1a's problem, not this
file's.

What this file is NOT: a claim that in-fragment programs are safe. It is the
*hypothesis* of that claim. The theorem is separate work; this is its scope —
and note that no theorem in `books/Books/Metatheory/` quantifies over it today, so relaxing it
here cannot break one. `books/Books/Metatheory/StaticSoundness.lean` plays the fragment role
with `CtlOk`/`KontOk` instead.
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
  | "table-removal" =>
    "removes a method, so a declared name may stop resolving (criterion 3)"
  | "key" =>
    "renames a class, changing the key its declarations hang off (criterion 3)"
  | "redefinition" =>
    "displaces a sig-annotated method without checking the replacement conforms (criterion 3)"
  | "dynamic" =>
    "the call target is not statically known, so its result is untyped (criterion 2)"
  | "state" =>
    "writes or reads state outside the declared types (criterion 2)"
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

/-- The method names a `sig` in the current scope declares. `scan` extends this
    as it walks a statement list and starts it afresh inside a class or module
    body, so a literal `define_method` can be matched against the declaration it
    would displace without guessing across scopes. -/
structure Scope where
  instanceNames : List String := []
  singletonNames : List String := []
deriving Repr, Inhabited

def emptyScope : Scope := {}

/-- The name a `define_method`-style call installs, when its argument is a
    literal symbol or string. A computed name cannot be matched syntactically,
    so it stays admitted. -/
def literalMethodName? : List Expr → Option String
  | [.sym s] => some s
  | [.str s] => some s
  | _ => none

/-- **Admitted** (D10): these install a method and cannot remove one. Where the
    installed name already has a declaration the step is a *redefinition*.
    `scan` refuses the one redefinition it can see syntactically: a
    `define_method`/`define_singleton_method` whose literal target already has
    a `sig` in the same scope (`redefinition`). A computed target, and
    `alias_method`/`prepend`, are still admitted: their conformance is a
    question about types, not syntax. The sig wrapper lives in the prelude, not
    in the scanned program, so refusing an explicit displacing `define_method`
    does not refuse an annotated method's own wrapper.

    `prepend` is in this list for the same reason with the opposite default: it
    splices *above* the owner and therefore always displaces, so it is admitted
    only in the conditional sense. It appears nowhere in the Homebrew slice. -/
def deferredSend : List String :=
  ["define_method", "define_singleton_method", "alias_method", "prepend"]

/-- Removal: the D10 exclusion. A declared name can stop resolving, which is a
    type-stuck outcome the declarations cannot see coming. `undef` is a head, not
    a send, and is handled in the main scan. -/
def removalSend : List String := ["remove_method", "undef_method"]

/-- Renaming a class changes the **key** its declarations hang off rather than
    the table, and the checker cannot name an `ObjId`. Incomplete by
    construction — see the header's note on `K = Class.new`. -/
def keySend : List String := ["set_temporary_name", "const_set"]

/-- Dynamic dispatch: the target is a value, so the checker cannot say which
    declaration the call is against. Excluded for the *result* type, not as a
    table escape. -/
def dynamicSend : List String :=
  ["send", "public_send", "__send__", "class_eval", "module_eval",
   "instance_eval", "instance_exec", "method_missing", "respond_to_missing?"]

/-- Instance-variable access installs and removes nothing; what it does is read
    or write state the declarations do not cover. `version.rb:783`'s `NULL`
    sentinel is the slice's one occurrence and is genuinely untypable until W8
    gives `@version` a nilable declaration
. -/
def stateSend : List String := ["instance_variable_set", "instance_variable_get"]

-- The classification is a partition, and `deferredSend` is the one list `scan`
-- does *not* consult — so this is what keeps it from being a comment. A name
-- admitted by D10 must not appear in an excluded list; checked at elaboration,
-- so the two cannot drift apart silently.
#guard deferredSend.all fun m =>
  !(removalSend.contains m || keySend.contains m
      || dynamicSend.contains m || stateSend.contains m)

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

/-- The `sig`-annotated definition a statement adds to its scope, if any:
    `(singleton?, name)`. A visibility modifier (`private def f`) counts as its
    argument, since the two form one statement. -/
private def declaredDef? : Expr → Option (Bool × String)
  | .def' name _ _ => some (false, name)
  | .defs _ name _ _ => some (true, name)
  | .send none m [.def' name _ _] _ =>
    if visibilityMod.contains m then some (false, name) else none
  | .send none m [.defs _ name _ _] _ =>
    if visibilityMod.contains m then some (true, name) else none
  | _ => none

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

    `scope` is the set of `sig`-annotated names declared so far in the current
    class or module body; `scanStmts` extends it as annotated definitions go by,
    so a literal `define_method` can be matched against the declaration it would
    displace. `sigPrecedes` is the one other piece of context a single
    expression cannot supply: whether the statement immediately before this one
    was a `sig { … }`. Both are threaded through the same function rather than
    split into a second traversal so that every recursive call lands on a
    strictly smaller expression (the alternative shape needs a same-size hop,
    which has no termination measure). -/
def scan (scope : Scope) (sigPrecedes : Bool) : Expr → List Violation
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
      else if removalSend.contains m then
        [{ kind := "table-removal", what := m }]
      else if keySend.contains m then
        [{ kind := "key", what := m }]
      else if let some name := (if m == "define_method" then literalMethodName? args else none) then
        if scope.instanceNames.contains name then
          [{ kind := "redefinition", what := "define_method :" ++ name }]
        else []
      else if let some name :=
          (if m == "define_singleton_method" then literalMethodName? args else none) then
        if scope.singletonNames.contains name then
          [{ kind := "redefinition", what := "define_singleton_method :" ++ name }]
        else []
      else if dynamicSend.contains m then
        [{ kind := "dynamic", what := m }]
      else if stateSend.contains m then
        [{ kind := "state", what := m }]
      else if recv.isNone && attrNames.contains m && !sigPrecedes then
        attrViolations m args
      else []
    -- A visibility modifier passes `sigPrecedes` through to its argument; every
    -- other send scans arguments with `false`.
    let argVs :=
      if recv.isNone && visibilityMod.contains m then scanListSig scope sigPrecedes args
      else scanList scope args
    here ++ scanOpt scope recv ++ argVs ++ scanOpt scope blk
  | .vcall m =>
    if removalSend.contains m then [{ kind := "table-removal", what := m }]
    else if keySend.contains m then [{ kind := "key", what := m }]
    else if dynamicSend.contains m then [{ kind := "dynamic", what := m }]
    else if stateSend.contains m then [{ kind := "state", what := m }]
    else []
  | .cpath base name =>
    let here : List Violation :=
      match base with
      | some (.const "T") =>
        if name == "Struct" || name == "Enum" then
          [{ kind := "unchecked", what := "T::" ++ name }]
        else []
      | _ => []
    here ++ scanOpt scope base
  | .cpathAsgn base _ e => scanOpt scope base ++ scan scope false e
  | .def' name params body =>
    (if sigPrecedes then [] else [missingSig name])
      ++ scanParams scope params ++ scan scope false body
  | .defs recv name params body =>
    (if sigPrecedes then [] else [missingSig ("self." ++ name)])
      ++ scan scope false recv ++ scanParams scope params ++ scan scope false body
  -- A class or module body is a fresh declaration scope.
  | .class' _ sup body => scanOpt scope sup ++ scan emptyScope false body
  | .module' _ body => scan emptyScope false body
  | .scopedClass base _ body => scanOpt scope base ++ scan emptyScope false body
  | .scopedModule base _ body => scanOpt scope base ++ scan emptyScope false body
  | .sclass obj body => scan scope false obj ++ scan emptyScope false body
  | .seq es => scanStmts scope es false
  -- `alias` adds when `newN` is fresh and redefines when it is not, and which of
  -- those it is depends on the heap rather than on this expression. Admitted
  -- either way (D10): the slice's three `alias eql? ==` are conforming
  -- redefinitions.
  | .alias' _ _ => []
  | .undef names => names.map fun n => { kind := "table-removal", what := "undef " ++ n }
  | .vasgn _ _ e => scan scope false e
  | .casgn _ e => scan scope false e
  | .if' c t e => scan scope false c ++ scan scope false t ++ scanOpt scope e
  | .while' c body => scan scope false c ++ scan scope false body
  | .dowhile body c => scan scope false body ++ scan scope false c
  | .for' _ coll body _ => scan scope false coll ++ scan scope false body
  | .block params _ body => scanParams scope params ++ scan scope false body
  | .yield' args => scanList scope args
  | .blockpass e => scanOpt scope e
  | .array elems => scanList scope elems
  | .hash pairs => scanPairs scope pairs
  | .splat e => scanOpt scope e
  | .ret e => scanOpt scope e
  | .brk e => scanOpt scope e
  | .nxt e => scanOpt scope e
  | .begin' body rescues els ens =>
    scan scope false body ++ scanRescues scope rescues ++ scanOpt scope els
      ++ scanOpt scope ens
  | .super' args blk => scanList scope args ++ scanOpt scope blk
  | .zsuper blk => scanOpt scope blk
  | .defined e => scan scope false e
  | .kwargs entries => scanKw scope entries
  | _ => []

/-- Statement-list scan: this is where "every method carries a sig" lives,
    because it is a property of a *sequence*. It also extends the scope with
    each `sig`-annotated definition as it goes, so a later redefinition can be
    matched against the declaration it displaces. -/
def scanStmts (scope : Scope) : List Expr → Bool → List Violation
  | [], _ => []
  | e :: rest, sigPrecedes =>
    let scope' :=
      if sigPrecedes then
        match declaredDef? e with
        | some (true, name) => { scope with singletonNames := name :: scope.singletonNames }
        | some (false, name) => { scope with instanceNames := name :: scope.instanceNames }
        | none => scope
      else scope
    scan scope sigPrecedes e ++ scanStmts scope' rest (sigHeader? e)

def scanOpt (scope : Scope) : Option Expr → List Violation
  | none => []
  | some e => scan scope false e

def scanList (scope : Scope) : List Expr → List Violation
  | [] => []
  | e :: rest => scan scope false e ++ scanList scope rest

/-- `scanList` with the statement's `sigPrecedes` threaded into each argument —
    used only for a visibility modifier wrapping a `def`. -/
def scanListSig (scope : Scope) (sigPrecedes : Bool) : List Expr → List Violation
  | [] => []
  | e :: rest => scan scope sigPrecedes e ++ scanListSig scope sigPrecedes rest

def scanPairs (scope : Scope) : List (Expr × Expr) → List Violation
  | [] => []
  | (k, v) :: rest => scan scope false k ++ scan scope false v ++ scanPairs scope rest

def scanKw (scope : Scope) : List KwEntry → List Violation
  | [] => []
  | .pair _ v :: rest => scan scope false v ++ scanKw scope rest
  | .dyn k v :: rest => scan scope false k ++ scan scope false v ++ scanKw scope rest
  | .splat e :: rest => scan scope false e ++ scanKw scope rest

def scanRescues (scope : Scope) :
    List (List Expr × Option (TargetKind × String) × Expr) → List Violation
  | [] => []
  | (classes, _, body) :: rest =>
    scanList scope classes ++ scan scope false body ++ scanRescues scope rest

def scanParams (scope : Scope) : List Param → List Violation
  | [] => []
  | p :: rest => scanParam scope p ++ scanParams scope rest

def scanParam (scope : Scope) : Param → List Violation
  | .opt _ d => scan scope false d
  | .key _ (some d) => scan scope false d
  | .destr subs => scanParams scope subs
  | _ => []

end

/-- The fragment predicate. Decidable and executable on purpose: it is the
    hypothesis of a theorem *and* a tool that can be run over a corpus. -/
def inSorbetFragment (e : Expr) : Bool := (scan emptyScope false e).isEmpty

/-- Violations with duplicates collapsed — the report wants "this program uses
    `T.unsafe`", not one line per occurrence. -/
def violationSummary (e : Expr) : List Violation :=
  (scan emptyScope false e).foldl (fun acc v => if acc.contains v then acc else acc ++ [v]) []

end Types
end RubyCore
