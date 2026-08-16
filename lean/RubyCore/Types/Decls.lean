import RubyCore.Types.Ty

/-!
# F1a — the static declaration table

`homebrew/typing-a-mutable-method-table.md` §8 F1a, `PLAN.md` D10. The table the
refinement invariant is *relative to*: a static, per-class map from a method name
to its declared signature, computed from the program and never from the heap.

## Why a table at all, when `builtinSig` was a function

`builtinSig : Ty → String → Option (List Ty × Ty)` was keyed on the receiver's
static **type**, which is enough while `Ty` and the dispatch class are in
bijection (`Types/Core.lean` says so in as many words) and stops being enough the
moment a user class has a type. More to the point, D10 changed what the invariant
*says*: not "the method table matches the declarations" but "every method the
declarations name resolves to something conforming to its declared signature".
That sentence quantifies over a table of declarations, so the table has to be an
artifact rather than a function definition — something a step can be shown to
preserve, and something an assumption can be *listed in* (D8: an assumption must
be an artifact, not a residue).

## Keyed on the class name, and why the key is the fragile part

`infer` cannot name an `ObjId` — `check` is a pure function of the program, and
object identities exist only in a heap. So declarations hang off the class
**name**, and the invariant's job is to tie that name to the heap's `ancestors`
(`Proof/Static/Decls.lean`). That is also why `Module#set_temporary_name` and
anonymous-class renaming are outside the D10 fragment: they change the key, not
the table (`typing-a-mutable-method-table.md` §5).

## What is in the table today

`baseDecls` — the three `Integer` builtins P0 tabulated, restated as
declarations. Nothing else: no program construct declares a signature yet, since
`sig` is not in `infer`'s domain. `declsOf` is nevertheless a function of the
program, so that when F1b reads a program's own `sig`s the *shape* of `check`
does not change.
-/

namespace RubyCore.Types

/-- A declared signature: parameter types and return type. The receiver's type is
    the key's class, not a field. -/
structure MethodDecl where
  params : List Ty
  ret : Ty
deriving DecidableEq, Repr, Inhabited

/-- The static declaration table: class name → method name → declared signature.

    An association list rather than a `HashMap` for the same reason `Env` is one:
    the proofs case on it, and `List.find?` has equation lemmas that reduce. -/
abbrev Decls := List (String × List (String × MethodDecl))

/-- The declarations of one class, by name. -/
def declsFor (D : Decls) (cls : String) : List (String × MethodDecl) :=
  match D.find? (·.1 == cls) with
  | some (_, ms) => ms
  | none => []

/-- The declared signature of `cls#name`, or `none` for "not declared", which the
    checker reads as `unknown` — never as "no such method". The distinction is
    load-bearing: the invariant is a *lower bound*, so silence about a name is
    silence, not a claim (`typing-a-mutable-method-table.md` §2). -/
def declOf? (D : Decls) (cls name : String) : Option MethodDecl :=
  (declsFor D cls |>.find? (·.1 == name)).map (·.2)

/-- Is `name` declared on **any** class? The side condition a `def` has to pass:
    installing a name the declarations do not mention is an addition, and
    additions are free; installing one they do mention is a redefinition, which
    F1c is where the conformance check lands. Until then a `def` of a declared
    name is `unknown`.

    With `baseDecls` this is exactly P0's `name ≠ "+" ∧ name ≠ "-" ∧ name ≠ "*"`,
    which is why F1a changes no verdict. -/
def declaresName (D : Decls) (name : String) : Bool :=
  D.any fun cd => cd.2.any fun md => md.1 == name

/-- The classes a value of a ground type can have. A **list**, not a single name,
    because `Ty.bool` is already two classes — which is the shape `T::Boolean`
    (`PLAN.md` W5 T4) needs, arriving here for free rather than as a union in
    `Ty`. -/
def tyClassNames : Ty → List String
  | .int => ["Integer"]
  | .bool => ["TrueClass", "FalseClass"]
  | .nilT => ["NilClass"]
  | .sym => ["Symbol"]

/-- The declared signature of `mname` for a receiver of static type `τ`: `some d`
    only when **every** class such a receiver can have declares it identically.

    Requiring agreement rather than picking the first is what makes the two-class
    types honest: a `T::Boolean` receiver may be either class at runtime, so a
    declaration that holds on only one of them supports no call site. -/
def declFor (D : Decls) (τ : Ty) (mname : String) : Option MethodDecl :=
  match tyClassNames τ with
  | [] => none
  | c :: cs =>
    match declOf? D c mname with
    | none => none
    | some d => if cs.all (fun c' => declOf? D c' mname == some d) then some d else none

/-- The signature in the `(params, ret)` shape `infer` and `KontOk` read. This is
    the direct replacement for P0's `builtinSig`, and the only difference visible
    to the type rules is that it takes the table. -/
def sigOf (D : Decls) (τ : Ty) (mname : String) : Option (List Ty × Ty) :=
  (declFor D τ mname).map fun d => (d.params, d.ret)

/-! ## The base table

`static-soundness-poc.md` §5's builtin signatures, as declarations. Every entry
is a **proof obligation** — `Proof/Static/Decls.lean`'s `DeclsOk` is what the
invariant carries, and `tableOk_declsOk` is the proof for these three. Entries
whose conformance is not proved may not appear; the notable absences and their
reasons are unchanged from P0 (`/` and `%` raise `ZeroDivisionError`, `**` makes
a Rational, and the `Float` promotions would need the argument type unpinned).
-/

def baseDecls : Decls :=
  [("Integer",
    [("+", { params := [.int], ret := .int }),
     ("-", { params := [.int], ret := .int }),
     ("*", { params := [.int], ret := .int })])]

/-- The declarations in force while checking `p`.

    A function of the program, and constant today: no construct in `infer`'s
    domain declares a signature, so the program contributes nothing. F1b's `def`
    and W8's `sig`s are what make it non-constant, and threading it now is what
    keeps that change local — the same argument L137 makes for heap-indexing a
    judgement whose arms do not yet read the heap. -/
def declsOf (_p : Expr) : Decls := baseDecls

/-- P0's table, recovered. Kept as a checked fact rather than a comment so that
    "F1a accepts no new programs" has a witness in the build. -/
example : sigOf baseDecls .int "+" = some ([Ty.int], Ty.int) := by
  simp [sigOf, declFor, declOf?, declsFor, baseDecls, tyClassNames]

example : sigOf baseDecls .int "/" = none := by
  simp [sigOf, declFor, declOf?, declsFor, baseDecls, tyClassNames]

/-- Nothing is declared on the two-class type, and `declFor` says so by
    *agreement* failing rather than by the type being absent — the case that
    matters once anything is declared on one of `TrueClass`/`FalseClass`. -/
example : sigOf baseDecls .bool "+" = none := by
  simp [sigOf, declFor, declOf?, declsFor, baseDecls, tyClassNames]

/-- The `def` side condition agrees with P0's three-name exclusion. -/
example : declaresName baseDecls "+" = true := by
  simp [declaresName, baseDecls]

example : declaresName baseDecls "f" = false := by
  simp [declaresName, baseDecls]

end RubyCore.Types
