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

/-- The static declaration table.

    **A structure with two fields since L176**, where it was an association list
    of method rows. The second field is the **constant** table, and it is here
    rather than in a table of its own for one reason: L160 made the declarations a
    *threaded* judgement — `infer` returns one, `KontOk` carries it as an index,
    `Inv` quantifies it existentially — and a constant assignment needs exactly
    that same threading, for exactly the same reason (`initiation` obliges the
    invariant at the **boot** heap, so a constant the program's own `casgn`
    creates cannot be in a table fixed up front). Putting it in the value that is
    already threaded costs **no new index anywhere**; a parallel table would cost
    one in `infer`'s answer, in three `KontOk` constructors, in `Inv`, in `CtlOk`
    and in every consecution case.

    `rows` is still an association list rather than a `HashMap` for the same
    reason `Env` is one: the proofs case on it, and `List.find?` has equation
    lemmas that reduce. -/
structure Decls where
  /-- class name → method name → declared signature. -/
  rows : List (String × List (String × MethodDecl)) := []
  /-- constant name → the type of its value. **Empty until a rule populates it**;
      L176 is the threading and nothing reads this field yet. -/
  consts : List (String × Ty) := []
deriving DecidableEq, Repr, Inhabited

/-- The declarations of one class, by name. -/
def declsFor (D : Decls) (cls : String) : List (String × MethodDecl) :=
  match D.rows.find? (·.1 == cls) with
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
  D.rows.any fun cd => cd.2.any fun md => md.1 == name

/-- The class names the four *ground* arms of `Ty` already denote. Subtracted from
    the class arm's key set by `tyClassNames`; see the note there. -/
def groundClassNames : List String :=
  ["Integer", "TrueClass", "FalseClass", "NilClass", "Symbol"]

/-- The classes a value of a ground type can have. A **list**, not a single name,
    because `Ty.bool` is already two classes — which is the shape `T::Boolean`
    (`PLAN.md` W5 T4) needs, arriving here for free rather than as a union in
    `Ty`. -/
def tyClassNames : Ty → List String
  | .int => ["Integer"]
  | .bool => ["TrueClass", "FalseClass"]
  | .nilT => ["NilClass"]
  | .sym => ["Symbol"]
  -- The class type is the arm this function was written for: one name, exactly
  -- the key. Note it is *not* the ancestors walk — a declaration inherited from a
  -- superclass is not visible here, which is `Sub`'s job (`PLAN.md` W5 T2) and is
  -- deliberately still absent, so today a class type sees only its own row.
  --
  -- **The ground names are subtracted, and that is not a technicality.** The two
  -- kinds of arm have *disjoint* inhabitants — `valueTy?` gives an immediate a
  -- ground type and a `.ref` a class type, never both — so if `.cls "Integer"`
  -- read `Integer`'s row, the invariant would owe an `EntryOk` for that row over
  -- receivers the row was never about: objects of some class merely *named*
  -- `Integer`. Nothing in the model rules those out, so the obligation would be
  -- unprovable rather than merely inconvenient. Giving them no declarations makes
  -- the type useless instead of unsound, which is the right failure direction and
  -- is what `Sub` will fix (an `Integer` receiver should be typed `.int`).
  | .cls n => if groundClassNames.contains n then [] else [n]

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

/-- **One table is carried by another**: every signature the first supports, the
    second supports identically.

    Stated over `declFor` rather than over the row lists because that is the only
    thing any rule reads, and because the structural version would be false for
    the shape that matters: `declFor` on a two-class ground type demands
    *agreement*, so a table can gain a row (`TrueClass#foo`) and support strictly
    fewer signatures than before unless the agreement survives. Requiring the
    conclusion directly makes the relation say what its users need and leaves the
    proof obligation at the step that grows the table, which is where the
    information is.

    This is the slack the F1b.8 threading needs. `infer` threads the table in
    force, and a method body checked at one point in the program is *called* at a
    later one, by which time the table has grown; carrying the smaller table in
    the witness and relating the two by `SubDecls` is what avoids needing `infer`
    to be monotone in the table — which it is **not** (`declaresName` is
    name-global, so a new row refuses a `def` of that name). -/
def SubDecls (F F' : Decls) : Prop :=
  ∀ τ mname d, declFor F τ mname = some d → declFor F' τ mname = some d

theorem SubDecls.refl (F : Decls) : SubDecls F F := fun _ _ _ h => h

theorem SubDecls.trans {F F' F'' : Decls} (h₁ : SubDecls F F') (h₂ : SubDecls F' F'') :
    SubDecls F F'' := fun τ m d h => h₂ τ m d (h₁ τ m d h)

/-- The `sigOf` form, which is what the type rules read. -/
theorem SubDecls.sigOf_eq {F F' : Decls} (hs : SubDecls F F') {τ : Ty} {mname : String}
    {ps : List Ty} {τret : Ty} (h : sigOf F τ mname = some (ps, τret)) :
    sigOf F' τ mname = some (ps, τret) := by
  unfold sigOf at h ⊢
  cases hd : declFor F τ mname with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some d => rw [hs τ mname d hd]; rw [hd] at h; exact h

/-- **A row, added.** Prepending shadows: `declsFor` reads `D.find?`, which stops
    at the first entry for the class, so the new entry carries the class's old rows
    plus the new one and every other class is found further down unchanged.

    The alternative — rewriting the existing entry in place — needs a `List.map`
    whose `find?` behaviour is a lemma; this way the only fact anything needs is
    `List.find?`'s own equation. -/
def addRow (D : Decls) (cls name : String) (d : MethodDecl) : Decls :=
  { D with rows := (cls, (name, d) :: declsFor D cls) :: D.rows }

/-! ## The base table

`static-soundness-poc.md` §5's builtin signatures, as declarations. Every entry
is a **proof obligation** — `Proof/Static/Decls.lean`'s `DeclsOk` is what the
invariant carries, and `tableOk_declsOk` is the proof for these three. Entries
whose conformance is not proved may not appear; the notable absences and their
reasons are unchanged from P0 (`/` and `%` raise `ZeroDivisionError`, `**` makes
a Rational, and the `Float` promotions would need the argument type unpinned).
-/

def baseDecls : Decls := { rows :=
  [("Integer",
    [("+", { params := [.int], ret := .int }),
     ("-", { params := [.int], ret := .int }),
     ("*", { params := [.int], ret := .int }),
     -- **The first nullary row** (L152), and it is here to *exercise* the zero-arity
     -- rule rather than for its own sake: without a row whose `params` is `[]`,
     -- `sigOf` never answers `some ([], _)` and the new `infer` arm, `KontOk.recvK0`
     -- and its consecution case would all be unreachable code with a proof attached.
     -- `zero?` was picked over `even?`/`abs` for two measured reasons. Constraint 2:
     -- `declaresName` is name-global, so every row added here refuses `def <name>`
     -- program-wide — and `def zero?` appears in **0** of the 1,227 bootstraptest
     -- programs. And resolution: `ResolvesAt` requires `fromPrelude = false`, while
     -- `abs` is defined **twice** in `prelude/prelude.rb`, so its row would be
     -- unwitnessable at the prelude-booted heap even though it is fine at the boot
     -- one. Check both before adding a row, not just the first.
     ("zero?", { params := [], ret := .bool })])] }

/-! ## The reopenable classes

`class C … end` takes one of three branches in `enterClassBody`
(`Interp/Dispatch.lean:236`): **reopen** if `constOwn defmod name` answers a class
object of matching kind, **`TypeError`** if it answers anything else, and
**allocate** if it answers nothing. Only the first is a step the invariant can
survive today — the third writes a class into the heap, which is what
`PlainGrow`'s *nothing became a class* clause forbids, and the second is a `.jump`,
which `CtlOk` refuses outright.

So the rule is admissible for a name the invariant can *promise* takes the reopen
branch, and this is that list. Every entry is a proof obligation of exactly the
same kind as a `baseDecls` row — `ClassOk` (`Proof/Static/Decls.lean`) is what the
invariant carries and `classOkB` is what the certificate decides — and widening it
is a table row plus a `decide`.

`String` is the one entry, and it is not arbitrary: it is the only ground class
the fragment can currently *produce a value of* (`.str`, L151), so it is the only
one for which reopening buys a call site. -/
def reopenableClasses : List String := ["String"]

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
