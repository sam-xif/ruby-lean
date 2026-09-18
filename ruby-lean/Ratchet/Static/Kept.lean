import Ratchet.Static.Narrow
import Ratchet.Guards.GlobalConsts

/-!
# `Ratchet/Static/Kept.lean`

`ctxKept` — what a statement owes the context, which is what the sequence rule reports back
down — and `ctx0`, the starting context. Also the note about the judgment that used to head
this vocabulary and is gone; see `Ratchet/Static/README.md`.
-/

namespace Ratchet

/-! ## What a statement owes the context the sequence rule reports back down

`context-splitting.md` §3 prices "weaken an outgoing `P'` back to a smaller `P`" at "antitone,
one line", on the grounds that `PosOk` is a `∀`-over-a-set and a bigger set is a stronger claim.
Three of `StateOk`'s components are not that shape, and this predicate is what buys them:

* **`ConstsOk`/`ConstPathsOk`** — `extendConsts` is `envSet`, which **overwrites**. A statement
  that rebinds a constant at a different type falsifies the old claim outright, and one that
  binds a *qualified* key can shadow an unqualified one `constGet?` was resolving through the
  frame's cref. §10.3's "our facts are keyed and immutable-per-key" is exactly what `consts` is
  not: it is keyed and **mutable** per key.
* **`BaseChainsOk`** — three of its clauses are guarded by facts *about the context*
  (`coreConstFree`, `isANoOk`, and `constGet? cn = none`), and every one of them fires on
  **fewer** inputs as the context grows. So it is antitone exactly where `ClassesOk` is
  monotone. That is §1.1's opposite-variance problem again, surviving the polarity split
  because this time it is *inside* `Pos`.

Each clause is a decidable `Bool` at a concrete pair of contexts, discharged by `rfl` wherever
it is a premise — the same shape `Neg`'s premises have, for §10.1(1)'s reason. What it refuses
is a statement that rebinds a constant, shadows one through the cref, binds a **class** to a new
constant (§F10's `Foo = Integer` shape), rebinds a core class name, or declares a class below a
builtin base. `Judge.casgn`'s `constAsgnOk` (§F18) already refuses the first; no corpus program
does any of the rest, which is what makes this a premise rather than a loss.

The honest reading: this is the *residue* of §7.2. `consts` is not a `Pos` field — it neither
grows monotonically nor stays immutable per key — and the two facts `BaseChainsOk` guards on are
**negative** facts about the context ("no constant rebinds a core name", "no class is declared
below this base"), which by §2's own test belong in `Neg`, seeded whole-program the way
`noMethod` is. Until that edit window, this predicate names the gap and makes it checkable. -/

/-- Does this type denote a class *object*? `.clsOf` is the only arm that does, and §F10's
shape (`Foo = Integer`) is exactly a constant bound at one. -/
def isClsOfTy : Ty → Bool
  | .clsOf _ => true
  | _ => false

/-- The seven static ancestor chains `Denote/Sem/Core/State.lean`'s `BaseChainsOk` is stated over,
without the boot ids — so that a `Ratchet`-side premise can talk about them. Kept here rather
than there because the *checker* is what has to discharge it. -/
def builtinChains : List (List String) :=
  [["Integer", "Numeric", "Comparable"] ++ rootAncestors,
   ["Float", "Numeric", "Comparable"] ++ rootAncestors,
   "NilClass" :: rootAncestors,
   ["Symbol", "Comparable"] ++ rootAncestors,
   ["String", "Comparable"] ++ rootAncestors,
   ["Hash", "Enumerable"] ++ rootAncestors,
   ["Array", "Enumerable"] ++ rootAncestors]

/-- **Everything `κ` claims about a machine, `κ'` still claims.**

Two families of clause, one per component that is not simply a `∀`-over-a-growing-set:

* **constants** (`ConstsOk`, `ConstPathsOk`) — every binding survives at the same type, and no
  new key shadows one `constGet?` was resolving through the frame's cref.
* **the class table's *antecedents*** (`DeclClassOk`) — `smroGet? … "new" = none`,
  `ctorGet? … = none`, `ancestors? … = some ch` and `mixinFreeChain` all guard clauses of that
  component, and all four fire on fewer inputs as the table grows. Stated one-directionally,
  since only "the goal's antecedent implies the hypothesis's" is needed.

`BaseChainsOk`'s three guards are **not** here: they were moved to `Neg` (`wholeCls`,
`boundConsts`), which `Ctx.afterStmt` does not touch, so they are invariant rather than
merely checked.

What is refused is a statement that rebinds a constant, shadows one through the cref, or
**reopens a class the context already records** in a way that changes its ancestor chain, its
`new`, or its `initialize`. `Judge.casgn`'s `constAsgnOk` (§F18) already refused the first. -/
def ctxKept (κ κ' : Ctx) : Bool :=
  κ.consts.all (fun p => decide (envGet? κ'.consts p.1 = some p.2)) &&
  -- Inside a method body, no *new* constant key at all. That is not the restriction it looks
  -- like: `constGet?` resolves through the frame's cref, so a new qualified key can change the
  -- answer for a name whose binding did not move — and Ruby forbids the shape anyway
  -- ("dynamic constant assignment" is a SyntaxError inside a method).
  (match κ.frame with
   | none => true
   | some _ => κ'.consts.all (fun p => (envGet? κ.consts p.1).isSome)) &&
  κ.classes.all (fun c =>
    (ancestors? κ.classes c.name == ancestors? κ'.classes c.name) &&
    (!(smroGet? κ.classes c.name "new").isNone || (smroGet? κ'.classes c.name "new").isNone) &&
    (!(ctorGet? κ.classes c.name).isNone || (ctorGet? κ'.classes c.name).isNone)) &&
  (!mixinFreeChain κ.classes rootAncestors || mixinFreeChain κ'.classes rootAncestors)

/-! ## The judgment itself lived here, and is gone

`inductive Judge` and its seven companions — 83 rules, 1,750 lines — were deleted in clink 68
along with `chk`, its 177 hand derivations and its soundness proof. The replacement is
`Ratchet/Check/Check.lean`'s `DJudge`: twelve rules, authored one at a time, each of which can only
join the certified judgment by acquiring an answer-typed semantic proof
(`Denote/Rules/`). `implementation-notes.md` clinks 65-68 and `AGENTS.md` record why 83 rules
with 48 value-shaped proofs could not be retrofitted into that discipline.

What survives in this file is the **datatype substrate** the semantic layer is indexed by:
`Ctx` and its three polarities, the class/method/constant tables and their accessors, and the
predicates `Denote/Sem/Core/State.lean`'s conformance components read (`nameFreeN`, `clsGet?`,
`smroGet?`, `constGet?`, …). `StateOk κ Γ I m` needs a `κ`; this is where `κ` is defined.

Also surviving, and worth knowing they are here rather than being rediscovered: `PrimSig`,
`EqSafe`, `NilQSafe`, `Comparable`, `IterSig`, `NarrowCond` and the narrowing functions
(`narrowEnvs`/`narrowSpine`/`falsyTy`/`truthyTy`). Those are *tables and predicates*, not
rules, and each records a fact about CRuby that a `DPrim` row or a future narrowing rule will
want — `Ratchet/Check/Check.lean`'s `DPrim` has 7 rows against `PrimSig`'s ~90 precisely so that the
obligation for each can be discharged one at a time. Nothing in the certified path reads them
today. -/



/-! ## The starting context

Moved here from `Ratchet/Validate.lean` when that file was deleted (clink 68): the *value*
is part of the context datatype's interface, and `Denote/Sem/Core/State.lean`'s conformance
statements are the only consumers left. -/

/-- The starting context: no classes, no methods, no assumptions, no `self`. Every
emptiness is load-bearing, and for a different reason — the two syntax tables because
nothing is declared before a program's first statement, the assumption table because a
derivation carrying one is only a conditional claim, and `frame`/`selfTy` because a
program's top level is inside no method and runs somewhere `self` is not an instance of
anything this judgment models. The constant table is empty for the first of those reasons:
a program's first statement is the first thing that could assign one. -/
def ctx0 : Ctx := ⟨⟨[], [], [], [], true, [], bootGlobalConsts⟩, ⟨[], [], [], false, [], [], []⟩, ⟨none, [], none, none, [], true, none, true⟩⟩

end Ratchet
