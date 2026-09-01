import Ratchet.Corpus
import Ratchet.Rungs
import Semantics.Interp

/-!
# `checkrungs` — pinning the hand-authored derivations to reality

`Ratchet/Rungs.lean` proves that the hand-written `Judge` derivations typecheck and that
`chk` agrees with each. Neither of those facts, on its own, rules out the two ways a
hand-authored judgment can be confidently wrong:

1. **The syntax could be a fiction.** A derivation about `send (int 1) "+" [int 2] nil`
   says nothing about the rung if the desugarer actually emits something else for
   `1 + 2`. So: decode each rung's committed `corpus/*.json` with the real
   `Ratchet.Decode.program` and compare it to the hand-written `Expr` with `==`.
2. **The types could be a fiction.** `Judge` says `1 + 2 : Int` and `"a" + "b" :
   String`; that is an assertion about what the semantics *does*. So: decode the same
   JSON a second time with the real `RubyCore.Decode.program`, run it under the real
   `stepFn` from the real booted heap, and check the value's actual class is one the
   claimed `Ty` names — and that the run is not type-stuck.

This is the one file in the package allowed to see both sides (`Ratchet/`'s copied type
language and `../lean/RubyCore`'s semantics); see `Semantics/Interp.lean`'s docstring for
why the boundary is drawn that way. It is a separate executable from `ratchet` on
purpose: the ratchet's headline number stays a pure statement about `validate`, and this
is the evidence behind the rungs it now counts.
-/

open Ratchet
open Lean (Json)

/-- The runtime class names a `Ty` admits — the bridge between the two languages, and
the only place a `Ty` is given an extensional reading in this package.

`.bool` maps to *both* boolean classes because `Ty` does not distinguish them
(`Judge.truLit`). Only the constructors the climbed rungs use are listed; anything else
returns `[]`, which fails loudly rather than passing vacuously. -/
def expectedClasses : Ty → List String
  | .int => ["Integer"]
  | .float => ["Float"]
  | .sym => ["Symbol"]
  | .nilT => ["NilClass"]
  | .bool => ["TrueClass", "FalseClass"]
  | .cls n => [n]
  -- Tier 4's joins produce types that admit more than one class, and the reading is
  -- exactly the obvious one: a `nilable` also admits `nil`, a `union` admits either
  -- side's classes. This is the point at which a `Ty` stops naming *the* class of the
  -- value and starts naming a *set* it belongs to (see `Ty.joinT`'s docstring), so the
  -- cross-check gets correspondingly weaker for these rungs -- deliberately, and
  -- visibly: the rung still fails if the class produced is outside the set.
  | .nilable τ => "NilClass" :: expectedClasses τ
  | .union σ τ => expectedClasses σ ++ expectedClasses τ
  -- Tier 5: an array literal's value is an `Array` whatever its element type is. The
  -- element type itself is *not* cross-checked against the semantics here — this harness
  -- compares the class of the whole result value, and nothing in it inspects an array's
  -- contents. What backs the element type instead is `arrayLit`'s premise: each element
  -- has its own derivation, and each of those would be a row here if it were a rung.
  | .arrayOf _ => ["Array"]
  | _ => []

/-- Fuel: these are small literal/arithmetic programs; a few hundred steps is already
generous, and `outOfFuel` is reported as a failure rather than silently passing. -/
def fuel : Nat := 20000

structure Row where
  id : String
  syntaxOk : Bool
  claimedTy : Ty
  outcome : String
  actualClass : Option String
  typeStuck : Bool
  semOk : Bool

def rowOk (r : Row) : Bool := r.syntaxOk && r.semOk && !r.typeStuck

def loadJson (p : System.FilePath) : IO Json := do
  match Json.parse (← IO.FS.readFile p) with
  | .error e => throw (IO.userError s!"{p}: JSON parse error: {e}")
  | .ok j => pure j

def checkRung (corpusDir : System.FilePath) (files : List System.FilePath)
    (r : Rung) : IO Row := do
  -- Find this rung's file by its recorded `id`, not by filename arithmetic.
  let mut found : Option Json := none
  for f in files do
    let j ← loadJson f
    match j.getObjValAs? String "id" with
    | .ok id => if id == r.id then found := some j
    | .error _ => pure ()
  let some j := found
    | throw (IO.userError s!"no corpus entry with id '{r.id}' under {corpusDir}")

  -- (1) syntax: does the real desugarer output decode to the hand-written `Expr`?
  let entry ← match CorpusEntry.ofJson? j with
    | .error e => throw (IO.userError s!"{r.id}: {e}")
    | .ok e => pure e
  let syntaxOk := entry.program == r.program

  -- (2) semantics: decode the same JSON into the real `RubyCore.Expr` and run it.
  let rp ← match RubyCore.Decode.program (← match j.getObjVal? "program" with
      | .error e => throw (IO.userError s!"{r.id}: missing program: {e}")
      | .ok p => pure p) with
    | .error e => throw (IO.userError s!"{r.id}: RubyCore decode: {e}")
    | .ok p => pure p
  let res := Ratchet.Semantics.run fuel rp
  let actualClass := Ratchet.Semantics.resultClassName res
  let stuck := Ratchet.Semantics.typeStuck res
  -- `.any` is the one type with no extensional content: it names no class, so the only
  -- thing left to check about a run is that it did not go type-stuck (which is checked
  -- separately, by `rowOk`). Today exactly one rung derives it —
  -- `bare-undeclared-var`, which raises `NameError` and so produces no value at all —
  -- and a rung that claimed `.any` for a program that *does* return a value would be
  -- passing here vacuously. That is the honest cost of `.any` being in the grammar; it
  -- is flagged in the report as `claims .any` rather than shown as a class match.
  let semOk := if r.ty == .any then true else match actualClass with
    | some cn => (expectedClasses r.ty).contains cn
    | none => false
  return { id := r.id, syntaxOk, claimedTy := r.ty
           outcome := Ratchet.Semantics.outcomeLabel res
           actualClass, typeStuck := stuck, semOk }

/-! ## Negative controls for `PrimSig`

Confirming the climbed rungs pass says nothing about whether `PrimSig`'s five rows are too
*generous* — a table with `PrimSig.intAdd : PrimSig .int "+" [.any] .int` would also pass
them all. These controls are the other side: neighbours of the rungs, one syntactic step
away, that `chk` must **not** certify. Each is hand-written syntax (not a corpus rung) —
that is the point, since what is being probed is the table's argument types, and it is
run under the real semantics to say which kind of rejection it is:

- **sound rejection** — the program really is type-stuck, so rejecting it is required.
- **conservative rejection** — the program is safe and `chk` still says no. Honest
  incompleteness, recorded rather than hidden: `1 + 1.5` is fine Ruby, and `PrimSig` has
  no `Integer#+ Float` row because no rung has needed one yet.

`BareNameError` gets the controls that matter most on this ladder, because the rule it
gates is the one a careless reading would state as a blanket "a bare name raises
NameError, which is not a type error". `proc` and `lambda` are bare names that resolve
to real `Kernel` methods and raise **ArgumentError** with no block — squarely in the
type-stuck family — so they are sound rejections that only the table's narrowness earns.
`y` is the other side: genuinely unbound and therefore safe, rejected purely because
nobody has added its row.

Note what the model says about `proc`/`lambda` versus what CRuby does. CRuby raises
`ArgumentError` ("tried to create Proc object without a block") — verified directly, and
that is the fact the narrowness of `BareNameError` is justified against. `RubyCore` does
not model the block-less form at all and answers `unsupported`, which is neither safe
nor stuck, so these two controls print the "model declined" verdict rather than a
soundness claim. They still do their job: the blanket rule is refuted by Ruby, and the
model's silence is not evidence for it.

The tier-2 rows added alongside `objEq` each get a control of the same kind: `1 < "a"`
and `1.length` and `nil.zero?` probe the receiver/argument constraints of the comparison
and nullary-query rows (all three genuinely raise), while `!nil`, `"a" < "b"` and
`5.to_s(2)` are the conservative side — safe Ruby whose signature is deliberately not in
the table. `PrimSig.objEq` has no *sound-rejection* control at all, and that is not an
oversight: `==` really is total on every receiver `EqSafe` admits, so there is no
neighbouring `==` program in this fragment that raises. What constrains it is `EqSafe`
itself, and the only way to violate that is with a `Ty` (`.any`, an arrow) no expression
in this fragment synthesizes.

The check fails only on a `validate = true` here; a conservative rejection is expected. -/
structure Control where
  label : String
  program : Expr

def controls : List Control :=
  [ ⟨"1 + true", .send (some (.int 1)) "+" [.tru] none⟩
  , ⟨"1 + \"a\"", .send (some (.int 1)) "+" [.str "a"] none⟩
  , ⟨"\"a\" + 1", .send (some (.str "a")) "+" [.int 1] none⟩
  , ⟨"1 + nil", .send (some (.int 1)) "+" [.nil] none⟩
  , ⟨"1 + 1.5 (safe; no PrimSig row)", .send (some (.int 1)) "+" [.flt (Float.toBits 1.5)] none⟩
  , ⟨"1.5 + 1 (safe; no PrimSig row)", .send (some (.flt (Float.toBits 1.5))) "+" [.int 1] none⟩
  , ⟨"1 < \"a\"", .send (some (.int 1)) "<" [.str "a"] none⟩
  , ⟨"1.length", .send (some (.int 1)) "length" [] none⟩
  , ⟨"nil.zero?", .send (some .nil) "zero?" [] none⟩
  , ⟨"!nil (safe; no PrimSig row)", .send (some .nil) "!" [] none⟩
  , ⟨"\"a\" < \"b\" (safe; no PrimSig row)", .send (some (.str "a")) "<" [.str "b"] none⟩
  , ⟨"5.to_s(2) (safe; no PrimSig row for the base form)",
      .send (some (.int 5)) "to_s" [.int 2] none⟩
  , ⟨"proc (a bare name that is NOT unbound)", .vcall "proc"⟩
  , ⟨"lambda (likewise)", .vcall "lambda"⟩
  , ⟨"y (safe; unbound, but not a BareNameError row)", .vcall "y"⟩
    -- The environment-join control: the same shape as
    -- `corpus/042-if-does-not-leak-reassignment`, kept here as well because this is
    -- where a rejection is labelled *sound* by actually running the program. An `if`
    -- rule that carried the pre-`if` environment forward would certify this.
  , ⟨"x = 1; if true then x = \"hello\" end; x + 1",
      .seq [.vasgn .lvar "x" (.int 1),
            .if' .tru (.vasgn .lvar "x" (.str "hello")) none,
            .send (some (.var .lvar "x")) "+" [.int 1] none]⟩
    -- ### Tier 5's controls
    --
    -- One per new `PrimSig` row, plus the two places tier 5's honest imprecision shows.
    -- The first is the only *unsound*-if-admitted one; the rest are safe programs this
    -- checker declines, and they are here so the cost is a recorded number rather than a
    -- surprise.
    -- `arrayIndex`'s `[.int]` argument is load-bearing: a String subscript raises
    -- TypeError, inside the family.
  , ⟨"[1,2,3][\"a\"]",
      .send (some (.array [.int 1, .int 2, .int 3])) "[]" [.str "a"] none⟩
    -- `nilable` is the price of not tracking lengths: this is safe Ruby (`2`) that the
    -- checker cannot type, because `nilable Int` matches no arithmetic row.
  , ⟨"[1,2,3][0] + 1 (safe; nilable result matches no PrimSig row)",
      .send (some (.send (some (.array [.int 1, .int 2, .int 3])) "[]" [.int 0] none))
        "+" [.int 1] none⟩
    -- The `Ty` gap in `hash-lit`/`hashIndex`, cashed out: safe Ruby (`2`), untypeable
    -- because `.any` is inert by design.
  , ⟨"{\"a\"=>1}[\"a\"] + 1 (safe; .any result is inert)",
      .send (some (.send (some (.hash [(.str "a", .int 1)])) "[]" [.str "a"] none))
        "+" [.int 1] none⟩
    -- And the element-union's price: safe Ruby (`2`), rejected because the array's
    -- element type is a union.
  , ⟨"[1,\"a\"][0] + 1 (safe; element type is a union)",
      .send (some (.send (some (.array [.int 1, .str "a"])) "[]" [.int 0] none))
        "+" [.int 1] none⟩
    -- ### Tier 6's controls
    --
    -- The first two are the two places tier 6 could have been *unsound*, and each one
    -- corresponds to a specific premise added this clink. They are the reason those
    -- premises are not decoration.
    -- (a) `Judge.callDef`'s second pass. `def f(x) = if x <= 0 then 1 else f(x-1) + true`
    -- really raises TypeError: the recursion bottoms out, returns 1, and `1 + true` runs.
    -- The *first* pass alone accepts it — the recursive call typed at `.never` makes the
    -- whole `else` branch `.never`, which the join then discards, leaving `Int`. Only
    -- re-running the body with `Int` assumed exposes `Int + true`.
  , ⟨"def f(x) = if x<=0 then 1 else f(x-1)+true; f(1)",
      .seq [.def' "f" [.req "x"]
              (.if' (.send (some (.var .lvar "x")) "<=" [.int 0] none)
                (.int 1)
                (some (.send
                  (some (.send none "f"
                    [.send (some (.var .lvar "x")) "-" [.int 1] none] none))
                  "+" [.tru] none))),
            .send none "f" [.int 1] none]⟩
    -- (b) `Judge.bareName`'s `defGet? D m = none` premise. Without it this takes the
    -- `BareNameError "x"` route to `.any` and validates a program that raises TypeError.
  , ⟨"def x; 1 + true; end; x",
      .seq [.def' "x" [] (.send (some (.int 1)) "+" [.tru] none), .vcall "x"]⟩
    -- (c) Per-call-site instantiation, from the failing side: the same `def` is fine at
    -- Int and stuck at String, and only the call site decides which.
  , ⟨"def f(x) = x + 1; f(\"a\")",
      .seq [.def' "f" [.req "x"] (.send (some (.var .lvar "x")) "+" [.int 1] none),
            .send none "f" [.str "a"] none]⟩
    -- (d) `paramEnv`'s required-parameters-only restriction, measured: safe Ruby the
    -- checker declines because `Param.opt` answers `none` (AGENTS.md §Frontier item 3).
  , ⟨"def f(x = 1); x; end; f() (safe; optional param unsupported)",
      .seq [.def' "f" [.opt "x" (.int 1)] (.var .lvar "x"),
            .send none "f" [] none]⟩ ]

mutual

/-- `Ratchet.Expr` → `RubyCore.Expr` for the controls only: they are hand-written on this
package's side of the isolation boundary, so there is no JSON to decode twice the way a
corpus rung has. Covers exactly the constructors `controls` uses; anything else is a
`none` that fails loudly. -/
def toRubyCore : Expr → Option RubyCore.Expr
  | .int n => some (.int n)
  | .flt b => some (.flt b)
  | .str s => some (.str s)
  | .sym s => some (.sym s)
  | .tru => some .tru
  | .fls => some .fls
  | .nil => some .nil
  | .vcall m => some (.vcall m)
  | .var .lvar x => some (.var .lvar x)
  | .vasgn .lvar x e => (toRubyCore e).map (fun e' => .vasgn .lvar x e')
  | .seq es => (es.mapM toRubyCore).map (fun es' => .seq es')
  | .if' c t e => do
    let c' ← toRubyCore c
    let t' ← toRubyCore t
    match e with
    | none => return .if' c' t' none
    | some e => return .if' c' t' (some (← toRubyCore e))
  | .def' n ps body => do
    let ps' ← ps.mapM toRubyCoreParam
    return .def' n ps' (← toRubyCore body)
  | .send none m args none =>
    (args.mapM toRubyCore).map (fun args' => .send none m args' none)
  | .array es => (es.mapM toRubyCore).map (fun es' => .array es')
  | .hash ps => (toRubyCorePairs ps).map (fun ps' => .hash ps')
  | .send (some r) m args none => do
    let r' ← toRubyCore r
    let args' ← args.mapM toRubyCore
    return .send (some r') m args' none
  | _ => none

/-- Parameters, for the controls' `def`s. Only the two kinds the controls use. -/
def toRubyCoreParam : Param → Option RubyCore.Param
  | .req x => some (.req x)
  | .opt x d => (toRubyCore d).map (fun d' => .opt x d')
  | _ => none

/-- The pair-list companion, spelled out rather than a `mapM` with a lambda: the lambda
hides the structural decrease from the termination checker. -/
def toRubyCorePairs : List (Expr × Expr) → Option (List (RubyCore.Expr × RubyCore.Expr))
  | [] => some []
  | (k, v) :: ps => do
    let k' ← toRubyCore k
    let v' ← toRubyCore v
    return (k', v') :: (← toRubyCorePairs ps)

end

def main (args : List String) : IO UInt32 := do
  let corpusDir : System.FilePath := args.headD "corpus"
  let dirEntries ← corpusDir.readDir
  let files := (dirEntries.map (·.path)).toList.filter (fun p => p.toString.endsWith ".json")
  let rows ← rungs.mapM (checkRung corpusDir files)

  IO.println "--- climbed rungs: hand-authored derivations, pinned to corpus + semantics ---"
  for r in rows do
    let cls := r.actualClass.getD "-"
    let mark := if rowOk r then "ok  " else "FAIL"
    IO.println s!"{mark} {r.id}: claimed {repr r.claimedTy}, ran to {r.outcome} of class {cls}, type_stuck={r.typeStuck}, syntax_matches_corpus={r.syntaxOk}"

  IO.println "\n--- negative controls: neighbours `PrimSig` must not certify ---"
  let mut controlFails : List String := []
  for c in controls do
    let certified := validate c.program
    let some rp := toRubyCore c.program
      | throw (IO.userError s!"control '{c.label}': not translatable to RubyCore.Expr")
    let res := Ratchet.Semantics.run fuel rp
    let stuck := Ratchet.Semantics.typeStuck res
    let label := Ratchet.Semantics.outcomeLabel res
    let verdict :=
      if certified then "CERTIFIED -- table is too generous"
      else if stuck then "rejected (sound: really type-stuck)"
      else if label.startsWith "unsupported" || label == "outOfFuel" then
        -- The model declined to run it, so it says nothing either way. Recorded as its
        -- own verdict rather than being swept into "conservative: safe": calling a
        -- program safe because the model would not execute it is exactly the kind of
        -- vacuous pass this file exists to prevent.
        "rejected (model declined to run it -- see the control's note)"
      else "rejected (conservative: safe, no rule yet)"
    IO.println s!"{if certified then "FAIL" else "ok  "} {c.label}: {verdict}, ran to {Ratchet.Semantics.outcomeLabel res}"
    if certified then controlFails := c.label :: controlFails

  let bad := rows.filter (fun r => !rowOk r)
  IO.println s!"\n{rows.length - bad.length}/{rows.length} rungs confirmed: the hand derivation's type agrees with the class the real semantics produced, on the real desugarer's syntax, with nothing trusted anywhere."
  IO.println s!"{controls.length - controlFails.length}/{controls.length} negative controls rejected as required."
  if bad.isEmpty && controlFails.isEmpty then
    IO.println "CHECKRUNGS OK"
    return 0
  else
    for r in bad do IO.eprintln s!"  FAIL: {r.id}"
    for l in controlFails do IO.eprintln s!"  FAIL (control certified): {l}"
    return 1
