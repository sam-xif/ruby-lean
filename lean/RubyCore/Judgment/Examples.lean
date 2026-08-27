import RubyCore.Judgment.Judge

/-!
# Hand-built derivations — J0's exit criterion

Each example is a derivation term built by hand (constructors only, no tactics doing
search), demonstrating that the rules compose on the toy shapes the milestone names:
sequencing with a flow-sensitive environment, the one-rule `if` join, narrowing on a
nilable local, and a loop with a chosen stackmap. Emitters will build exactly these
trees (as `Deriv` data) at J2.
-/

namespace RubyCore.Judgment

open RubyCore.Types

/-- A context in which `self` is an Object instance — the toplevel-method shape. -/
def objCtx : JCtx := { cls := "Object", selfCls := some "Object" }

/-- `x = 1; x` — assignment retypes the environment, the read sees it. -/
example : Judge {} [] (.seq [.vasgn .lvar "x" (.int 1), .var .lvar "x"])
    false objCtx .int [("x", .int)] {} :=
  .seq (.cons
    (.vasgnLvar rfl .int)
    (.single (.varLvar rfl)))

/-- `if true then 1 else 2` — the join at a chosen upper bound (`.int`, both branches
    below it by reflexivity), continuation environment the entry one. -/
example : Judge {} [] (.if' .tru (.int 1) (some (.int 2)))
    false objCtx .int [] {} :=
  .ifElse .tru .int .int (SubJ.refl _) (SubJ.refl _) (SubEnv.refl _) (SubEnv.refl _)

/-- **A widened union join** (J14): `if true then 1 else "s"` — the branches share
    no `joinTy`, so `chk` would demand a claim and answer only under one; here the
    chosen bound is the union, each branch below it by one injection. -/
example : Judge {} [] (.if' .tru (.int 1) (some (.str "s")))
    false objCtx (.union .int (.cls "String")) [] {} :=
  .ifElse .tru .int .str (.unionR1 (SubJ.refl _)) (.unionR2 (SubJ.refl _))
    (SubEnv.refl _) (SubEnv.refl _)

/-- Narrowing: with `x : Int?` in the environment, `if x then x else 0` types at
    `.int` — the then-branch reads `x` at the narrowed `.int`.

    Both branches narrow: the then-branch reads `x` at `dropNil = .int`, the
    else-branch holds `x : nilT` (`elseNarrow`, since `.int` is `boolFree`).

    The continuation environment is `[]`: `SubEnv` is *exact-type* containment (it
    can drop a binding, never coarsen one), so `x` — `.int` at the then-exit,
    `.nilT` at the else-exit — survives at neither type. A subtype-aware
    environment weakening (or a per-binding `joinTy` env-join) is the precision
    upgrade, noted at J13. -/
example : Judge {} [("x", .nilable .int)]
    (.if' (.var .lvar "x") (.var .lvar "x") (some (.int 0)))
    false objCtx .int [] {} :=
  .ifNarrowElse rfl (.varLvar rfl) .int (SubJ.refl _) (SubJ.refl _)
    (fun _ _ h => by simp [envGet?] at h) (fun _ _ h => by simp [envGet?] at h)

/-- **A union re-narrowed** (J14): with `x : nilT ∪ Int` — the raw shape a widened
    join emits — `if x then x else 0` recovers `.int` in the then-branch
    (`dropNil` strips the nil member) and holds `x : nilT` in the else. -/
example : Judge {} [("x", .union .nilT .int)]
    (.if' (.var .lvar "x") (.var .lvar "x") (some (.int 0)))
    false objCtx .int [] {} :=
  .ifNarrowElse rfl (.varLvar rfl) .int (SubJ.refl _) (SubJ.refl _)
    (fun _ _ h => by simp [envGet?] at h) (fun _ _ h => by simp [envGet?] at h)

/-- `while true; x = 1; end` from `x : Int` — the stackmap `Γl` is the entry
    environment, the body's exit re-guarantees it, and the loop answers `nil` at
    `Γl`. -/
example : Judge {} [("x", .int)] (.while' .tru (.vasgn .lvar "x" (.int 1)))
    false objCtx .nilT [("x", .int)] {} :=
  .while' (SubEnv.refl _) .tru (SubEnv.refl _)
    (.vasgnLvar rfl .int) (fun _ _ h => h)

/-- Subsumption: `1` also judges at `Int?`, with a binding dropped from the exit
    environment. -/
example : Judge {} [("y", .bool)] (.int 3) false objCtx (.nilable .int) [] {} :=
  .sub .int (.base (by decide)) (fun _ _ h => by simp [envGet?] at h)

/-- **Arrow intro + elim, end to end** (L270/J16): `l = lambda { |a| a }; l.call(1)`
    types at `.int` — the lambda is minted at `(Int) → Int` (its body judged at the
    chosen parameter type), stored, read back, and `call`'s arguments checked
    against the spine. -/
example : Judge {} []
    (.seq [.vasgn .lvar "l"
             (.send none "lambda" [] (some (.block [.req "a"] [] (.var .lvar "a")))),
           .send (some (.var .lvar "l")) "call" [.int 1] none])
    false objCtx .int [("l", arrowOf [.int] .int)] {} :=
  .seq (.cons
    (.vasgnLvar rfl
      (.sendLambdaArrow rfl rfl (.varLvar rfl) (SubJ.refl _)))
    (.single (.sendCall (.varLvar rfl) rfl (.cons .int .nil) (.cons (SubJ.refl _) .nil))))

/-- **Arrow variance** (J16): `(Int?) → Int ≤ (Int) → Int?` — parameters
    contravariant (the wider lambda accepts at least an `Int`), return covariant. -/
example : SubJ (arrowOf [.nilable .int] .int) (arrowOf [.int] (.nilable .int)) :=
  .arrowCons (.base (by decide)) (.arrow0 (.base (by decide)))

/-- And the refusals that make variance meaningful: neither the flipped direction
    nor an arity mismatch is derivable — checked here only at the `subTy` base
    (the structural rules refuse by shape). -/
example : subTy (arrowOf [.int] (.nilable .int)) (arrowOf [.nilable .int] .int) = false := by
  decide

end RubyCore.Judgment
