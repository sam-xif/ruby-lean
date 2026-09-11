import Denote.Typed.Controls

/-!
# `Denote/Typed/Safety.lean` — **the end-to-end safety proof, one theorem per certified rung**

This is where the ladder's safety claim is cashed out, and it is the file to watch: one
theorem per corpus rung the certified judgment covers, at the **real prelude-booted machine**
the difftest SUT runs, with every hypothesis discharged.

```
corpus/NNN-id.rb  --(pipeline)-->  Deriv  --(check)-->  DJudge
                                                         |
                        registered rules only -----> DJudgeC dclinks
                                                         |  dregistry_safe
                                                         v
                                   StuckFree bootMachine <program>
```

`StuckFree m e` is `∀ fuel, Semantics.typeStuck (Interp.run fuel (evalFrom m e)) = false` —
**at every fuel**, so it covers runs that return, escape, diverge and gate alike. `typeStuck`
is the model's own predicate for an uncaught `NoMethodError`/`ArgumentError`/`TypeError`.

## Why it cannot go stale

Safety is a **field of the clink target** (`SemSafeA` = `SemJudgeA ∧ SafeJudge`), so
`dregistry_safe` is unconditional and holds at every registry size. A rule cannot join
`DJudgeC` without its safety proof, and a rule leaving would break `dclinks`. So "the safety
proof stays green at every clink" is not a discipline anyone has to remember — it is what the
`Clink` structure's third field means.

What each theorem below *adds* to that is the discharge of the remaining hypothesis: the
program has a derivation using only registered rules, and `bootMachine` conforms. The second
is `stateOk_boot`, conditional on one `Bool` (`bootOkB`) rather than `decide`d, because the
booted heap is the output of `Interp.run 200_000` over the whole prelude and kernel reduction
of that is not on the table. The `Bool` is a build gate in `Denote/Sanity.lean`;
`native_decide` was rejected for the axiom it costs.

## What is *not* claimed

These are the rungs whose derivations use **only the eight registered rules**: a literal, or a
local read. Rungs 009 onward are checked by `Ratchet/Check.lean` and have no safety theorem,
because `prim`, `seq`, `vasgn` and `if'` are unregistered — all four behind `RunAPushK`
(`Denote/Typed/JudgeA.lean` §4). `lake exe semladder` reports both numbers so the gap is a
line in the report rather than a footnote here.
-/

set_option autoImplicit false

namespace Ratchet.Denote.Typed

open RubyCore Ratchet Ratchet.Denote

/-! ## §1 The derivations, one per registered leaf

Each is `hF c hc` — the rule, handed over by the closure hypothesis. One line, because the
Church encoding makes a derivation a term (`Denote/Clink/Spec.lean` §3). -/

theorem derivD_fltLit {Γ : Env} {b : UInt64} : (DJudgeC dclinks).judge Γ (.flt b) .float Γ :=
  fun _ hF => hF DClink.fltLit (by simp [dclinks])

theorem derivD_strLit {Γ : Env} {s : String} :
    (DJudgeC dclinks).judge Γ (.str s) (.cls "String") Γ :=
  fun _ hF => hF DClink.strLit (by simp [dclinks])

theorem derivD_symLit {Γ : Env} {s : String} : (DJudgeC dclinks).judge Γ (.sym s) .sym Γ :=
  fun _ hF => hF DClink.symLit (by simp [dclinks])

theorem derivD_truLit {Γ : Env} : (DJudgeC dclinks).judge Γ .tru .bool Γ :=
  fun _ hF => hF DClink.truLit (by simp [dclinks])

theorem derivD_flsLit {Γ : Env} : (DJudgeC dclinks).judge Γ .fls .bool Γ :=
  fun _ hF => hF DClink.flsLit (by simp [dclinks])

theorem derivD_nilLit {Γ : Env} : (DJudgeC dclinks).judge Γ .nil .nilT Γ :=
  fun _ hF => hF DClink.nilLit (by simp [dclinks])

/-! ## §2 The rungs, at the booted machine

The programs are the corpus's own — `corpus/001-int-lit.rb` is `1`, and so on down to
`008-neg-int-lit.rb`'s `-5`, which the desugarer emits as a negative literal rather than a
unary send (which is why one rule covers both). -/

/-- `corpus/001-int-lit.rb` — `1`. -/
theorem safe_001_int_lit (hb : bootOkB = true) : StuckFree bootMachine (.int 1) :=
  dregistry_safe derivD_intLit (stateOk_boot hb)

/-- `corpus/002-bool-true.rb` — `true`. -/
theorem safe_002_bool_true (hb : bootOkB = true) : StuckFree bootMachine .tru :=
  dregistry_safe derivD_truLit (stateOk_boot hb)

/-- `corpus/003-bool-false.rb` — `false`. -/
theorem safe_003_bool_false (hb : bootOkB = true) : StuckFree bootMachine .fls :=
  dregistry_safe derivD_flsLit (stateOk_boot hb)

/-- `corpus/004-str-lit.rb` — `"hello"`. The one rung here whose evaluation **allocates**, so
its clink's proof goes through `ext_push` rather than being `rfl` at the step. -/
theorem safe_004_str_lit (hb : bootOkB = true) : StuckFree bootMachine (.str "hello") :=
  dregistry_safe derivD_strLit (stateOk_boot hb)

/-- `corpus/005-sym-lit.rb` — `:ok`. -/
theorem safe_005_sym_lit (hb : bootOkB = true) : StuckFree bootMachine (.sym "ok") :=
  dregistry_safe derivD_symLit (stateOk_boot hb)

/-- `corpus/006-nil-lit.rb` — `nil`. -/
theorem safe_006_nil_lit (hb : bootOkB = true) : StuckFree bootMachine .nil :=
  dregistry_safe derivD_nilLit (stateOk_boot hb)

/-- `corpus/007-flt-lit.rb` — `1.5`, carried as its IEEE-754 bit pattern by the syntax layer
(`Ratchet/Expr.lean`: `Float` has no useful `DecidableEq`, so `flt` stores the bits). -/
theorem safe_007_flt_lit (hb : bootOkB = true) :
    StuckFree bootMachine (.flt (1.5 : Float).toBits) :=
  dregistry_safe derivD_fltLit (stateOk_boot hb)

/-- `corpus/008-neg-int-lit.rb` — `-5`. -/
theorem safe_008_neg_int_lit (hb : bootOkB = true) : StuckFree bootMachine (.int (-5)) :=
  dregistry_safe derivD_intLit (stateOk_boot hb)

/-! ## §3 The list **is** the theorem's subject

`safeRungs` pairs each rung's name with the program the theorem above is about, and
`safeRungs_safe` is proved over the list — so the list and the proofs cannot drift. The
previous version was a `List String` with a `#guard` on its *length*, which would have been
satisfied by eight names and no theorems. -/

def safeRungs : List (String × Ratchet.Expr) :=
  [("001-int-lit", .int 1),
   ("002-bool-true", .tru),
   ("003-bool-false", .fls),
   ("004-str-lit", .str "hello"),
   ("005-sym-lit", .sym "ok"),
   ("006-nil-lit", .nil),
   ("007-flt-lit", .flt (1.5 : Float).toBits),
   ("008-neg-int-lit", .int (-5))]

/-- **Every program named in `safeRungs` is safe at the booted machine.** One case per entry,
each discharging to the named theorem above, so adding a list entry without a theorem does not
typecheck. -/
theorem safeRungs_safe (hb : bootOkB = true) :
    ∀ q ∈ safeRungs, StuckFree bootMachine q.2 := by
  intro q hq
  simp only [safeRungs, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact safe_001_int_lit hb
  · exact safe_002_bool_true hb
  · exact safe_003_bool_false hb
  · exact safe_004_str_lit hb
  · exact safe_005_sym_lit hb
  · exact safe_006_nil_lit hb
  · exact safe_007_flt_lit hb
  · exact safe_008_neg_int_lit hb

/-! ## §4 …and every registered rule is **exercised** by it

The gate this section adds. A rule could be registered — proved, in the judgment, counted —
and never appear in any program the safety proof is about, in which case the end-to-end claim
would be about a fragment narrower than the registry. `rulesUsed` says which rules a
derivation of a program *must* use (exact for this fragment: each `Expr` head admits exactly
one `DJudge` rule), and the `#guard` below requires every registered rule to be used by at
least one rung.

It grows by itself in the direction that matters: register `vasgn` and the guard fails until
`safeRungs` gains a program containing an assignment. That is the check
`scripts/run_typed_ratchet.sh` asks for, run at build time where it cannot be skipped. -/

mutual
/-- The `DJudge` rules a derivation of `e` must use. `"?"` for a head with no rule, so an
unsupported program shows up as an uncovered name rather than as an empty list. -/
def rulesUsed : Ratchet.Expr → List String
  | .int _ => ["intLit"]
  | .flt _ => ["fltLit"]
  | .str _ => ["strLit"]
  | .sym _ => ["symLit"]
  | .tru => ["truLit"]
  | .fls => ["flsLit"]
  | .nil => ["nilLit"]
  | .var .lvar _ => ["var"]
  | .vasgn .lvar _ e => "vasgn" :: rulesUsed e
  | .seq es => "seq" :: rulesUsedAll es
  | .send (some r) _ args none => "prim" :: (rulesUsed r ++ rulesUsedAll args)
  | .if' c t (some e) => "if'" :: (rulesUsed c ++ rulesUsed t ++ rulesUsed e)
  | _ => ["?"]

def rulesUsedAll : List Ratchet.Expr → List String
  | [] => []
  | e :: es => rulesUsed e ++ rulesUsedAll es
end

/-- Every rule the safety proof's programs need, with duplicates. -/
def rulesExercised : List String := rulesUsedAll (safeRungs.map (·.2))

/-- Registered rules that **no rung the safety proof covers uses**, frozen by name. The gate
below fails if anything else joins this list, so a newly registered rule must either be
exercised end to end or be added here with a reason.

Today: **`var`**, and the reason is structural rather than an oversight
(`found-issues.md` §F30). A program that reads a local has to bind it first, so exercising
`var` needs an assignment and a statement sequence — `vasgn` and `seq`, both unregistered and
both behind `RunAPushK`. There is no single-expression program in the corpus that reads a
local: a bare name that is *not* a local desugars to `vcall`, which has no rule at all. So
`var`'s clink is proved and in the judgment, and the end-to-end safety claim genuinely does
not reach it yet. **Only ever shrink this.** -/
def unexercised : List String := ["var"]

-- **The coverage gate.** Every registered rule is either used by a rung the safety proof
-- covers, or a named exception. Register a rule without exercising it and this goes red.
#guard dRegisteredRules.all (fun r => rulesExercised.contains r || unexercised.contains r)

-- The other direction, and the control that keeps the gate from being vacuous: every name in
-- `unexercised` really is registered and really is unexercised.
#guard unexercised.all (fun r => dRegisteredRules.contains r && !rulesExercised.contains r)

-- And no rung uses an unregistered rule -- which the safety theorems' existence already
-- forces, but stating it makes the two columns' relationship checkable.
#guard dUnregisteredRules.all (fun r => !rulesExercised.contains r)

-- And no rung reaches a head with no rule, which would make `rulesUsed` an over-approximation
-- of something unprovable.
#guard !rulesExercised.contains "?"

#print axioms safe_001_int_lit
#print axioms safe_004_str_lit
#print axioms safe_007_flt_lit
#print axioms safe_008_neg_int_lit

end Ratchet.Denote.Typed
