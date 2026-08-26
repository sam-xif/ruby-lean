import RubyCore.Cert.Validate

/-!
# `chk`'s structural laws — the infer-free soundness development, rung 1

`validate` no longer calls `infer` (V9–V16, and V12 makes it a module-graph fact). The
*soundness argument* still does, through `CtlOk`, whose eval clause is literally
`infer F Γ e … = some …` (`Proof/Static/Konts.lean`). Closing that is milestone **C-1**
(`docs/semantics/certificate-language.md` §10.6): restate the invariant over `chk`,
which needs `chk`'s structural laws first, which is this file.

A bridge from `chk` *back* to `infer` was built and deleted: it makes the headline
theorem depend on the function the pivot exists to retire, so `infer` could not be
deprecated while the bridge held the theorem up.

## V20 — the induction principle, and the measurement that priced the rung

V17 estimated the port at ~8,200 lines and was pricing the **wrong design**. The
correction is V19 (`Cert/Check.lean`): with `chk` and its helpers in one `mutual` block
where every call decreases the fuel, Lean derives **`chk.induct`** — ten motives, one
per function, the same shape `Proof/Static/Mono.lean`'s twenty laws are written
against. Hand-rolling a single law without it took a session and did not close.

**The motive map**, which is the hard-won part and cannot be read off the file:

| motive | function | note |
|---|---|---|
| 1 | `chkOpt` | |
| 2 | `chk` | the goal's own motive |
| 3 | `chkSeq` | |
| 4 | `chkPairs` | returns `(Env × Decls)` — two outputs, not three |
| 5 | `chkElems` | |
| 6 | `chkRescues` | returns `Option (List Ty)` — **no table**, so the motive is `True` |
| 7 | `chkArgs` | |
| 8 | `chkKwEntries` | two outputs |
| 9 | `chkBlockClaim` | |
| 10 | `chkRecv` | |

Motives 3, 5 and 7 have **identical types**, so a swapped assignment type-checks and
only the induction hypotheses' shapes reveal it. Measured: the first assignment had 5
and 7 exchanged, and it surfaced as a send case whose hypothesis was about `chkElems`
where the arm uses `chkArgs`. That is `Proof/Static/Mono.lean`'s L230 note — *"the
order is not the file's … measured with `trace_state`"* — recurring verbatim one layer
up. Motives 1 and 10 are ambiguous for the same reason.

**Two arms had to be given names before any law could reach them**, and both are in
V19: `chkOpt` (the optional-subterm computation) and `chkRecv` (a send's receiver). An
*inline* `match eo with …` becomes a case hypothesis of `chk.induct` whose scrutinee is
still `eo`, and in the arms whose enclosing pattern is a wildcard — a send whose block
is `some val` for an unconstrained `val` — there is no way to make it concrete. Named,
each gets a motive and the induction hypothesis covers it.

**What the uniform tactic reaches.** For the table-return law (*inside a method body
nothing grows the table*), `chk.induct` generates ~250 cases and

```lean
first
| trivial
| (intro hr ht τ Γ' D₀ h
   simp_all [chk, chkOpt, chkRecv, chkSeq, chkArgs, chkElems, chkPairs,
     chkKwEntries, chkBlockClaim]
   <closers>)
| (intro hr ht Γ' D₀ h; …)
```

closes all but a handful — with the motives assigned as above and every motive given
the same `ctx.ret.isSome → top = false →` prefix, including `chkBlockClaim`'s, which
does not need it but wants the uniform binder shape so the `first` dispatch is
reliable.

The residue is **not mathematical**: it is the `chkPairs`/`chkKwEntries` cases, which
need a three-link chain of induction hypotheses (`chkPairs` at `D₂`, the value at `D₁`,
the key at `D`) and where `simp_all` diverges — max steps, then max recursion, then
`isDefEq` heartbeats in turn, and at 40M heartbeats it does not terminate in ten
minutes. Those two motives want the chain applied *explicitly* rather than searched
for. Recorded at this grain because it is the next thing to write, not a thing to
rediscover.

**Three tactical facts, each of which cost a wrong turn:**

1. **`split at h`, not `cases`** on a scrutinee that is not a hypothesis — `cases`
   leaves `h` untouched and every later `simp` reports no progress.
2. **A generic `VarKind` blocks the head match.** `chk`'s arms are per-kind, so
   matching `.var _ _` leaves the match irreducible and `split` re-opens all 47 arms
   with impossible `heq` hypotheses. Same for `.vasgn`.
3. **`absurd h (by simp)` is not a finisher.** It elaborates and leaves its side goal
   open, so a `first` combinator treats it as a success and never reaches the branches
   after it — twenty-six arms failed silently that way. `simp at h; done` fails
   cleanly.

And one that is not about this proof but about writing any of them: **macro bodies are
hygienic.** An `ih` or `hr` written inside a `local macro` refers to a fresh `ih✝`, not
the caller's hypothesis, and the failure mode is a `first` branch that silently never
fires. Three separate wrong turns before it was written down; pass them as macro
parameters.

## What is proved here

`chkBlockClaim_table_ret` — the one law that needs no induction, because the claimed
block-send arm answers the table it was handed outright. Everything else waits on the
residue above.
-/

namespace RubyCore
namespace Proof
namespace Cert

open RubyCore.Types
open RubyCore.Cert

set_option maxHeartbeats 1000000

/-- **The claimed block-send arm returns the table it was handed**, unconditionally —
    no fuel hypothesis and no `ctx.ret` side condition, because the arm's answer is
    `some (cl.ty, Γ, D)`.

    Wanted as a standalone law rather than an induction case because `chk`'s block-send
    fallback is a bare `chkBlockClaim` application, with no `some (…)` wrapper for the
    injective-`some` step to see. -/
theorem chkBlockClaim_table_ret {c : Cert} {n : Nat} {top : Bool} {ctx : FrameCtx}
    {key : Expr} {D : Decls} {Γ : Env} {τs : List Ty} {ps : List Param}
    {ls : List String} {body : Expr} {τ : Ty} {Γ' : Env} {D₀ : Decls}
    (h : chkBlockClaim c n top ctx key D Γ τs ps ls body = some (τ, Γ', D₀)) :
    D₀ = D := by
  -- The fuel has to be cased first: `chkBlockClaim`'s own `match` is on it, so with
  -- `n` a variable `simp only [chkBlockClaim]` makes no progress. At zero fuel the arm
  -- is `none`, which refuses — the safe direction, as everywhere else.
  cases n with
  | zero => simp [chkBlockClaim] at h
  | succ m =>
    simp only [chkBlockClaim] at h
    (repeat' split at h) <;>
      first
      | (simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.2.symm)
      | (simp at h; done)

end Cert
end Proof
end RubyCore
