import RubyCore.Proof.TypeSafety
import RubyCore.Proof.HeapFacts

/-!
# RBI-conformance for the builtins the typed fragment calls

`docs/semantics/static-soundness-poc.md` §5. Every entry of
`Types/Decls.lean`'s `baseDecls` is a **claim about the model's own
implementation**, and this file discharges those claims: for each declared
signature, the interpreter's dispatch really does produce a value of the
declared type, in one step, without raising.

This is the obligation `typed-portion-safety.md` §6 names, arriving early
(§8.1(3) of the POC doc explains why it slipped from P0a to P0b). Our setting
is better off than Sorbet's: Sorbet trusts its RBIs with no runtime backstop,
whereas here the model *defines* the builtin, so conformance is a theorem.

## What is assumed, and what that costs

`IntBuiltinResolves` collects the **heap** facts a dispatch depends on — that
the method table still resolves the name to the builtin, publicly, unshadowed.
It is a hypothesis rather than a lemma because it is false in general: a program
may reopen `Integer` and redefine `+`. The fragment forbids that
(`static-soundness-poc.md` §6, "no class reopening"), and discharging the
hypothesis for the concrete booted heap is a separate, `native_decide`-shaped
job that must stay out of this file so the metatheorems keep their axiom
baseline — the same split `SorbetConcrete.lean` uses (L81).

Proof shape follows `T5.dispatch_progress`: `rw [invoke.eq_def]` then
`simp [invoke.invokeDispatch, …]`. Per L73, everything on this path must stay
kernel-reducible; the `Builtins.run` layer is `rfl`.
-/

namespace RubyCore
namespace Proof
namespace Static

open Interp

set_option maxRecDepth 20000

/-! ## 1. The builtin layer: `rfl` -/

theorem run_int_add (a b : Int) (m : Machine) :
    Builtins.run "Integer#+" (.int a) [.int b] m = .ok (.int (a + b)) m := rfl

theorem run_int_sub (a b : Int) (m : Machine) :
    Builtins.run "Integer#-" (.int a) [.int b] m = .ok (.int (a - b)) m := rfl

theorem run_int_mul (a b : Int) (m : Machine) :
    Builtins.run "Integer#*" (.int a) [.int b] m = .ok (.int (a * b)) m := rfl

/-- The first **nullary** one (L152). Still `rfl`, and note the rule's arity is
    carried by the *declaration* rather than by the builtin: `Integer#zero?` matches
    on the receiver and ignores `args` entirely (`Builtins/Numerics.lean:296`), so it
    is `baseDecls`'s `params := []` and `infer`'s zero-argument arm that make
    `1.zero?(5)` `unknown` rather than typed. -/
theorem run_int_zero (a : Int) (m : Machine) :
    Builtins.run "Integer#zero?" (.int a) [] m = .ok (.bool (a == 0)) m := rfl

/-! ## 2. The dispatch layer -/

/-- The heap facts an `Integer` builtin dispatch depends on: the table resolves
    `mname` on an integer receiver to `bid`, the entry is live and public, and
    neither the between-chain nor the prelude-suppression gate fires.

    `crubySingletonShadow` needs no clause — it is `none` by computation for a
    non-`ref` receiver (`Interp.lean:126`). P1's object receivers will need it. -/
def IntBuiltinResolves (h : Heap) (mname bid : String) : Prop :=
  ∃ owner md,
    lookup h (.int 0) mname = some (owner, md) ∧
    md.builtin = some bid ∧
    md.undefined = false ∧
    md.visibility = .pub ∧
    md.fromPrelude = false ∧
    crubyShadow h ((ancestors h Boot.integerId).takeWhile (· != owner)) mname = none

/-- `lookup` on an immediate consults only `classOf`, which is `Boot.integerId`
    for every `.int` (`Heap.lean:396`), so resolution does not depend on the
    integer's value. -/
theorem lookup_int_const (h : Heap) (a : Int) (mname : String) :
    lookup h (.int a) mname = lookup h (.int 0) mname := rfl

/-- **The conformance step.** With the receiver and the argument both already
    values, the dispatch yields the declared result in one `.next` — no raise,
    which makes this discharge a progress obligation as much as a preservation
    one.

    Stated at the `startArgs` level rather than about `stepFn`: conformance is a
    fact about *dispatch*, and the caller (`StaticSoundness.step_ok`) has by then
    already unfolded `applyKont`, so a `stepFn`-shaped statement would not
    compose. -/
theorem int_bin_dispatch
    {m : Machine} {a b : Int} {mname bid : String} {op : Int → Int → Int}
    (hres : IntBuiltinResolves m.heap mname bid)
    (hns : (mname == "send" || mname == "public_send" || mname == "__send__") = false)
    (hrun : ∀ (x y : Int) (m' : Machine),
        Builtins.run bid (.int x) [.int y] m' = .ok (.int (op x y)) m')
    -- L116 put a **prelude-twin deferral** in front of every builtin: one whose
    -- answer would need a dispatch it cannot perform hands the call to a prelude
    -- method instead of running (repr purity, and L123's coerce protocol).
    -- Arithmetic over two Integers is never such a call, but the *statement* has to
    -- say so — leaving it implicit is what broke this proof, and `Proof/` being off
    -- the default target is why nothing noticed (L119).
    (hdefer : Builtins.deferTwin? m.heap bid (.int a) [.int b] = none) :
    startArgs m (.int a) .explicit mname [.int b] [] .none
      = .next (withCtl m (.value (.int (op a b)))) := by
  obtain ⟨owner, md, hlook, hb, hu, hvis, hpre, hbtw⟩ := hres
  rw [lookup_int_const m.heap 0 mname] at hlook
  simp only [startArgs, finishSend]
  rw [invoke.eq_def]
  simp [invoke.invokeDispatch, classOf, lookup_int_const, hlook, hb, hu, hbtw, hpre,
    visError?, hvis, appendKwHash, hrun, hns, hdefer]

/-! ### 2.1 The three table entries -/

theorem int_add_dispatch {m : Machine} {a b : Int}
    (hres : IntBuiltinResolves m.heap "+" "Integer#+") :
    startArgs m (.int a) .explicit "+" [.int b] [] .none
      = .next (withCtl m (.value (.int (a + b)))) :=
  int_bin_dispatch hres (by decide) run_int_add (by simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?, Builtins.toAryDefer?, Builtins.num?])

theorem int_sub_dispatch {m : Machine} {a b : Int}
    (hres : IntBuiltinResolves m.heap "-" "Integer#-") :
    startArgs m (.int a) .explicit "-" [.int b] [] .none
      = .next (withCtl m (.value (.int (a - b)))) :=
  int_bin_dispatch hres (by decide) run_int_sub (by simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?, Builtins.toAryDefer?, Builtins.num?])

theorem int_mul_dispatch {m : Machine} {a b : Int}
    (hres : IntBuiltinResolves m.heap "*" "Integer#*") :
    startArgs m (.int a) .explicit "*" [.int b] [] .none
      = .next (withCtl m (.value (.int (a * b)))) :=
  int_bin_dispatch hres (by decide) run_int_mul (by simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?, Builtins.toAryDefer?, Builtins.num?])

/-! ## 3. Starting argument evaluation

The cheap half of the send path: no heap facts, since nothing has dispatched
yet. The four excluded argument shapes are `startArgs`' own special cases
(`Interp.lean:1832`), and the fragment cannot express any of them — which is
why the side condition is discharged from `infer` succeeding rather than
carried by the caller.
-/

theorem startArgs_plain {m : Machine} {arg : Expr} {recv : Value} {acc : List Value}
    {rest : List Expr} {site : SendSite} {mname : String}
    (hsplat : ∀ e, arg ≠ .splat e) (hkw : ∀ es, arg ≠ .kwargs es) (hfwd : arg ≠ .fwd) :
    startArgs m recv site mname acc (arg :: rest) .none
      = .next (withKont m (.eval arg) (.argsK recv site mname acc rest .none)) := by
  cases arg <;> simp_all [startArgs]

/-- The same, for `super` (L212). `startSuperArgs` has `startArgs`' three refusals —
    a splat, keywords, and `...` forwarding — and no receiver or site to carry. -/
theorem startSuperArgs_plain {m : Machine} {arg : Expr} {acc : List Value}
    {rest : List Expr} {blk : Option Value}
    (hsplat : ∀ e, arg ≠ .splat e) (hkw : ∀ es, arg ≠ .kwargs es) (hfwd : arg ≠ .fwd) :
    startSuperArgs m acc (arg :: rest) blk
      = .next (withKont m (.eval arg) (.superArgK acc rest blk)) := by
  cases arg <;> simp_all [startSuperArgs]

/-! ## 4. Surviving a user `def`

`IntBuiltinResolves` is a *heap* condition, so any step that writes the method
table has to preserve it. The `defineMethod` chain is proved in
`Proof/HeapFacts.lean`; this is its application, and the side condition
(`mname ≠ name`) is the one the fragment can supply syntactically by forbidding a
`def` of any name the declaration table declares (`Types.declaresName`).
-/

theorem crubyShadow_defineMethod (h : Heap) (cls : ObjId) (name mname : String)
    (md : MethodDef) (chain : List ObjId) :
    crubyShadow (defineMethod h cls name md) chain mname
      = crubyShadow h chain mname := by
  unfold crubyShadow
  simp only [className_defineMethod]

theorem IntBuiltinResolves_defineMethod {h : Heap} {mname bid : String}
    {cls : ObjId} {name : String} {md : MethodDef}
    (hres : IntBuiltinResolves h mname bid) (hne : ¬ (mname = name)) :
    IntBuiltinResolves (defineMethod h cls name md) mname bid := by
  obtain ⟨owner, md0, hlook, hb, hu, hvis, hpre, hbtw⟩ := hres
  refine ⟨owner, md0, ?_, hb, hu, hvis, hpre, ?_⟩
  · rw [lookup_defineMethod h cls name mname md (.int 0) hne rfl]; exact hlook
  · rw [ancestors_defineMethod, crubyShadow_defineMethod]; exact hbtw

end Static
end Proof
end RubyCore
