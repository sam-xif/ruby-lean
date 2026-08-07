import RubyCore.Proof.TypeSafety

/-!
# RBI-conformance for the builtins the typed fragment calls

`docs/semantics/static-soundness-poc.md` §5. Every entry of
`Types/Core.lean`'s `builtinSig` is a **claim about the model's own
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

/-- **The conformance step.** With the last argument in flight and the receiver
    already evaluated, one `stepFn` yields the declared result — `.next`, so no
    raise, which is what makes this discharge a progress obligation as well as a
    preservation one. -/
theorem int_bin_step
    {m : Machine} {a b : Int} {mname bid : String} {op : Int → Int → Int}
    {rest : List Kont}
    (hctl : m.ctl = .value (.int b))
    (hk : m.kont = .argsK (.int a) .explicit mname [] [] .none :: rest)
    (hres : IntBuiltinResolves m.heap mname bid)
    (hns : (mname == "send" || mname == "public_send" || mname == "__send__") = false)
    (hrun : ∀ (x y : Int) (m' : Machine),
        Builtins.run bid (.int x) [.int y] m' = .ok (.int (op x y)) m') :
    stepFn m = .next (withCtl { m with kont := rest } (.value (.int (op a b)))) := by
  obtain ⟨owner, md, hlook, hb, hu, hvis, hpre, hbtw⟩ := hres
  rw [lookup_int_const m.heap 0 mname] at hlook
  simp only [stepFn, hctl, applyKont, hk, startArgs, finishSend]
  rw [invoke.eq_def]
  simp [invoke.invokeDispatch, classOf, lookup_int_const, hlook, hb, hu, hbtw, hpre,
    visError?, hvis, appendKwHash, hrun, hns]

/-! ### 2.1 The three table entries -/

theorem int_add_step {m : Machine} {a b : Int} {rest : List Kont}
    (hctl : m.ctl = .value (.int b))
    (hk : m.kont = .argsK (.int a) .explicit "+" [] [] .none :: rest)
    (hres : IntBuiltinResolves m.heap "+" "Integer#+") :
    stepFn m = .next (withCtl { m with kont := rest } (.value (.int (a + b)))) :=
  int_bin_step hctl hk hres (by decide) run_int_add

theorem int_sub_step {m : Machine} {a b : Int} {rest : List Kont}
    (hctl : m.ctl = .value (.int b))
    (hk : m.kont = .argsK (.int a) .explicit "-" [] [] .none :: rest)
    (hres : IntBuiltinResolves m.heap "-" "Integer#-") :
    stepFn m = .next (withCtl { m with kont := rest } (.value (.int (a - b)))) :=
  int_bin_step hctl hk hres (by decide) run_int_sub

theorem int_mul_step {m : Machine} {a b : Int} {rest : List Kont}
    (hctl : m.ctl = .value (.int b))
    (hk : m.kont = .argsK (.int a) .explicit "*" [] [] .none :: rest)
    (hres : IntBuiltinResolves m.heap "*" "Integer#*") :
    stepFn m = .next (withCtl { m with kont := rest } (.value (.int (a * b)))) :=
  int_bin_step hctl hk hres (by decide) run_int_mul

/-! ## 3. The receiver step

`recvK` needs no heap facts at all — it only starts argument evaluation. Split
out because it is the cheap half and the preservation proof needs it separately.
-/

theorem recv_step {m : Machine} {v : Value} {mname : String} {arg : Expr}
    {rest : List Kont}
    (hctl : m.ctl = .value v)
    (hk : m.kont = .recvK mname [arg] .none .explicit :: rest)
    (harg : ∀ ps ls b, arg ≠ .block ps ls b)
    (harg2 : ∀ e, arg ≠ .splat e)
    (harg3 : ∀ es, arg ≠ .kwargs es)
    (harg4 : arg ≠ .fwd) :
    stepFn m =
      .next (withKont { m with kont := rest } (.eval arg)
              (.argsK v .explicit mname [] [] .none)) := by
  simp only [stepFn, hctl, applyKont, hk, startArgs]
  cases arg <;> simp_all

end Static
end Proof
end RubyCore
