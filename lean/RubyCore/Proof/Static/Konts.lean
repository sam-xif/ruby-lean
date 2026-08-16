import RubyCore.Proof.Static.Decls

/-!
# P0 static soundness, part 2 — typing the machine

§2 of `Proof/StaticSoundness.lean` before the L136 split: `KontOk` (one
constructor per admitted continuation, and the *absence* of the other 39 is what
collapses preservation's case analysis), `CtlOk`, the two heap conditions
`TableOk`/`NoHook`, the invariant `Inv` itself, and the inversion lemmas the send
and `def` cases need.
-/

namespace RubyCore
namespace Proof
namespace Static

open Interp
open RubyCore.Types

set_option maxRecDepth 100000

/-! ## 2. Typing the machine

`KontOk h Γ τ k` reads: *the in-flight value has type `τ`, the environment is
`Γ`, and `k` is a well-typed continuation.* There is one constructor per
admitted `Kont` — five out of the machine's 48 (`Machine.lean:140`) — and the
absence of the other 43 is what makes preservation's case analysis collapse.
-/

/-- A `while` whose condition and body are both **environment-stable** at `Γ`.
    The loop re-enters the condition with whatever the body leaves, so without
    stability there is no single `Γ` to index the two loop konts by. -/
def LoopOk (D : Decls) (Γ : Env) (c body : Expr) : Prop :=
  (∃ τc, infer D Γ c = some (τc, Γ)) ∧ (∃ τb, infer D Γ body = some (τb, Γ))

/-- `KontOk h Γs τ k` reads: *in heap `h`, the in-flight value has type `τ`, the
    environment **stack** is `Γs` (innermost first), and `k` is a well-typed
    continuation.*

    The heap index arrived with L137 and is carried for one constructor only —
    `argsK`, which stores an already-evaluated **receiver** and therefore a
    `ValueTy` fact about a value the heap describes. It is the reason a
    heap-writing step now owes `KontOk.heap_congr`.

    The stack replaces P0's single environment because a method activation has
    its own locals: `frameK` — the kont `enterUserMethod` pushes
    (`Interp.lean:573`) and `applyKont` pops (`Interp.lean:2206`) — is exactly
    the marker at which one environment goes out of scope. Every other
    constructor operates on the head and passes the tail through untouched. -/
inductive KontOk (D : Decls) : Heap → List Env → Ty → List Kont → Prop where
  /-- Empty stack: the in-flight value is the program's result. -/
  | nil {h Γs τ} : KontOk D h Γs τ []
  /-- `seqK []` yields the in-flight value unchanged (`Interp.lean:1957`). -/
  | seqNil {h Γ Γs τ k} : KontOk D h (Γ :: Γs) τ k → KontOk D h (Γ :: Γs) τ (.seqK [] :: k)
  /-- `seqK (e :: es)` discards the in-flight value and runs the rest. -/
  | seqCons {h Γ Γs τ e es τ' Γ' k} :
      inferSeq D Γ (e :: es) = some (τ', Γ') → KontOk D h (Γ' :: Γs) τ' k →
      KontOk D h (Γ :: Γs) τ (.seqK (e :: es) :: k)
  /-- Assignment binds `x` at the in-flight type and re-yields the value. -/
  | asgn {h Γ Γs τ x k} :
      KontOk D h (envSet Γ x τ :: Γs) τ k → KontOk D h (Γ :: Γs) τ (.asgnK .lvar x :: k)
  /-- The in-flight value is the condition; either branch may run next, so the
      join must be the one `inferIf` computed. -/
  | ifK {h Γ Γs τ t els τ' Γ' k} :
      inferIf D Γ t els = some (τ', Γ') → KontOk D h (Γ' :: Γs) τ' k →
      KontOk D h (Γ :: Γs) τ (.ifK t els :: k)
  | whileCond {h Γ Γs τ c body k} :
      LoopOk D Γ c body → KontOk D h (Γ :: Γs) .nilT k →
      KontOk D h (Γ :: Γs) τ (.whileCondK c body :: k)
  | whileBody {h Γ Γs τ c body k} :
      LoopOk D Γ c body → KontOk D h (Γ :: Γs) .nilT k →
      KontOk D h (Γ :: Γs) τ (.whileBodyK c body :: k)
  /-- The in-flight value is the **receiver** of a binary builtin send; the
      argument expression runs next. The site is `.explicit` because `evalExpr`
      picks it syntactically and `infer` rejects `self` in receiver position. -/
  | recvK {h Γ Γs τ mname arg τp τret Γ₂ k} :
      sigOf D τ mname = some ([τp], τret) →
      infer D Γ arg = some (τp, Γ₂) →
      KontOk D h (Γ₂ :: Γs) τret k →
      KontOk D h (Γ :: Γs) τ (.recvK mname [arg] .none .explicit :: k)
  /-- The in-flight value is the **argument**; the receiver is already a value
      carried by the kont, so its type is pinned by `ValueTy` rather than by
      `infer`. -/
  | argsK {h Γ Γs τ mname recv τr τret k} :
      ValueTy h recv τr →
      sigOf D τr mname = some ([τ], τret) →
      KontOk D h (Γ :: Γs) τret k →
      KontOk D h (Γ :: Γs) τ (.argsK recv .explicit mname [] [] .none :: k)
  /-- **Method return.** The in-flight value is the body's value; popping the
      activation (`Interp.lean:2206`) discards the callee's environment and
      resumes the caller's.

      Note the **two-deep** env stack `Γ :: Γ' :: Γs`. A one-deep version would
      be provable-looking and wrong: `KontOk.nil` accepts *any* stack including
      `[]`, so `KontOk h (Γ :: []) τ (frameK :: [])` would be derivable, and
      popping it leaves a machine with no current environment for `CtlOk` to use.
      Requiring a caller environment to exist is what makes the pop total. -/
  | frameK {h Γ Γ' Γs τ fid k} :
      KontOk D h (Γ' :: Γs) τ k → KontOk D h (Γ :: Γ' :: Γs) τ (.frameK fid :: k)

/-- The control component. `.jump` is excluded outright: `break`/`next`/`return`
    are not in the fragment, so no step can produce one. -/
def CtlOk (D : Decls) (Γ : Env) (Γs : List Env) (m : Machine) : Prop :=
  match m.ctl with
  | .eval e => ∃ τ Γ', infer D Γ e = some (τ, Γ') ∧ KontOk D m.heap (Γ' :: Γs) τ m.kont
  | .value v => ∃ τ, ValueTy m.heap v τ ∧ KontOk D m.heap (Γ :: Γs) τ m.kont
  | .jump _ => False

/-- **Transport of the continuation judgement.** The other half of L137's cost:
    a heap-writing step must carry every `ValueTy` fact already stored in the
    continuation stack into the new heap. Only `argsK` stores one, so this is a
    one-case induction today — and it is the case that stops being trivial the
    moment `Ty` gains a nominal arm, which is the point of writing it now. -/
theorem KontOk.heap_congr {D : Decls} {h h' : Heap} (ha : TypeAgree h h') :
    ∀ {Γs : List Env} {τ : Ty} {k : List Kont}, KontOk D h Γs τ k → KontOk D h' Γs τ k := by
  intro Γs τ k hk
  induction hk with
  | nil => exact .nil
  | seqNil _ ih => exact .seqNil ih
  | seqCons hs _ ih => exact .seqCons hs ih
  | asgn _ ih => exact .asgn ih
  | ifK hi _ ih => exact .ifK hi ih
  | whileCond hl _ ih => exact .whileCond hl ih
  | whileBody hl _ ih => exact .whileBody hl ih
  | recvK hsg ha' _ ih => exact .recvK hsg ha' ih
  | argsK hv hsg _ ih => exact .argsK (ValueTy.congr ha hv) hsg ih
  | frameK _ ih => exact .frameK ih

/-- **The invariant** handed to `invariant_sound_from`. -/
def Inv (D : Decls) (m : Machine) : Prop :=
  DeclsOk D m.heap ∧ NoHook m.heap ∧
    ∃ Γ Γs, FramesOk m.heap m.frames m.stack (Γ :: Γs) ∧ CtlOk D Γ Γs m

/-! ### Inversions used by the send cases -/

/-- The signature in the shape `EntryOk` reads it. Trivial, and it exists because
    `sigOf` is `declFor` composed with a projection while `DeclsOk` is stated over
    `declFor` — so the `argsK` case has to move between the two. -/
theorem sigOf_declFor {D : Decls} {τr : Ty} {mname : String} {τp τret : Ty}
    (h : sigOf D τr mname = some ([τp], τret)) :
    declFor D τr mname = some { params := [τp], ret := τret } := by
  unfold sigOf at h
  cases hd : declFor D τr mname with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some d =>
    obtain ⟨ps, r⟩ := d
    rw [hd] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

/-- `evalExpr` chooses the send site *syntactically* from the receiver
    expression (`Interp.lean:2582`); `infer` rejects `self`, so the site is
    always `.explicit` in the fragment. -/
theorem site_explicit {D : Decls} {Γ : Env} {r : Expr} {x : Ty × Env}
    (h : infer D Γ r = some x) :
    (match r with | .self' => SendSite.selfRecv | _ => SendSite.explicit) = .explicit := by
  cases r <;> try rfl
  exact absurd h (by simp [infer])

/-- `Machine.currentFrame` and `curFrame` agree once the stack is non-empty. -/
theorem currentFrame_eq {m : Machine} (hne : m.stack ≠ []) :
    m.currentFrame = curFrame m := by
  cases hst : m.stack with
  | nil => exact absurd hst hne
  | cons fid _ => simp [Machine.currentFrame, curFrame, curFid, hst]

/-- Inversion for the `def` rule. -/
theorem infer_def_inv {D : Decls} {Γ : Env} {name : String} {params : List Param}
    {body : Expr} {τ : Ty} {Γ' : Env}
    (h : infer D Γ (.def' name params body) = some (τ, Γ')) :
    τ = .sym ∧ Γ' = Γ ∧ params = [] ∧ declaresName D name = false
      ∧ name ≠ "method_added" := by
  simp only [infer] at h
  split at h
  · next hc =>
    obtain ⟨hp, h1, h2⟩ := hc
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨h.1.symm, h.2.symm, List.isEmpty_iff.mp hp, h1, h2⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Inversion for the send rule. Factored out of `step_ok` because the nested
    `split at` needs `next`-bound names that are unreadable inline. -/
theorem infer_send_inv {D : Decls} {Γ : Env} {r arg : Expr} {mname : String} {τ : Ty}
    {Γ' : Env} (h : infer D Γ (.send (some r) mname [arg] none) = some (τ, Γ')) :
    ∃ τr Γ₁ τp, infer D Γ r = some (τr, Γ₁) ∧
      sigOf D τr mname = some ([τp], τ) ∧
      infer D Γ₁ arg = some (τp, Γ') := by
  simp only [infer] at h
  split at h
  · next τr Γ₁ hr =>
    split at h
    · next τp τret hsg =>
      split at h
      · next τa Γ₂ ha =>
        split at h
        · next hτ =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨τr, Γ₁, τp, hr, hsg, hτ ▸ ha⟩
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)


/-! ### 2.2 `FramesOk` survives the fragment's frame-preserving updates

`ctl` and `kont` updates leave `frames` and `stack` alone, and `FramesOk` reads
nothing else — so it transports by `rfl` rather than by a congruence lemma. That
is the payoff of phrasing conformance over the array and the stack instead of
over the machine: P0a needed `FrameOk_congr` *and* `LocalsOk_congr`, and both are
now gone.
-/

/-! ### 2.3 Building `Inv` for the machines the fragment steps to -/

theorem inv_eval {D : Decls} {m : Machine} {Γ : Env} {Γs : List Env} {e : Expr}
    {τ : Ty} {Γ' : Env}
    (hfs : FramesOk m.heap m.frames m.stack (Γ :: Γs)) (ht : DeclsOk D m.heap)
    (hh : NoHook m.heap)
    (hinf : infer D Γ e = some (τ, Γ')) (hk : KontOk D m.heap (Γ' :: Γs) τ m.kont) :
    Inv D (withCtl m (.eval e)) :=
  ⟨ht, hh, Γ, Γs, hfs, ⟨τ, Γ', hinf, hk⟩⟩

theorem inv_value {D : Decls} {m : Machine} {Γ : Env} {Γs : List Env} {v : Value}
    {τ : Ty}
    (hfs : FramesOk m.heap m.frames m.stack (Γ :: Γs)) (ht : DeclsOk D m.heap)
    (hh : NoHook m.heap)
    (hv : ValueTy m.heap v τ) (hk : KontOk D m.heap (Γ :: Γs) τ m.kont) :
    Inv D (withCtl m (.value v)) :=
  ⟨ht, hh, Γ, Γs, hfs, ⟨τ, hv, hk⟩⟩

theorem inv_push {D : Decls} {m : Machine} {Γ : Env} {Γs : List Env} {e : Expr}
    {τ : Ty} {Γ' : Env} {k : Kont}
    (hfs : FramesOk m.heap m.frames m.stack (Γ :: Γs)) (ht : DeclsOk D m.heap)
    (hh : NoHook m.heap)
    (hinf : infer D Γ e = some (τ, Γ'))
    (hk : KontOk D m.heap (Γ' :: Γs) τ (k :: m.kont)) :
    Inv D (withKont m (.eval e) k) :=
  ⟨ht, hh, Γ, Γs, hfs, ⟨τ, Γ', hinf, hk⟩⟩
end Static
end Proof
end RubyCore
