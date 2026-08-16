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
def LoopOk (D : Decls) (Γ : Env) (c body : Expr) (top : Bool := false) : Prop :=
  (∃ τc, infer D Γ c top = some (τc, Γ)) ∧ (∃ τb, infer D Γ body top = some (τb, Γ))

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
  /-- `seqK (e :: es)` discards the in-flight value and runs the rest.

      **`Γs.isEmpty` is the toplevel mode** (L155), and this is the only
      constructor that has to name it: `seqK` is the one kont that stores
      *unevaluated statements*, so it is the one whose contents may be a `class`.
      The mode is read off the environment stack rather than carried as an index
      because `frameK` — the constructor at which an activation's environment goes
      out of scope — is already exactly where the definee changes. -/
  | seqCons {h Γ Γs τ e es τ' Γ' k} :
      inferSeq D Γ (e :: es) Γs.isEmpty = some (τ', Γ') → KontOk D h (Γ' :: Γs) τ' k →
      KontOk D h (Γ :: Γs) τ (.seqK (e :: es) :: k)
  /-- Assignment binds `x` at the in-flight type and re-yields the value. -/
  | asgn {h Γ Γs τ x k} :
      KontOk D h (envSet Γ x τ :: Γs) τ k → KontOk D h (Γ :: Γs) τ (.asgnK .lvar x :: k)
  /-- The in-flight value is the condition; either branch may run next, so the
      join must be the one `inferIf` computed. -/
  | ifK {h Γ Γs τ t els τ' Γ' k} :
      inferIf D Γ t els Γs.isEmpty = some (τ', Γ') → KontOk D h (Γ' :: Γs) τ' k →
      KontOk D h (Γ :: Γs) τ (.ifK t els :: k)
  | whileCond {h Γ Γs τ c body k} :
      LoopOk D Γ c body Γs.isEmpty → KontOk D h (Γ :: Γs) .nilT k →
      KontOk D h (Γ :: Γs) τ (.whileCondK c body :: k)
  | whileBody {h Γ Γs τ c body k} :
      LoopOk D Γ c body Γs.isEmpty → KontOk D h (Γ :: Γs) .nilT k →
      KontOk D h (Γ :: Γs) τ (.whileBodyK c body :: k)
  /-- The in-flight value is the **receiver** of a binary builtin send; the
      argument expression runs next. The site is `.explicit` because `evalExpr`
      picks it syntactically and `infer` rejects `self` in receiver position. -/
  | recvK {h Γ Γs τ mname arg τp τret Γ₂ k} :
      sigOf D τ mname = some ([τp], τret) →
      infer D Γ arg Γs.isEmpty = some (τp, Γ₂) →
      KontOk D h (Γ₂ :: Γs) τret k →
      KontOk D h (Γ :: Γs) τ (.recvK mname [arg] .none .explicit :: k)
  /-- **A zero-argument send** (L152), and it is a separate constructor rather than
      `recvK` with an empty list because the two describe *different numbers of
      steps*. With an argument, `applyKont` pushes an `argsK` and the dispatch is a
      step away; with none, `startArgs … [] []` is `finishSend`, so the send completes
      **in this step** and the continuation `k` must already be typed at the return
      type. There is no `argsK` in the chain at all, and therefore no `ValueTy` stored
      in the kont — which is why this constructor, unlike `argsK`, does not read the
      heap. -/
  | recvK0 {h Γ Γs τ mname τret k} :
      sigOf D τ mname = some ([], τret) →
      KontOk D h (Γ :: Γs) τret k →
      KontOk D h (Γ :: Γs) τ (.recvK mname [] .none .explicit :: k)
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
  | .eval e =>
    ∃ τ Γ', infer D Γ e Γs.isEmpty = some (τ, Γ') ∧ KontOk D m.heap (Γ' :: Γs) τ m.kont
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
  | recvK0 hsg _ ih => exact .recvK0 hsg ih
  | argsK hv hsg _ ih => exact .argsK (ValueTy.congr ha hv) hsg ih
  | frameK _ ih => exact .frameK ih

/-- **The invariant** handed to `invariant_sound_from`.

    **`Saturated` is the third heap conjunct since L148**, and it is here for one
    reason: `DeclsOk_grow` — the invariant's own preservation across an allocating
    step — needs the ancestor walk to be fuel-saturated *at the heap the step starts
    from*, and only the invariant can carry a fact there. It is a heap clause of the
    same kind as `NoHook`: true at the boot heap by `decide`, true at the
    prelude-booted heap by the certificate `heapOkB` (L148 folded `saturatedB` into
    it), and preserved by every step that writes the heap
    (`Saturated_defineMethod`, `Saturated_grow`).

    It is *not* a fragment restriction. A program cannot make it false — nothing in
    the object model builds a cyclic `include` — but nothing in the `Heap` **type**
    forbids one either, which is why it cannot be a theorem.

    **`StrClsOk` is the fourth heap conjunct** (L151), and it is here for the
    producer: `infer` gives a string literal the type `.cls "String"`, which is a
    claim about a name, while the step allocates an object whose class is the id
    `Boot.stringId`. See its own docstring for why the join belongs in the
    invariant rather than at the use site.

    **`BottomObj` is the sixth conjunct** (L155), and it is the only one that is
    not about the heap: *the outermost activation's definee is `Object`.* It is
    what turns `infer`'s `top` flag from a decoration into a fact — `CtlOk` reads
    the mode as `Γs.isEmpty`, `FramesOk` makes that a singleton frame stack, and
    this names that frame's definee. Carried rather than derived because nothing
    in the `Machine` *type* says the bottom frame is the toplevel one; `initFrom`
    establishes it and every step preserves it. -/
def Inv (D : Decls) (m : Machine) : Prop :=
  DeclsOk D m.heap ∧ NoHook m.heap ∧ Saturated m.heap ∧ StrClsOk m.heap ∧
    ClassOk m.heap ∧ BottomObj m.frames m.stack ∧
    ∃ Γ Γs, FramesOk m.heap m.frames m.stack (Γ :: Γs) ∧ CtlOk D Γ Γs m

/-! ### Inversions used by the send cases -/

/-- The signature in the shape `EntryOk` reads it. Trivial, and it exists because
    `sigOf` is `declFor` composed with a projection while `DeclsOk` is stated over
    `declFor` — so the `argsK` case has to move between the two.

    **Generalized from `[τp]` to any `params` in L152**, because the zero-argument
    case needs it at `[]` and the two would otherwise be the same proof twice. -/
theorem sigOf_declFor {D : Decls} {τr : Ty} {mname : String} {params : List Ty}
    {τret : Ty} (h : sigOf D τr mname = some (params, τret)) :
    declFor D τr mname = some { params := params, ret := τret } := by
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
theorem site_explicit {D : Decls} {Γ : Env} {r : Expr} {x : Ty × Env} {top : Bool}
    (h : infer D Γ r top = some x) :
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
    {body : Expr} {τ : Ty} {Γ' : Env} {top : Bool}
    (h : infer D Γ (.def' name params body) top = some (τ, Γ')) :
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

/-- Inversion for the **class-reopen** rule (L156). The three side conditions come
    back out as separate facts because the consecution case spends them in three
    different places: `top` against `BottomObj`, `sup = none` against `evalExpr`'s
    own match, and membership against `ClassOk`. -/
theorem infer_class_inv {D : Decls} {Γ : Env} {name : String} {sup : Option Expr}
    {body : Expr} {τ : Ty} {Γ' : Env} {top : Bool}
    (h : infer D Γ (.class' name sup body) top = some (τ, Γ')) :
    top = true ∧ sup = none ∧ reopenableClasses.contains name = true ∧ Γ' = Γ ∧
      ∃ Γ'', infer D [] body = some (τ, Γ'') := by
  simp only [infer] at h
  split at h
  · next hc =>
    obtain ⟨ht, hs, hm⟩ := hc
    split at h
    · next τb Γb hb =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨ht, Option.isNone_iff_eq_none.mp hs, hm, rfl, Γb, hb⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Inversion for the **zero-argument** send rule (L152). One `split` shallower than
    its unary sibling, because there is no argument to infer and therefore no
    parameter-type equality to check — the output environment is the receiver's. -/
theorem infer_send0_inv {D : Decls} {Γ : Env} {r : Expr} {mname : String} {τ : Ty}
    {Γ' : Env} {top : Bool}
    (h : infer D Γ (.send (some r) mname [] none) top = some (τ, Γ')) :
    ∃ τr, infer D Γ r top = some (τr, Γ') ∧ sigOf D τr mname = some ([], τ) := by
  simp only [infer] at h
  split at h
  · next τr Γ₁ hr =>
    split at h
    · next τret hsg =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨τr, hr, hsg⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Inversion for the send rule. Factored out of `step_ok` because the nested
    `split at` needs `next`-bound names that are unreadable inline. -/
theorem infer_send_inv {D : Decls} {Γ : Env} {r arg : Expr} {mname : String} {τ : Ty}
    {Γ' : Env} {top : Bool}
    (h : infer D Γ (.send (some r) mname [arg] none) top = some (τ, Γ')) :
    ∃ τr Γ₁ τp, infer D Γ r top = some (τr, Γ₁) ∧
      sigOf D τr mname = some ([τp], τ) ∧
      infer D Γ₁ arg top = some (τp, Γ') := by
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
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : StrClsOk m.heap) (hcls : ClassOk m.heap)
    (hbot : BottomObj m.frames m.stack)
    (hinf : infer D Γ e Γs.isEmpty = some (τ, Γ'))
    (hk : KontOk D m.heap (Γ' :: Γs) τ m.kont) :
    Inv D (withCtl m (.eval e)) :=
  ⟨ht, hh, hsat, hstr, hcls, hbot, Γ, Γs, hfs, ⟨τ, Γ', hinf, hk⟩⟩

theorem inv_value {D : Decls} {m : Machine} {Γ : Env} {Γs : List Env} {v : Value}
    {τ : Ty}
    (hfs : FramesOk m.heap m.frames m.stack (Γ :: Γs)) (ht : DeclsOk D m.heap)
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : StrClsOk m.heap) (hcls : ClassOk m.heap)
    (hbot : BottomObj m.frames m.stack)
    (hv : ValueTy m.heap v τ) (hk : KontOk D m.heap (Γ :: Γs) τ m.kont) :
    Inv D (withCtl m (.value v)) :=
  ⟨ht, hh, hsat, hstr, hcls, hbot, Γ, Γs, hfs, ⟨τ, hv, hk⟩⟩

theorem inv_push {D : Decls} {m : Machine} {Γ : Env} {Γs : List Env} {e : Expr}
    {τ : Ty} {Γ' : Env} {k : Kont}
    (hfs : FramesOk m.heap m.frames m.stack (Γ :: Γs)) (ht : DeclsOk D m.heap)
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : StrClsOk m.heap) (hcls : ClassOk m.heap)
    (hbot : BottomObj m.frames m.stack)
    (hinf : infer D Γ e Γs.isEmpty = some (τ, Γ'))
    (hk : KontOk D m.heap (Γ' :: Γs) τ (k :: m.kont)) :
    Inv D (withKont m (.eval e) k) :=
  ⟨ht, hh, hsat, hstr, hcls, hbot, Γ, Γs, hfs, ⟨τ, Γ', hinf, hk⟩⟩

/-- **A freshly allocated non-class object has the class type its `klass` names**
    (L151). This is the *value* half of a producer's obligation — the half
    `inv_grow_value` deliberately left to the rule (`hv`, read in the **new** heap) —
    and it is stated once here because every producer owes exactly it: a string
    literal today, `.array` and `C.new` later, each differing only in which `klass`
    and which payload it pushes.

    The four hypotheses are `plainRecv`'s four conjuncts at the fresh id, each
    discharged from the object literal or from the invariant:
    the bound is free (the id is the one being pushed), `hpl` is a computation on the
    payload, `hk`/`hn` are the heap facts — which for `String` is exactly what the
    `StrClsOk` conjunct carries.

    `hpl` is three refutations rather than `plainRecv`'s own `match` because a `match`
    written in a *statement* elaborates to a fresh matcher constant, which then will
    not `rw` against the one `plainRecv` was compiled with. Case-splitting the payload
    is the shape that composes; `entry_dispatch` discharges the same three shapes the
    same way. -/
theorem valueTy_alloc_fresh {h : Heap} {obj : Object} {n : String}
    (hpl : (∀ c, obj.payload ≠ .proc c) ∧ (∀ xs, obj.payload ≠ .hsh xs) ∧
           (∀ c, obj.payload ≠ .cls c))
    (he : obj.eigen = none)
    (hk : (h.classPayload? obj.klass).isSome)
    (hn : className h obj.klass = n) :
    ValueTy ⟨h.objs.push obj⟩ (.ref h.objs.size) (.cls n) := by
  obtain ⟨hproc, hhsh, hnc⟩ := hpl
  have hg : PlainGrow h ⟨h.objs.push obj⟩ := plainGrow_alloc h obj hnc
  -- The fresh id reads back as the object that was pushed; everything else is a
  -- rewrite through `PlainGrow`, which pins `classPayload?` at *every* id.
  have hget : (Heap.get ⟨h.objs.push obj⟩ h.objs.size) = obj := by
    simp [Heap.get, Array.getD_eq_getD_getElem?]
  have hlt : h.objs.size < (Heap.mk (h.objs.push obj)).objs.size := by simp
  have hplain : plainRecv ⟨h.objs.push obj⟩ h.objs.size = true := by
    unfold plainRecv
    rw [hget, he, hg.payload obj.klass]
    cases hp : obj.payload
    case proc c => exact absurd hp (hproc c)
    case hsh xs => exact absurd hp (hhsh xs)
    case cls c => exact absurd hp (hnc c)
    all_goals simp [hlt, hk]
  show valueTy? _ _ = _
  simp only [valueTy?, hplain, if_true]
  rw [plainRecv_classOf hplain, hget, hg.className_eq obj.klass, hn]

/-- **The invariant survives a step that allocates a plain object** (L149) — which
    is the producer's consecution case with the rule removed, and therefore the
    statement that says how much of the producer is *not* about the producer.

    Every conjunct is discharged by a lemma of its own rung, and it is worth reading
    the list as a summary of what items 2–5 of the bill bought:

    | conjunct | discharged by | rung |
    |---|---|---|
    | `DeclsOk`   | `DeclsOk_grow`          | L147 (class-indexed resolution) |
    | `NoHook`    | `NoHook_grow`           | L149 |
    | `Saturated` | `Saturated_grow`        | L148 |
    | `FramesOk`  | `FramesOk.heap_congr` ∘ `typeAgree_of_plainGrow` | L143/L145 |
    | `CtlOk`     | `KontOk.heap_congr` ∘ the same | L143/L145 |

    What the *rule* still owes is only what a rule can owe: that the step really
    lands in a machine related to this one by `PlainGrow` with frames, stack and
    `kont` untouched, and that the value it produces has the type the rule assigns.
    `plainGrow_alloc` supplies the first for a non-class `Heap.alloc`.

    The produced value's type is read in the **new** heap (`hv`), which is the whole
    reason the transport had to be relativized rather than proved unrelativized
    (L143): the fresh object has no type in the old one. -/
theorem inv_grow_value {D : Decls} {m m' : Machine} {Γ : Env} {Γs : List Env}
    {v : Value} {τ : Ty}
    (hfs : FramesOk m.heap m.frames m.stack (Γ :: Γs)) (ht : DeclsOk D m.heap)
    (hh : NoHook m.heap) (hsat : Saturated m.heap) (hstr : StrClsOk m.heap) (hcls : ClassOk m.heap)
    (hbot : BottomObj m.frames m.stack)
    (hg : PlainGrow m.heap m'.heap)
    (hfr : m'.frames = m.frames) (hst : m'.stack = m.stack) (hko : m'.kont = m.kont)
    (hv : ValueTy m'.heap v τ) (hk : KontOk D m.heap (Γ :: Γs) τ m.kont) :
    Inv D (withCtl m' (.value v)) := by
  have hag : TypeAgree m.heap m'.heap := typeAgree_of_plainGrow hg
  refine ⟨DeclsOk_grow hg hsat ht, NoHook_grow hg hsat hh,
    Saturated_grow hg.shapeAgree hg.size hsat, StrClsOk_grow hg hstr,
    ClassOk_grow hg hcls,
    show BottomObj m'.frames m'.stack by rw [hfr, hst]; exact hbot, Γ, Γs, ?_, ?_⟩
  · show FramesOk m'.heap m'.frames m'.stack (Γ :: Γs)
    rw [hfr, hst]
    exact FramesOk.heap_congr hag hfs
  · show ∃ σ, ValueTy m'.heap v σ ∧ KontOk D m'.heap (Γ :: Γs) σ m'.kont
    exact ⟨τ, hv, by rw [hko]; exact KontOk.heap_congr hag hk⟩
end Static
end Proof
end RubyCore
