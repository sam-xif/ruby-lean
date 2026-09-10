import Denote.Rules.Alloc
import Denote.Sem.Obligations

/-!
# `Denote/Rules/Lambda.lean` — `lambda { … }`, the rung that made the spine a lookup

`Judge.lambdaLit` is the ladder's first **higher-order** conclusion: the value it types is a
Proc, and the type records what the Proc *captured* — `.clos idx (envToSpine Γ)
(κ.selfTy.getD .never)`. Three things about the rung, in the order they cost work.

## 1. It is a two-step allocating run, and the second literal shape `ext_push` serves

`evalExpr`'s `.send` arm with a block literal builds `PendingBlk.lit`, `startArgs` at an empty
argument list goes straight to `finishSend`, and `finishSend`'s `.lit` arm answers
`.next (withCtl … (.value v))` for an implicit-self `lambda`/`proc` — with `reifyBlock`
having pushed one `Proc` object. So the whole run is `evals_pure` at an `Ext`, exactly as
`Judge.strLit` and `Judge.regexpLit` are, and the `Ext` is `ext_push` at a `.proc` payload.
`CoreOk` grew one row for it (`procBasic`), which is the third time that structure's docstring
has predicted its own growth correctly.

## 2. `nameFree` is spent here, and it is spent against `NameFreeOk`

The rule's premise (`found-issues.md` §F2, clink 49) is that the program has not defined a
method called `lambda`. `finishSend` tests the same thing on the *machine* —
`md.builtin.isNone && !md.undefined` at `methodOn (classOf recv) mname` — and `NameFreeOk`
(clink 51) is the component that connects them: at a name in `shadowableNames`, any method
the chain carries is a builtin, a tombstone, or one `κ` records. `nameFree` says `κ` records
none, so `shadowed` is `false` and the special case fires. `nameFree_declaresName` is the one
new lemma: the checker's `find?`-shaped predicate and the component's `any`-shaped one are
negations of each other.

## 3. The conclusion is where the tenth stall point came from

`denM`'s `.clos` arm asks for `denSpine (envToSpine Γ) m' (closLocal m' cl)`, and *that* is
what forced `denSpineFrom`'s accumulator (`Denote/Den.lean`, `Denote/Sem/notes.md` §The tenth
stall point): `EnvOk` is stated at `envGet?`, which reads the **first** binding for a name,
while `envToSpine` copies **every** entry — and the checker really does build environments with
a repeated key (`Judge.closCall` types a body in `paramEnv … ++ spineToEnv cap`). With the
old all-entries reading this obligation was false, not merely unprovable, and the machines that
falsified it were the ones `StateOk` should have described.

With the accumulator the two line up exactly, and `denSpineFrom_envToSpine` below is that
alignment: the accumulator holds the keys of the prefix already walked, so "not shadowed" and
"`envGet?` finds this entry" are the same condition, and the induction carries the prefix.

`closLocal m' cl` is the captured frame's reader, and `reifyBlock` captures the *current*
frame — so the function the spine is read through is `m.getLocal` itself, which is what `EnvOk`
speaks about. `frameLocal_head` is that step (two copies of one walk, from the same frame).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Ratchet.Denote

open RubyCore

/-! ## `envGet?` and the spine accumulator are the same condition -/

/-- A name the prefix does not bind is looked up in the tail. One induction on the prefix. -/
theorem envGet?_append_of_notMem : ∀ (pre : Env) {x : String} {τ : Ty} {Γ : Env},
    x ∉ pre.map Prod.fst → envGet? (pre ++ (x, τ) :: Γ) x = some τ
  | [], x, τ, Γ, _ => by simp [envGet?]
  | (y, σ) :: pre, x, τ, Γ, hx => by
    have hy : ¬ (y = x) := by
      intro h; exact hx (by simp [h])
    have hb : (y == x) = false := by simpa using hy
    simp only [List.cons_append, envGet?, List.find?, hb]
    exact envGet?_append_of_notMem pre (fun h => hx (by simp [h]))

/-- **The captured spine denotes, because `EnvOk` and `envToSpine` read the environment the
same way.** `seen` carries the keys of the prefix already walked, so an entry the accumulator
skips is exactly an entry `envGet?` would not have found. -/
theorem denSpineFrom_envToSpine {m : Machine} : ∀ (Γ pre : Env) (seen : List String),
    EnvOk (pre ++ Γ) m → (∀ y ∈ pre.map Prod.fst, y ∈ seen) →
    denSpineFrom seen (envToSpine Γ) m (fun x => m.getLocal x)
  | [], _, _, _, _ => by simp [envToSpine, denSpineFrom]
  | (x, τ) :: Γ, pre, seen, henv, hpre => by
    rw [envToSpine, denSpineFrom]
    refine ⟨?_, ?_⟩
    · by_cases hx : x ∈ seen
      · exact Or.inl hx
      · exact Or.inr (henv.1 x τ (envGet?_append_of_notMem pre (fun h => hx (hpre x h)))).1
    · refine denSpineFrom_envToSpine Γ (pre ++ [(x, τ)]) (x :: seen) ?_ ?_
      · simpa using henv
      · intro y hy
        simp only [List.map_append, List.mem_append, List.map_cons, List.map_nil,
          List.mem_singleton] at hy
        rcases hy with hy | hy
        · exact List.mem_cons_of_mem _ (hpre y hy)
        · simp [hy]

/-! ## The captured frame is the current one -/

/-- `frameLocal` and `Machine.getLocal` are one walk written twice; started from the frame
`getLocal` starts from, they agree. -/
theorem frameLocal_go_getLocal_go (m : Machine) (x : String) :
    ∀ (fuel : Nat) (fid : FrameId),
      frameLocal.go m x fid fuel = Machine.getLocal.go m x fid fuel := by
  intro fuel
  induction fuel with
  | zero => intro fid; rfl
  | succ n ih =>
    intro fid
    simp only [frameLocal.go, Machine.getLocal.go]
    cases (m.frames.getD fid default).locals.find? (fun p => p.1 == x) with
    | some p => rfl
    | none =>
      cases (m.frames.getD fid default).captured with
      | some q => exact ih q
      | none => rfl

theorem frameLocal_head (m : Machine) (x : String) :
    frameLocal m (m.stack.headD 0) x = m.getLocal x :=
  frameLocal_go_getLocal_go m x _ _

/-- `returnTarget` reads the frame stack and the frame array, so `evalFrom`'s rewrite of
`ctl`/`kont` leaves the closure's `home` where it was. -/
@[simp] theorem returnTarget_reCtl (m : Machine) (c : Ctl) (k : List Kont) :
    Interp.returnTarget (reCtl m c k) = Interp.returnTarget m := rfl

/-! ## The escape and the premise are now the same fact

`NameFreeOk`'s escape used to be `declaresName κ n = true`, read off `κ.defs`/`κ.classes`, while
the rule's premise was `nameFree κ n = true`, read off the same two tables — so the two had to
be related by a lemma, and both were wrong together at a program with a buried `def`
(`found-issues.md` §F20). Both are now the one whole-program fact `Neg` carries
(`context-splitting.md` §2.2), so what was a lemma is a rewrite. -/

theorem nameFree_declaresName {κ : Ctx} {n : String} (h : nameFreeN κ n = true) :
    nameFreeN κ n = false ↔ False := by simp [h]

/-! ## The step -/

/-- The closure `reifyBlock` builds: this block's parameters and body, capturing the
**current** frame (which is why the spine below is read through `m.getLocal`). -/
def lamClos (m : Machine) (ps : List RubyCore.Param) (body : RubyCore.Expr) (lam : Bool) :
    Closure :=
  { params := ps, locals := [], body, captured := some (m.stack.headD 0),
    home := Interp.returnTarget m, lam }

/-- The `Proc` object `reifyBlock` pushes. -/
def lamObj (m : Machine) (ps : List RubyCore.Param) (body : RubyCore.Expr) (lam : Bool) :
    Object :=
  { klass := Boot.procId, payload := .proc (lamClos m ps body lam) }

/-- The machine after the push. -/
def lamMachine (m : Machine) (ps : List RubyCore.Param) (body : RubyCore.Expr) (lam : Bool) :
    Machine := { m with heap := pushHeap m.heap (lamObj m ps body lam) }

/-- **One `stepFn` step from `evalFrom` to the reified Proc.** The `shadowed` test is the
hypothesis: given that the chain carries no *user* method of this name, `finishSend`'s
`lambda`/`proc` special case fires and the step is `withCtl` of the pushed Proc. -/
theorem stepFn_lambdaLit (m : Machine) (n : String) (hn : n = "lambda" ∨ n = "proc")
    (ps : List Ratchet.Param) (body : Ratchet.Expr)
    (hsh : ∀ o md, Interp.methodOn m.heap (classOf m.heap m.currentFrame.self) n = some (o, md) →
        (md.builtin.isNone && !md.undefined) = false) :
    ∃ lam, Interp.stepFn (evalFrom m (.send none n [] (some (.block ps [] body)))) =
      .next (reCtl (lamMachine m (toRubyParams ps) (toRuby body) lam)
        (.value (.ref m.heap.objs.size)) []) := by
  -- `hsh` is spent inside the `split`s below: `finishSend`'s `shadowed` test is a `match` on
  -- exactly the `methodOn` walk it constrains, so the branch where a *user* method shadows
  -- `lambda` is the branch `hsh` refutes.
  rcases hn with rfl | rfl <;>
    simp only [evalFrom, toRuby, toRubyOpt, toRubyList, Interp.stepFn, Interp.evalExpr,
      Interp.startArgs, Interp.finishSend, Interp.reifyBlock, Interp.withCtl,
      currentFrame_reCtl, heap_reCtl, stack_reCtl, Heap.alloc, lamObj, lamMachine,
      pushHeap, reCtl, returnTarget_reCtl, lamClos] <;> (repeat' split) <;>
    first | exact ⟨_, rfl⟩ | simp_all

/-! ## The rung -/

/-- The `Ext` the step is: one `Proc` pushed. `CoreOk` is spent twice — `basicSelf` on the
dangling-read clause and the new `procBasic` on the descendant clause — and `HeapSaturated`
on the `ancestors` clause, exactly as `Judge.strLit` spends them. -/
theorem ext_lamPush {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} (hm : StateOk κ Γ I m)
    (ps : List RubyCore.Param) (body : RubyCore.Expr) (lam : Bool) :
    Ext m (lamMachine m ps body lam) :=
  ext_push _ hm.sat hm.core.basicSelf (fun _ => by simp [lamObj])
    (by simp [lamObj]) (by simp [lamObj]) hm.core.procBasic

theorem Sem.Judge.lambdaLit : Obl.Judge.lambdaLit := by
  intro κ Γ I n ps body idx hn _hidx hfree _hret
  first
    | refine ⟨by first | trivial | simp [PlainAll, Plain]
                       | simp_all [PlainAll, Plain], ?_⟩
    | skip
  intro m hm v m' hev
  -- The machine-side reading of `nameFree`: `NameFreeOk` at a `shadowableNames` entry, with
  -- the `nameFreeN` escape closed by the rule's own premise.
  have hsh : ∀ o md, Interp.methodOn m.heap (classOf m.heap m.currentFrame.self) n
      = some (o, md) → (md.builtin.isNone && !md.undefined) = false := by
    intro o md hmo
    have hn' : n ∈ shadowableNames := by
      rcases hn with rfl | rfl <;> simp [shadowableNames]
    rcases hm.nameFree n hn' o md hmo with h | h | h
    · have : md.builtin.isNone = false := by
        cases hb : md.builtin with
        | none => rw [hb] at h; simp at h
        | some _ => rfl
      simp [this]
    · simp [h]
    · exact absurd h (by simp [hfree])
  obtain ⟨lam, hstep⟩ := stepFn_lambdaLit m n hn ps body hsh
  obtain ⟨rfl, rfl⟩ := evals_pure hstep hev
  have he : Ext m (lamMachine m (toRubyParams ps) (toRuby body) lam) :=
    ext_lamPush hm _ _ _
  refine ⟨(Framed.of_ext he).trans (Framed_reCtl _ _ _), ?_,
    StateOk_reCtl (StateOk_ext hm he) _ _, StateOk_reCtl (StateOk_ext hm he) _ _⟩
  -- The value is the pushed Proc, and its closure is the one `reifyBlock` built.
  refine denM_reCtl.mpr ?_
  rw [denM]
  refine ⟨lamClos m (toRubyParams ps) (toRuby body) lam, ?_, ?_, ?_⟩
  · simp [procClosure?, lamMachine, lamObj, pushHeap_get_self]
  · -- The captured spine: `closLocal` at the *current* frame is `m.getLocal`, which is what
    -- `EnvOk` speaks about, and `denSpineFrom`'s accumulator is `envGet?`'s "first match".
    have hloc : closLocal (lamMachine m (toRubyParams ps) (toRuby body) lam)
        (lamClos m (toRubyParams ps) (toRuby body) lam) = fun x => m.getLocal x := by
      funext x
      simp only [closLocal, lamClos, frameLocal?]
      rw [he.frameLocal_eq]
      exact frameLocal_head m x
    rw [hloc]
    exact (denM_ext_aux he (envToSpine Γ)).2 [] _
      (denSpineFrom_envToSpine Γ [] [] (by simpa using hm.env) (by simp))
  · -- `self`: the closure sees the creating frame's, which is the frame `SelfTyOk` is about.
    cases hst : κ.selfTy with
    | none => exact Or.inl (by simp)
    | some σ =>
      refine Or.inr ?_
      have hself : denM σ m m.currentFrame.self := by
        have := hm.selfTy; unfold SelfTyOk at this; rw [hst] at this; exact this
      -- `closSelf` reads the *captured* frame by id, `SelfTyOk` reads `currentFrame`; the
      -- two agree because `reifyBlock` captured the current frame, and that they are the
      -- same frame is `FrameInRange`'s non-emptiness conjunct.
      have : closSelf (lamMachine m (toRubyParams ps) (toRuby body) lam)
          (lamClos m (toRubyParams ps) (toRuby body) lam) = m.currentFrame.self := by
        simp only [closSelf, lamClos, lamMachine, Option.getD_some]
        rw [currentFrame_headD hm.frameInRange.1]
      rw [Option.getD_some, this]
      exact denM_ext he hself

#print axioms Sem.Judge.lambdaLit

end Ratchet.Denote
