import RubyCore.Proof.TypeSafety
import RubyCore.Proof.Static.Locals
import RubyCore.Types.LambdaArrow

/-!
# Typed lambdas — the semantic layer (`docs/semantics/typed-lambdas-plan.md` L3)

`LamTy` is the reachability meaning of "this heap object is a `dom → cod`
lambda" (plan §0 item 1): a fact about the real machine, mentioning no
checker. `Types.TL.chk` (`Types/LambdaArrow.lean`) is the *syntactic
admission route*; `lamTy_of_capture_read` below is a *direct semantic* one
(plan §3, "prove `SemFrame`/the semantic fact by hand … the J31 pilot pattern
verbatim") — discharged by chasing the concrete step chain a captured-variable
read takes, not by an inductive invariant over a growing declaration table.
There is no such table here: `Types.TL.chkTop` closes its `RetTable` once, up
front (`Types/LambdaArrow.lean`'s header), so nothing about this file needs
`Inv`, `CtlOk`/`DeclsOk`, or any of `Types/Core.lean`'s machinery. The whole
vocabulary is `ValueTy`/`ValuesTy`/`FrameConforms`/`ShallowChain`/`localOfIn`
(`Proof/Static/Locals.lean`) and `Reaches`/`SmallStep` (`Proof/TypeSafety.lean`)
— neither file mentions `infer`/`Decls`, so this is genuinely a second,
independent semantic development, not a rider on the P0 invariant.

**Scope, honestly**: `lamTy_of_capture_read` proves `LamTy` for the *shape* of
closure the plan's forcing example needs — an arbitrary-arity lambda whose
body is a bare read of one variable captured from the enclosing frame,
untouched by the parameters (`comparator_for`'s `tiebreak`) — not an
induction over every shape `Types.TL.chk`'s body-checker could in principle
admit. A general body-checker soundness theorem (structural induction on
`chk`'s rules) is future work the plan's own §5 leaves open; this is the
"direct semantic proof" admission route the design explicitly allows instead,
sized to what the distilled example actually needs.
-/

namespace RubyCore.Proof.Static

open Interp Types

/-! ## 1. `ValuesTy` weakens pointwise (needed by the variance lemma) -/

theorem ValuesTy.weaken {h : Heap} : ∀ {vs : List Value} {σs τs : List Ty},
    ValuesTy h vs σs → subTys σs τs = true → ValuesTy h vs τs
  | [], [], [], _, hst => by simp [subTys] at hst; simp [ValuesTy]
  | [], [], _ :: _, _, hst => by simp [subTys] at hst
  | [], _ :: _, _, hv, _ => by simp [ValuesTy] at hv
  | _ :: _, [], _, hv, _ => by simp [ValuesTy] at hv
  | v :: vs, σ :: σs, [], hv, hst => by simp [subTys] at hst
  | v :: vs, σ :: σs, τ :: τs, hv, hst => by
    simp only [ValuesTy] at hv
    obtain ⟨⟨σ', hσ, hσσ'⟩, hrest⟩ := hv
    simp only [subTys, Bool.and_eq_true] at hst
    exact ⟨⟨σ', hσ, subTy_trans hσσ' hst.1⟩, ValuesTy.weaken hrest hst.2⟩

/-! ## 2. `LamTy` -/

/-- **The reachability meaning of a `dom → cod` lambda** (plan §0 item 1).
    `Γcap` is the types the *captured* frame's locals are claimed to have —
    supplied by whoever admits the fact, not carried by `LamTy` itself.
    `hcap`/`hshallow` are the two side-conditions every real closure's
    `captured` id satisfies by construction (the frame it names exists and is
    itself not a block) — `ShallowChain`'s own docstring's "the weakest
    replacement that keeps `localOfIn` an honest description of `getLocal`".

    The conclusion is deliberately **not** "no type-stuck outcome is
    reachable from the post-call state" — that state's continuation is
    whatever the *caller* was doing before the call, which this closure has
    no say over. It is "the call returns": some reachable state has the
    activation stack and continuation exactly restored to their pre-call
    shape, control holding a value, that value typed at `cod`. Since `stepFn`
    is a total *function* (one successor per state, `Interp.lean`'s own
    header), exhibiting *one* such reachable state is the whole story for
    this closure — there is no other branch to also rule out. -/
def LamTy (Γcap : Env) (dom : List Ty) (cod : Ty) (p : ObjId) : Prop :=
  ∀ (m : Machine) (c : Closure) (args : List Value) (brk : Option FrameId) (m' : Machine)
    (fcap : FrameId),
    (m.heap.get p).payload = .proc c →
    c.lam = true →
    -- **The captured frame, named** (L266). `Closure.captured` became an `Option`, so
    -- "the frame this closure closes over" is a hypothesis rather than a projection, and
    -- the three clauses below are about `fcap` instead of about `c.captured` coerced to a
    -- `Nat`. The scope this costs is exactly the capture-free closures — which is to say
    -- the two `Symbol#to_proc` sites, the only source of `captured = none` in the model —
    -- and `LamTy` says nothing about those. That is the honest reading and not a
    -- weakening in substance: with `captured = none` there *is* no frame for `Γcap` to
    -- describe, and the old statement silently pointed `Γcap` at frame `0`.
    c.captured = some fcap →
    fcap < m.frames.size →
    (m.frames.getD fcap default).captured = none →
    FrameConforms m.heap m.frames Γcap fcap →
    ValuesTy m.heap args dom →
    callClosure m c args brk = .next m' →
    ∃ (v : Value) (m'' : Machine), Reaches m' m'' ∧
      m''.stack = m.stack ∧ m''.kont = m.kont ∧ m''.ctl = .value v ∧
      ValueTy m''.heap v cod

/-! ## 3. Variance -/

/-- **Contravariant in `dom`, covariant in `cod`** (plan L3.5), directly from
    the definition: weaken the caller's actual args up from `dom'` to `dom`
    (`ValuesTy.weaken`), invoke the hypothesis, then weaken the result down
    from `cod` to `cod'` (`ValueTy.weaken`). No machine reasoning at all —
    the whole content is `subTy`'s own transitivity, which is why this is
    "the cheap early sanity check" the plan calls it. -/
theorem LamTy.variance {Γcap : Env} {dom dom' : List Ty} {cod cod' : Ty} {p : ObjId}
    (h : LamTy Γcap dom cod p) (hdom : subTys dom' dom = true) (hcod : subTy cod cod' = true) :
    LamTy Γcap dom' cod' p := by
  intro m c args brk m' fcap hpay hlam hfc hcap hshallow hconf hargs' hcall
  obtain ⟨v, m'', hreach, hstack, hkont, hctl, hv⟩ :=
    h m c args brk m' fcap hpay hlam hfc hcap hshallow hconf (hargs'.weaken hdom) hcall
  exact ⟨v, m'', hreach, hstack, hkont, hctl, hv.weaken hcod⟩

/-! ## 4. The direct semantic proof, for a bare-capture-read body

`callClosure_req2_lam` mirrors `Proof/Static/Iter.lean`'s `callClosure_req1`
exactly — same proof shape (`unfold`, `simp` the three structural hypotheses,
`rfl`) — at the one shape that lemma's `hlam : cl.lam = false` refuses and
this plan needs: two required params, `lam = true`. -/

theorem callClosure_req2_lam {m : Machine} {cl : Closure} {v1 v2 : Value}
    {x y : String} {brk : Option FrameId}
    (hps : cl.params = [.req x, .req y]) (hls : cl.locals = []) (hlam : cl.lam = true) :
    callClosure m cl [v1, v2] brk
      = .next (withKont
          { m with
            frames := m.frames.push
              { self := (m.frames.getD (cl.captured.getD 0) default).self,
                defmod := (m.frames.getD (cl.captured.getD 0) default).defmod,
                blk := (m.frames.getD (cl.captured.getD 0) default).blk,
                locals := [(x, v1), (y, v2)], kind := .block, captured := cl.captured,
                home := cl.home, lam := cl.lam,
                cref := (m.frames.getD (cl.captured.getD 0) default).cref },
            stack := m.frames.size :: m.stack }
          (.eval cl.body) (.blkFrameK m.frames.size cl.lam brk cl [v1, v2])) := by
  unfold callClosure
  simp only [hps, hls, hlam, classifySimple]
  rfl

/-- **The fundamental lemma, for a bare-capture-read body** (plan L3.4): a
    two-required-param `lam = true` closure whose body is a bare read of one
    name `y` — captured, not a parameter (`x₁ ≠ y`, `x₂ ≠ y`) — behaves as
    `LamTy` at any `dom`/`cod` the capture is claimed to carry `y` at.

    The whole proof is the deterministic two-step trace `callClosure_req2_lam`
    lands in (push the block frame, then the body — a `.var .lvar` read, one
    `evalExpr` step — then the `blkFrameK` pop, one `applyKont` step) composed
    via `Reaches.tail` twice; `y`'s value survives the walk by
    `Machine.getLocal`'s own definition (checks the pushed frame's `locals`
    first — `x₁`/`x₂` only, since `y ≠ x₁, x₂` — then follows `captured` to
    the frame `FrameConforms`'s hypothesis is about). Args are bound and never
    read — arity has to match (`callClosure`'s own gate, `ValuesTy`'s length
    equation gives it), but nothing about *what* they are matters. -/
theorem lamTy_of_capture_read {Γcap : Env} {dom : List Ty} {cod : Ty} {p : ObjId}
    {c : Closure} {x₁ x₂ y : String}
    -- **`p`'s payload is `c`, in every machine state** — the honest way to
    -- say "`p` is (already) a heap object holding this closure" without
    -- LamTy's own `∀ m` letting a *different* payload show up at some other
    -- `m`: real heap objects don't change their payload's constructor once
    -- allocated (`Proof/HeapGrow.lean`'s monotonicity family), so this is
    -- what an end-to-end use discharges, not an extra assumption about the
    -- world.
    (hpayload : ∀ m : Machine, (m.heap.get p).payload = .proc c)
    (hps : c.params = [.req x₁, .req x₂]) (hls : c.locals = []) (hlam : c.lam = true)
    (hbody : c.body = .var .lvar y) (hne1 : x₁ ≠ y) (hne2 : x₂ ≠ y)
    (hcapy : envGet? Γcap y = some cod) (hdomlen : dom.length = 2) :
    LamTy Γcap dom cod p := by
  intro m c' args brk m' fcap hpay hlam' hfc hcaplt hshallow hconf hargs hcall
  have hc : c = c' := by
    have h1 := hpayload m
    rw [hpay] at h1
    injection h1 with h2
    exact h2.symm
  subst hc
  obtain ⟨v1, v2, rfl⟩ : ∃ v1 v2, args = [v1, v2] := by
    match dom, hdomlen, args, hargs with
    | [_, _], _, [v1, v2], _ => exact ⟨v1, v2, rfl⟩
    | [_, _], _, [], hargs => simp [ValuesTy] at hargs
    | [_, _], _, [_], hargs => simp [ValuesTy] at hargs
    | [_, _], _, _ :: _ :: _ :: _, hargs => simp [ValuesTy] at hargs
  rw [callClosure_req2_lam hps hls hlam] at hcall
  -- L266: `callClosure` reads `cl.captured.getD 0` and copies `cl.captured` onto the
  -- pushed frame; `hfc` names both.
  simp only [hfc, Option.getD_some] at hcall
  injection hcall with hcall
  subst hcall
  let fid := m.frames.size
  have hfid : fid = m.frames.size := rfl
  let nf : Frame :=
    { self := (m.frames.getD fcap default).self,
      defmod := (m.frames.getD fcap default).defmod,
      blk := (m.frames.getD fcap default).blk,
      locals := [(x₁, v1), (x₂, v2)], kind := .block, captured := some fcap,
      home := c.home, lam := c.lam, cref := (m.frames.getD fcap default).cref }
  have hnf : nf =
    { self := (m.frames.getD fcap default).self,
      defmod := (m.frames.getD fcap default).defmod,
      blk := (m.frames.getD fcap default).blk,
      locals := [(x₁, v1), (x₂, v2)], kind := .block, captured := some fcap,
      home := c.home, lam := c.lam, cref := (m.frames.getD fcap default).cref } := rfl
  let M1 : Machine :=
    withKont { m with frames := m.frames.push nf, stack := fid :: m.stack }
      (.eval c.body) (.blkFrameK fid c.lam brk c [v1, v2])
  have hM1 : M1 = withKont { m with frames := m.frames.push nf, stack := fid :: m.stack }
      (.eval c.body) (.blkFrameK fid c.lam brk c [v1, v2]) := rfl
  -- `M1` is `FrameShallow`: the pushed frame's own chain is the one hop
  -- `hcaplt`/`hshallow` license.
  have hcurfid : curFid M1 = fid := by simp [curFid, hM1, withKont]
  have hM1size : M1.frames.size = fid + 1 := by simp [hM1, withKont, hfid]
  have hM1shallow : FrameShallow M1 := by
    refine ⟨?_, ?_, ?_⟩
    · show M1.stack ≠ []
      simp [hM1, withKont]
    · show curFid M1 < M1.frames.size
      calc curFid M1 = fid := hcurfid
        _ < fid + 1 := Nat.lt_succ_self fid
        _ = M1.frames.size := hM1size.symm
    intro q hq
    rw [hcurfid] at hq ⊢
    have hcur : (M1.frames.getD fid default) = nf := by
      simp only [hM1, withKont]
      exact getD_push_lt_self m.frames nf
    rw [hcur] at hq
    simp only [hnf] at hq
    have hq' : fcap = q := by simpa using hq
    subst hq'
    refine ⟨hcaplt, ?_⟩
    have : (M1.frames.getD fcap default) = m.frames.getD fcap default := by
      simp only [hM1, withKont]
      exact getD_push_lt m.frames fcap nf hcaplt
    rw [this]; exact hshallow
  have hcur : curFrame M1 = nf := by
    show M1.frames.getD (curFid M1) default = nf
    have : curFid M1 = fid := by simp [curFid, hM1, withKont]
    rw [this]
    simp only [hM1, withKont]
    exact getD_push_lt_self m.frames nf
  have hgetcap : (M1.frames.getD fcap default) = m.frames.getD fcap default := by
    simp only [hM1, withKont]
    exact getD_push_lt m.frames fcap nf hcaplt
  -- **step 1**: the body, a bare local read, is one `evalExpr` step.
  let v : Value := M1.getLocal y
  have hv : v = M1.getLocal y := rfl
  have hval : ValueTy m.heap v cod := by
    have hstep : M1.getLocal y = localOfIn M1.frames (curFrame M1) y := getLocal_curIn hM1shallow y
    rw [hcur] at hstep
    have hnfval : localOfIn M1.frames nf y = localOf (m.frames.getD fcap default) y := by
      simp only [hnf, localOfIn]
      have hx1 : ¬ ((x₁ == y) = true) := by simpa using hne1
      have hx2 : ¬ ((x₂ == y) = true) := by simpa using hne2
      simp only [List.find?, hx1, hx2, hgetcap]
    rw [hv, hstep, hnfval]
    have hloc : localOfIn m.frames (m.frames.getD fcap default) y
        = localOf (m.frames.getD fcap default) y :=
      localOfIn_of_captured_none y hshallow
    rw [← hloc]
    exact hconf.2.2 y cod hcapy
  have hM1M2 : SmallStep M1 (withCtl M1 (.value v)) := by
    show stepFn M1 = .next (withCtl M1 (.value v))
    show evalExpr M1 c.body = .next (withCtl M1 (.value v))
    rw [hbody]
    rfl
  let M2 : Machine := withCtl M1 (.value v)
  have hM2 : M2 = withCtl M1 (.value v) := rfl
  let M3 : Machine := withCtl { M2 with kont := m.kont, stack := m.stack } (.value v)
  have hM3 : M3 = withCtl { M2 with kont := m.kont, stack := m.stack } (.value v) := rfl
  have hM2M3 : SmallStep M2 M3 := by
    show stepFn M2 = .next M3
    show applyKont M2 v = .next M3
    rw [hM2, hM1]
    unfold withCtl withKont applyKont
    simp only
    rw [hM3, hM2, hM1]
    unfold withCtl withKont
    simp only [List.tail_cons]
  refine ⟨v, M3, Reaches.tail (Reaches.tail Reaches.refl hM1M2) hM2M3, ?_, ?_, ?_, ?_⟩
  · simp [hM3, withCtl]
  · simp [hM3, withCtl, hM2, withCtl]
  · simp [hM3, withCtl]
  · have : M3.heap = m.heap := by simp [hM3, withCtl, hM2, hM1, withKont, withCtl]
    rw [this]; exact hval

/-- **Worked end**: `comparator_for`'s closure (`difftest/ruby/lambda_comparator.rb`)
    — arity 2, params `a`/`b`, body a bare read of the captured `tiebreak` —
    instantiates the fundamental lemma at exactly the types its `sig`
    declares (`T.proc.params(a: String, b: String).returns(Integer)`),
    demonstrating it is not vacuous. This is the "backed by proof, not just a
    checker that says yes" the plan's L3 exit criterion asks for: `Types.TL.chk`'s
    `lambda` arm (`Types/LambdaArrow.lean`) admits exactly this closure under
    exactly these conditions — same arity gate (`allReq?`/length), same body
    (a captured-variable read), same capture set (`addPins` pins the whole
    enclosing `Γ`, which is where `tiebreak : Ty.int` comes from) — so a
    successful check of the real file supplies exactly these six hypotheses. -/
example (p : ObjId) (c : Closure)
    (hpayload : ∀ m : Machine, (m.heap.get p).payload = .proc c)
    (hps : c.params = [.req "a", .req "b"]) (hls : c.locals = [])
    (hlam : c.lam = true) (hbody : c.body = .var .lvar "tiebreak") :
    LamTy [("tiebreak", Ty.int)] [.cls "String", .cls "String"] .int p :=
  lamTy_of_capture_read hpayload hps hls hlam hbody (by decide) (by decide) rfl rfl

end RubyCore.Proof.Static
