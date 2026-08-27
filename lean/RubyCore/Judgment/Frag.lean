import RubyCore.Judgment.Judge

/-!
# `MFrag` — the machine-typed fragment gate (J20, J31)

`Judge` covers all 47 heads; the machine-typing invariant (`judgment-layer.md` §3)
does not, and the boundary has to be *syntactic*: the invariant's eval arm
quantifies existentially over derivations, so inversion at a head surfaces **every**
rule whose conclusion matches — a head admitted into machine typing drags in all its
rules' preservation cases at once. `MFrag` is the gate: the eval arm conjoins it, an
out-of-fragment head refutes its case by this predicate rather than by typing work
(the role `infer`'s partiality played for the old spine, `StaticSoundness.lean` §Shape).

The fragment grows head by head, each with its preservation case; the current list is
the J-ladder's progress marker. Two exclusions are *shape* conditions inside admitted
heads rather than head exclusions, and each is a recorded design point:

* a send named **`call`** stays out even after sends land — `Judge.sendCall`
  eliminates arrows, and no machine-typed value witnesses an arrow yet (J19).
  (The bare-local-`if` shape gate this list used to open with is gone: J27's
  narrowing rung machine-types those derivations.)

**J31: the gate is indexed by the semantic axiom set `A`.** A claimed expression
(out-of-fragment head, `e ∈ A`) is in the fragment via the `semantic` arm — that is
how a program *containing* a semantic leaf stays machine-typed. Two disciplines keep
the two routes from competing:

* the `semantic` arm demands `fragHead e = false`, and every syntactic constructor
  concludes at a `fragHead`-true shape — so at any given head exactly one route is
  possible, and preservation's `MFrag` inversions refute the foreign arm by one
  `fragHead` computation;
* every container **except `seq`** requires its subterms `fragHead`-true (i.e.
  syntactic): a semantic leaf embeds only in *statement position*, where the value
  is discarded or absorbed at the canonical `.any` and the `JudgeSeq` coupling
  premises hand preservation the environment/table threading it needs. Widening the
  admissible positions (an `if` branch, a send argument) is a rung per position:
  each needs its coupling premise and its delivery case.
-/

namespace RubyCore.Judgment

open RubyCore.Types

/-- The machine-typed fragment, as an inductive so preservation cases decompose it
    by `cases`. The Boolean form for the certificate checker is `mfragB` below. -/
inductive MFrag (A : SemAxioms) : Expr → Prop where
  /-- **The semantic leaf (J31/J32)**: a claimed expression, out-of-fragment head. -/
  | semantic {e} : (∃ cl ∈ A, cl.e = e) → fragHead e = false → MFrag A e
  | int {n} : MFrag A (.int n)
  | flt {x} : MFrag A (.flt x)
  | str {s} : MFrag A (.str s)
  | sym {s} : MFrag A (.sym s)
  | tru : MFrag A .tru
  | fls : MFrag A .fls
  | nil : MFrag A .nil
  | varLvar {x} : MFrag A (.var .lvar x)
  | vasgnLvar {x rhs} :
      fragHead rhs = true → MFrag A rhs → MFrag A (.vasgn .lvar x rhs)
  /-- The one container that admits semantic leaves — statement position. -/
  | seq {es} : (∀ e ∈ es, MFrag A e) → MFrag A (.seq es)
  | ifElse {cond t els} :
      fragHead cond = true → fragHead t = true → fragHead els = true →
      MFrag A cond → MFrag A t → MFrag A els → MFrag A (.if' cond t (some els))
  | ifNone {cond t} :
      fragHead cond = true → fragHead t = true →
      MFrag A cond → MFrag A t → MFrag A (.if' cond t none)
  | while' {c b} :
      fragHead c = true → fragHead b = true →
      MFrag A c → MFrag A b → MFrag A (.while' c b)
  -- J22: sends. Block-less only (`blk = none` in the stored shape), and an explicit
  -- send named `call` stays out — `Judge.sendCall` eliminates arrows, and no
  -- machine-typed value witnesses one (J19). Argument shapes that take their own
  -- kont path (`splat`/`kwargs`/`fwd`) are excluded by having no constructor here,
  -- which is what lets the dispatch cases prove `startArgs` takes the plain branch.
  | self' : MFrag A .self'
  | vcall {mname} : MFrag A (.vcall mname)
  | send {r mname args} : mname ≠ "call" →
      fragHead r = true → (∀ a ∈ args, fragHead a = true) →
      MFrag A r → (∀ a ∈ args, MFrag A a) → MFrag A (.send (some r) mname args none)
  | sendImplicit {mname args} :
      (∀ a ∈ args, fragHead a = true) →
      (∀ a ∈ args, MFrag A a) → MFrag A (.send none mname args none)
  -- J23: definition forms. The body gate is what the *promotion* derivation's
  -- installed row needs (`UserConformsJ` carries `MFrag body`); a reopen's body
  -- runs, so its gate is the eval arm's own.
  | def' {name params body} :
      fragHead body = true → MFrag A body → MFrag A (.def' name params body)
  | classTop {name body} :
      fragHead body = true → MFrag A body → MFrag A (.class' name none body)
  -- J26: the table-read heads and the array literal. A splat element has no
  -- constructor here, which is what keeps the literal's loop on the plain branch
  -- (`continueArray_plain`'s side conditions fall out of `MFrag`'s own emptiness
  -- at those shapes).
  | const {n} : MFrag A (.const n)
  -- J38: scoped constant reads. `::n` is one step (a toplevel lookup); `b::n`
  -- pushes `.cpathK` on the base, whose delivery only *reads* (`ScopedConstOk`).
  | cpathAbs {n} : MFrag A (.cpath none n)
  | cpathScoped {b n} :
      fragHead b = true → MFrag A b → MFrag A (.cpath (some b) n)
  | varIvar {x} : MFrag A (.var .ivar x)
  | varGvar {x} : MFrag A (.var .gvar x)
  | vasgnIvar {x rhs} :
      fragHead rhs = true → MFrag A rhs → MFrag A (.vasgn .ivar x rhs)
  | vasgnGvar {x rhs} :
      fragHead rhs = true → MFrag A rhs → MFrag A (.vasgn .gvar x rhs)
  | array {es} :
      (∀ e ∈ es, fragHead e = true) →
      (∀ e ∈ es, MFrag A e) → MFrag A (.array es)

/-- The disjointness the `semantic` arm's gate buys, cashed: an in-fragment
    expression at an out-of-fragment head **is** a claim. (Every syntactic
    constructor concludes at a `fragHead`-true shape.) -/
theorem MFrag.claimed_of_fragHead_false {A : SemAxioms} {e : Expr}
    (hm : MFrag A e) (hf : fragHead e = false) : ∃ cl ∈ A, cl.e = e := by
  cases hm
  case semantic hmem _ => exact hmem
  all_goals simp [fragHead] at hf

/-! ## Claim membership, decidably (J31)

`Float` is opaque, so `Expr` has no derivable `DecidableEq` (the V15 note at the
`BEq` instance), and the derived `BEq` is *unsound for propositional equality* at
`.flt` (`-0.0 == 0.0`). The checker therefore decides claim membership with a
**float-refusing structural equality**: sound (`= true → =`, the only direction
the soundness proofs need), complete except at `.flt` fields — and a claim with a
float literal in it simply cannot be checker-matched, which is the safe direction
(the refusal is a reject, never an unsound accept). Fueled, per the L73
kernel-reduction discipline. -/

mutual
def exprEqB : Nat → Expr → Expr → Bool
  | 0, _, _ => false
  | n + 1, a, b =>
    match a, b with
    | .int x, .int y => decide (x = y)
    | .flt _, .flt _ => false
    | .str x, .str y => decide (x = y)
    | .sym x, .sym y => decide (x = y)
    | .tru, .tru => true
    | .fls, .fls => true
    | .nil, .nil => true
    | .self', .self' => true
    | .fwd, .fwd => true
    | .retry', .retry' => true
    | .redo', .redo' => true
    | .var k x, .var k' x' => decide (k = k') && decide (x = x')
    | .vasgn k x e, .vasgn k' x' e' =>
      decide (k = k') && decide (x = x') && exprEqB n e e'
    | .const x, .const x' => decide (x = x')
    | .casgn x e, .casgn x' e' => decide (x = x') && exprEqB n e e'
    | .cpath b1 x, .cpath b2 x' => exprOptEqB n b1 b2 && decide (x = x')
    | .cpathAsgn b1 x e, .cpathAsgn b2 x' e' =>
      exprOptEqB n b1 b2 && decide (x = x') && exprEqB n e e'
    | .send r m args blk, .send r' m' args' blk' =>
      exprOptEqB n r r' && decide (m = m') && exprsEqB n args args' &&
        exprOptEqB n blk blk'
    | .vcall m, .vcall m' => decide (m = m')
    | .kwargs es, .kwargs es' => kwsEqB n es es'
    | .block ps ls e, .block ps' ls' e' =>
      paramsEqB n ps ps' && decide (ls = ls') && exprEqB n e e'
    | .yield' args, .yield' args' => exprsEqB n args args'
    | .blockpass e, .blockpass e' => exprOptEqB n e e'
    | .if' c t e, .if' c' t' e' =>
      exprEqB n c c' && exprEqB n t t' && exprOptEqB n e e'
    | .while' c b1, .while' c' b2 => exprEqB n c c' && exprEqB n b1 b2
    | .dowhile b1 c, .dowhile b2 c' => exprEqB n b1 b2 && exprEqB n c c'
    | .for' ts c b1, .for' ts' c' b2 =>
      decide (ts = ts') && exprEqB n c c' && exprEqB n b1 b2
    | .def' x ps e, .def' x' ps' e' =>
      decide (x = x') && paramsEqB n ps ps' && exprEqB n e e'
    | .array es, .array es' => exprsEqB n es es'
    | .hash prs, .hash prs' => pairsEqB n prs prs'
    | .splat e, .splat e' => exprOptEqB n e e'
    | .ret e, .ret e' => exprOptEqB n e e'
    | .brk e, .brk e' => exprOptEqB n e e'
    | .nxt e, .nxt e' => exprOptEqB n e e'
    | .class' x sup e, .class' x' sup' e' =>
      decide (x = x') && exprOptEqB n sup sup' && exprEqB n e e'
    | .module' x e, .module' x' e' => decide (x = x') && exprEqB n e e'
    | .scopedClass b1 x e, .scopedClass b2 x' e' =>
      exprOptEqB n b1 b2 && decide (x = x') && exprEqB n e e'
    | .scopedModule b1 x e, .scopedModule b2 x' e' =>
      exprOptEqB n b1 b2 && decide (x = x') && exprEqB n e e'
    | .sclass o e, .sclass o' e' => exprEqB n o o' && exprEqB n e e'
    | .defs r x ps e, .defs r' x' ps' e' =>
      exprEqB n r r' && decide (x = x') && paramsEqB n ps ps' && exprEqB n e e'
    | .begin' e rs els ens, .begin' e' rs' els' ens' =>
      exprEqB n e e' && rescuesEqB n rs rs' && exprOptEqB n els els' &&
        exprOptEqB n ens ens'
    | .super' args blk, .super' args' blk' =>
      exprsEqB n args args' && exprOptEqB n blk blk'
    | .zsuper blk, .zsuper blk' => exprOptEqB n blk blk'
    | .undef xs, .undef xs' => decide (xs = xs')
    | .alias' x y, .alias' x' y' => decide (x = x') && decide (y = y')
    | .defined e, .defined e' => exprEqB n e e'
    | .seq es, .seq es' => exprsEqB n es es'
    | _, _ => false

def exprOptEqB : Nat → Option Expr → Option Expr → Bool
  | 0, _, _ => false
  | n + 1, a, b =>
    match a, b with
    | none, none => true
    | some x, some y => exprEqB n x y
    | _, _ => false

def exprsEqB : Nat → List Expr → List Expr → Bool
  | 0, _, _ => false
  | n + 1, a, b =>
    match a, b with
    | [], [] => true
    | x :: xs, y :: ys => exprEqB n x y && exprsEqB n xs ys
    | _, _ => false

def pairsEqB : Nat → List (Expr × Expr) → List (Expr × Expr) → Bool
  | 0, _, _ => false
  | n + 1, a, b =>
    match a, b with
    | [], [] => true
    | (k, v) :: xs, (k', v') :: ys =>
      exprEqB n k k' && exprEqB n v v' && pairsEqB n xs ys
    | _, _ => false

def rescuesEqB : Nat → List (List Expr × Option (TargetKind × String) × Expr) →
    List (List Expr × Option (TargetKind × String) × Expr) → Bool
  | 0, _, _ => false
  | n + 1, a, b =>
    match a, b with
    | [], [] => true
    | (excs, tgt, h) :: xs, (excs', tgt', h') :: ys =>
      exprsEqB n excs excs' && decide (tgt = tgt') && exprEqB n h h' &&
        rescuesEqB n xs ys
    | _, _ => false

def paramEqB : Nat → Param → Param → Bool
  | 0, _, _ => false
  | n + 1, a, b =>
    match a, b with
    | .req x, .req y => decide (x = y)
    | .opt x d, .opt y d' => decide (x = y) && exprEqB n d d'
    | .rest x, .rest y => decide (x = y)
    | .key x d, .key y d' => decide (x = y) && exprOptEqB n d d'
    | .kwrest x, .kwrest y => decide (x = y)
    | .block x, .block y => decide (x = y)
    | .fwd, .fwd => true
    | .destr ps, .destr ps' => paramsEqB n ps ps'
    | _, _ => false

def paramsEqB : Nat → List Param → List Param → Bool
  | 0, _, _ => false
  | n + 1, a, b =>
    match a, b with
    | [], [] => true
    | x :: xs, y :: ys => paramEqB n x y && paramsEqB n xs ys
    | _, _ => false

def kwEqB : Nat → KwEntry → KwEntry → Bool
  | 0, _, _ => false
  | n + 1, a, b =>
    match a, b with
    | .pair k v, .pair k' v' => decide (k = k') && exprEqB n v v'
    | .dyn k v, .dyn k' v' => exprEqB n k k' && exprEqB n v v'
    | .splat e, .splat e' => exprEqB n e e'
    | _, _ => false

def kwsEqB : Nat → List KwEntry → List KwEntry → Bool
  | 0, _, _ => false
  | n + 1, a, b =>
    match a, b with
    | [], [] => true
    | x :: xs, y :: ys => kwEqB n x y && kwsEqB n xs ys
    | _, _ => false
end

set_option maxHeartbeats 4000000 in
/-- Soundness — the only direction anything needs. -/
theorem exprEqB_sound_all : ∀ n : Nat,
    (∀ a b, exprEqB n a b = true → a = b) ∧
    (∀ a b, exprOptEqB n a b = true → a = b) ∧
    (∀ a b, exprsEqB n a b = true → a = b) ∧
    (∀ a b, pairsEqB n a b = true → a = b) ∧
    (∀ a b, rescuesEqB n a b = true → a = b) ∧
    (∀ a b, paramEqB n a b = true → a = b) ∧
    (∀ a b, paramsEqB n a b = true → a = b) ∧
    (∀ a b, kwEqB n a b = true → a = b) ∧
    (∀ a b, kwsEqB n a b = true → a = b) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      exact fun a b h => Bool.noConfusion h
  | succ n ih =>
    obtain ⟨ihE, ihO, ihL, ihP, ihR, ihPm, ihPs, ihK, ihKs⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a b h
      match a, b with
      | .flt _, .flt _ => exact Bool.noConfusion h
      | .int a1, .int b1 =>
        replace h : (decide (a1 = b1)) = true := h
        replace h := of_decide_eq_true h
        rw [h]
      | .str a1, .str b1 =>
        replace h : (decide (a1 = b1)) = true := h
        replace h := of_decide_eq_true h
        rw [h]
      | .sym a1, .sym b1 =>
        replace h : (decide (a1 = b1)) = true := h
        replace h := of_decide_eq_true h
        rw [h]
      | .tru, .tru => rfl
      | .fls, .fls => rfl
      | .nil, .nil => rfl
      | .self', .self' => rfl
      | .fwd, .fwd => rfl
      | .retry', .retry' => rfl
      | .redo', .redo' => rfl
      | .var a1 a2, .var b1 b2 =>
        replace h : (decide (a1 = b1) && decide (a2 = b2)) = true := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨h1, h2⟩ := h
        rw [h1, h2]
      | .vasgn a1 a2 a3, .vasgn b1 b2 b3 =>
        replace h : (decide (a1 = b1) && decide (a2 = b2) && exprEqB n a3 b3) = true := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        rw [h1, h2, ihE _ _ h3]
      | .const a1, .const b1 =>
        replace h : (decide (a1 = b1)) = true := h
        replace h := of_decide_eq_true h
        rw [h]
      | .casgn a1 a2, .casgn b1 b2 =>
        replace h : (decide (a1 = b1) && exprEqB n a2 b2) = true := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨h1, h2⟩ := h
        rw [h1, ihE _ _ h2]
      | .cpath a1 a2, .cpath b1 b2 =>
        replace h : (exprOptEqB n a1 b1 && decide (a2 = b2)) = true := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨h1, h2⟩ := h
        rw [ihO _ _ h1, h2]
      | .cpathAsgn a1 a2 a3, .cpathAsgn b1 b2 b3 =>
        replace h : (exprOptEqB n a1 b1 && decide (a2 = b2) && exprEqB n a3 b3) = true := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        rw [ihO _ _ h1, h2, ihE _ _ h3]
      | .send a1 a2 a3 a4, .send b1 b2 b3 b4 =>
        replace h : (exprOptEqB n a1 b1 && decide (a2 = b2) && exprsEqB n a3 b3 && exprOptEqB n a4 b4) = true := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
        rw [ihO _ _ h1, h2, ihL _ _ h3, ihO _ _ h4]
      | .vcall a1, .vcall b1 =>
        replace h : (decide (a1 = b1)) = true := h
        replace h := of_decide_eq_true h
        rw [h]
      | .kwargs a1, .kwargs b1 =>
        replace h : (kwsEqB n a1 b1) = true := h
        rw [ihKs _ _ h]
      | .block a1 a2 a3, .block b1 b2 b3 =>
        replace h : (paramsEqB n a1 b1 && decide (a2 = b2) && exprEqB n a3 b3) = true := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        rw [ihPs _ _ h1, h2, ihE _ _ h3]
      | .yield' a1, .yield' b1 =>
        replace h : (exprsEqB n a1 b1) = true := h
        rw [ihL _ _ h]
      | .blockpass a1, .blockpass b1 =>
        replace h : (exprOptEqB n a1 b1) = true := h
        rw [ihO _ _ h]
      | .if' a1 a2 a3, .if' b1 b2 b3 =>
        replace h : (exprEqB n a1 b1 && exprEqB n a2 b2 && exprOptEqB n a3 b3) = true := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        rw [ihE _ _ h1, ihE _ _ h2, ihO _ _ h3]
      | .while' a1 a2, .while' b1 b2 =>
        replace h : (exprEqB n a1 b1 && exprEqB n a2 b2) = true := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨h1, h2⟩ := h
        rw [ihE _ _ h1, ihE _ _ h2]
      | .dowhile a1 a2, .dowhile b1 b2 =>
        replace h : (exprEqB n a1 b1 && exprEqB n a2 b2) = true := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨h1, h2⟩ := h
        rw [ihE _ _ h1, ihE _ _ h2]
      | .for' a1 a2 a3, .for' b1 b2 b3 =>
        replace h : (decide (a1 = b1) && exprEqB n a2 b2 && exprEqB n a3 b3) = true := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        rw [h1, ihE _ _ h2, ihE _ _ h3]
      | .def' a1 a2 a3, .def' b1 b2 b3 =>
        replace h : (decide (a1 = b1) && paramsEqB n a2 b2 && exprEqB n a3 b3) = true := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        rw [h1, ihPs _ _ h2, ihE _ _ h3]
      | .array a1, .array b1 =>
        replace h : (exprsEqB n a1 b1) = true := h
        rw [ihL _ _ h]
      | .hash a1, .hash b1 =>
        replace h : (pairsEqB n a1 b1) = true := h
        rw [ihP _ _ h]
      | .splat a1, .splat b1 =>
        replace h : (exprOptEqB n a1 b1) = true := h
        rw [ihO _ _ h]
      | .ret a1, .ret b1 =>
        replace h : (exprOptEqB n a1 b1) = true := h
        rw [ihO _ _ h]
      | .brk a1, .brk b1 =>
        replace h : (exprOptEqB n a1 b1) = true := h
        rw [ihO _ _ h]
      | .nxt a1, .nxt b1 =>
        replace h : (exprOptEqB n a1 b1) = true := h
        rw [ihO _ _ h]
      | .class' a1 a2 a3, .class' b1 b2 b3 =>
        replace h : (decide (a1 = b1) && exprOptEqB n a2 b2 && exprEqB n a3 b3) = true := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        rw [h1, ihO _ _ h2, ihE _ _ h3]
      | .module' a1 a2, .module' b1 b2 =>
        replace h : (decide (a1 = b1) && exprEqB n a2 b2) = true := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨h1, h2⟩ := h
        rw [h1, ihE _ _ h2]
      | .scopedClass a1 a2 a3, .scopedClass b1 b2 b3 =>
        replace h : (exprOptEqB n a1 b1 && decide (a2 = b2) && exprEqB n a3 b3) = true := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        rw [ihO _ _ h1, h2, ihE _ _ h3]
      | .scopedModule a1 a2 a3, .scopedModule b1 b2 b3 =>
        replace h : (exprOptEqB n a1 b1 && decide (a2 = b2) && exprEqB n a3 b3) = true := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        rw [ihO _ _ h1, h2, ihE _ _ h3]
      | .sclass a1 a2, .sclass b1 b2 =>
        replace h : (exprEqB n a1 b1 && exprEqB n a2 b2) = true := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨h1, h2⟩ := h
        rw [ihE _ _ h1, ihE _ _ h2]
      | .defs a1 a2 a3 a4, .defs b1 b2 b3 b4 =>
        replace h : (exprEqB n a1 b1 && decide (a2 = b2) && paramsEqB n a3 b3 && exprEqB n a4 b4) = true := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
        rw [ihE _ _ h1, h2, ihPs _ _ h3, ihE _ _ h4]
      | .begin' a1 a2 a3 a4, .begin' b1 b2 b3 b4 =>
        replace h : (exprEqB n a1 b1 && rescuesEqB n a2 b2 && exprOptEqB n a3 b3 && exprOptEqB n a4 b4) = true := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
        rw [ihE _ _ h1, ihR _ _ h2, ihO _ _ h3, ihO _ _ h4]
      | .super' a1 a2, .super' b1 b2 =>
        replace h : (exprsEqB n a1 b1 && exprOptEqB n a2 b2) = true := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨h1, h2⟩ := h
        rw [ihL _ _ h1, ihO _ _ h2]
      | .zsuper a1, .zsuper b1 =>
        replace h : (exprOptEqB n a1 b1) = true := h
        rw [ihO _ _ h]
      | .undef a1, .undef b1 =>
        replace h : (decide (a1 = b1)) = true := h
        replace h := of_decide_eq_true h
        rw [h]
      | .alias' a1 a2, .alias' b1 b2 =>
        replace h : (decide (a1 = b1) && decide (a2 = b2)) = true := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨h1, h2⟩ := h
        rw [h1, h2]
      | .defined a1, .defined b1 =>
        replace h : (exprEqB n a1 b1) = true := h
        rw [ihE _ _ h]
      | .seq a1, .seq b1 =>
        replace h : (exprsEqB n a1 b1) = true := h
        rw [ihL _ _ h]
    · intro a b h
      match a, b with
      | none, none => rfl
      | some x, some y =>
        replace h : exprEqB n x y = true := h
        rw [ihE _ _ h]
    · intro a b h
      match a, b with
      | [], [] => rfl
      | x :: xs, y :: ys =>
        replace h : (exprEqB n x y && exprsEqB n xs ys) = true := h
        simp only [Bool.and_eq_true] at h
        rw [ihE _ _ h.1, ihL _ _ h.2]
    · intro a b h
      match a, b with
      | [], [] => rfl
      | (k, v) :: xs, (k', v') :: ys =>
        replace h : (exprEqB n k k' && exprEqB n v v' && pairsEqB n xs ys) = true := h
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        rw [ihE _ _ h1, ihE _ _ h2, ihP _ _ h3]
    · intro a b h
      match a, b with
      | [], [] => rfl
      | (excs, tgt, hb) :: xs, (excs', tgt', hb') :: ys =>
        replace h : (exprsEqB n excs excs' && decide (tgt = tgt') &&
          exprEqB n hb hb' && rescuesEqB n xs ys) = true := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
        rw [ihL _ _ h1, h2, ihE _ _ h3, ihR _ _ h4]
    · intro a b h
      match a, b with
      | .req x, .req y =>
        replace h : decide (x = y) = true := h
        rw [of_decide_eq_true h]
      | .opt x d, .opt y d' =>
        replace h : (decide (x = y) && exprEqB n d d') = true := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        rw [h.1, ihE _ _ h.2]
      | .rest x, .rest y =>
        replace h : decide (x = y) = true := h
        rw [of_decide_eq_true h]
      | .key x d, .key y d' =>
        replace h : (decide (x = y) && exprOptEqB n d d') = true := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        rw [h.1, ihO _ _ h.2]
      | .kwrest x, .kwrest y =>
        replace h : decide (x = y) = true := h
        rw [of_decide_eq_true h]
      | .block x, .block y =>
        replace h : decide (x = y) = true := h
        rw [of_decide_eq_true h]
      | .fwd, .fwd => rfl
      | .destr ps, .destr ps' =>
        replace h : paramsEqB n ps ps' = true := h
        rw [ihPs _ _ h]
    · intro a b h
      match a, b with
      | [], [] => rfl
      | x :: xs, y :: ys =>
        replace h : (paramEqB n x y && paramsEqB n xs ys) = true := h
        simp only [Bool.and_eq_true] at h
        rw [ihPm _ _ h.1, ihPs _ _ h.2]
    · intro a b h
      match a, b with
      | .pair k v, .pair k' v' =>
        replace h : (decide (k = k') && exprEqB n v v') = true := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        rw [h.1, ihE _ _ h.2]
      | .dyn k v, .dyn k' v' =>
        replace h : (exprEqB n k k' && exprEqB n v v') = true := h
        simp only [Bool.and_eq_true] at h
        rw [ihE _ _ h.1, ihE _ _ h.2]
      | .splat e, .splat e' =>
        replace h : exprEqB n e e' = true := h
        rw [ihE _ _ h]
    · intro a b h
      match a, b with
      | [], [] => rfl
      | x :: xs, y :: ys =>
        replace h : (kwEqB n x y && kwsEqB n xs ys) = true := h
        simp only [Bool.and_eq_true] at h
        rw [ihK _ _ h.1, ihKs _ _ h.2]

theorem exprEqB_sound {n : Nat} {a b : Expr} (h : exprEqB n a b = true) : a = b :=
  (exprEqB_sound_all n).1 a b h

/-- Claim-list membership, decided by the structural equality. -/
def claimedB (A : SemAxioms) (n : Nat) (e : Expr) : Bool :=
  A.any (fun cl => exprEqB n cl.e e)

theorem claimedB_sound {A : SemAxioms} {n : Nat} {e : Expr}
    (h : claimedB A n e = true) : ∃ cl ∈ A, cl.e = e := by
  obtain ⟨cl, hmem, heq⟩ := List.any_eq_true.mp h
  exact ⟨cl, hmem, exprEqB_sound heq⟩

/-- The syntactic arms of the fragment gate, with the recursive call abstracted
    (`rec` is `mfragB A n`) — a plain non-recursive definition, so every proof step
    over it is a small definitional reduction. -/
def mfragBody (A : SemAxioms) (rec : Expr → Bool) : Expr → Bool
  | e =>
    match e with
    | .int _ | .flt _ | .str _ | .sym _ | .tru | .fls | .nil => true
    | .var .lvar _ => true
    | .vasgn .lvar _ rhs => fragHead rhs && rec rhs
    | .seq es => es.all rec
    | .if' cond t els =>
      fragHead cond && fragHead t && rec cond && rec t &&
      (match els with | some e' => fragHead e' && rec e' | none => true)
    | .while' c b => fragHead c && fragHead b && rec c && rec b
    | .self' => true
    | .vcall _ => true
    | .send (some r) mname args none =>
      (mname != "call") && fragHead r && args.all fragHead &&
      rec r && args.all rec
    | .send none _ args none => args.all fragHead && args.all rec
    | .def' _ _ body => fragHead body && rec body
    | .class' _ none body => fragHead body && rec body
    | .const _ => true
    | .cpath none _ => true
    | .cpath (some b) _ => fragHead b && rec b
    | .var .ivar _ => true
    | .var .gvar _ => true
    | .vasgn .ivar _ rhs => fragHead rhs && rec rhs
    | .vasgn .gvar _ rhs => fragHead rhs && rec rhs
    | .array es => es.all fragHead && es.all rec
    | _ => false

/-- The `Bool` fragment gate, on fuel (the L73 discipline: the J2 checker runs it
    under `decide`, so it must kernel-reduce). Semantic disjunct first (J31), then
    the syntactic arms. Sound against `MFrag`. -/
def mfragB (A : SemAxioms) : Nat → Expr → Bool
  | 0, _ => false
  | n + 1, e =>
    if !fragHead e && claimedB A (n + 1) e then true
    else mfragBody A (fun e' => mfragB A n e') e

set_option maxHeartbeats 1000000 in
theorem mfragB_sound {A : SemAxioms} :
    ∀ {n : Nat} {e : Expr}, mfragB A n e = true → MFrag A e := by
  intro n
  induction n with
  | zero => intro e h; exact Bool.noConfusion h
  | succ n ih =>
    intro e h
    by_cases hsem : (!fragHead e && claimedB A (n + 1) e) = true
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hsem
      exact .semantic (claimedB_sound hsem.2) hsem.1
    · have h' : (if (!fragHead e && claimedB A (n + 1) e) = true then true
        else mfragBody A (fun e' => mfragB A n e') e) = true := h
      rw [if_neg hsem] at h'
      clear h hsem
      match e with
      | .int _ => exact .int
      | .flt _ => exact .flt
      | .str _ => exact .str
      | .sym _ => exact .sym
      | .tru => exact .tru
      | .fls => exact .fls
      | .nil => exact .nil
      | .var .lvar _ => exact .varLvar
      | .vasgn .lvar x rhs =>
        replace h' : (fragHead rhs && mfragB A n rhs) = true := h'
        simp only [Bool.and_eq_true] at h'
        exact .vasgnLvar h'.1 (ih h'.2)
      | .seq es =>
        replace h' : (es.all (fun e' => mfragB A n e')) = true := h'
        exact .seq fun e' he' => ih (List.all_eq_true.mp h' e' he')
      | .if' cond t (some e') =>
        replace h' : (fragHead cond && fragHead t && mfragB A n cond && mfragB A n t &&
          (fragHead e' && mfragB A n e')) = true := h'
        simp only [Bool.and_eq_true] at h'
        obtain ⟨⟨⟨⟨hfc, hft⟩, hc⟩, ht⟩, hfe, he⟩ := h'
        exact .ifElse hfc hft hfe (ih hc) (ih ht) (ih he)
      | .if' cond t none =>
        replace h' : (fragHead cond && fragHead t && mfragB A n cond && mfragB A n t &&
          true) = true := h'
        simp only [Bool.and_eq_true] at h'
        obtain ⟨⟨⟨⟨hfc, hft⟩, hc⟩, ht⟩, -⟩ := h'
        exact .ifNone hfc hft (ih hc) (ih ht)
      | .while' c b =>
        replace h' : (fragHead c && fragHead b && mfragB A n c && mfragB A n b) = true := h'
        simp only [Bool.and_eq_true] at h'
        obtain ⟨⟨⟨hfc, hfb⟩, hc⟩, hb⟩ := h'
        exact .while' hfc hfb (ih hc) (ih hb)
      | .self' => exact .self'
      | .vcall _ => exact .vcall
      | .send (some r) mname args none =>
        replace h' : ((mname != "call") && fragHead r && args.all fragHead &&
          mfragB A n r && args.all (fun e' => mfragB A n e')) = true := h'
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at h'
        obtain ⟨⟨⟨⟨hnc, hfr⟩, hfas⟩, hr⟩, has⟩ := h'
        exact .send hnc hfr (fun a ha => hfas a ha) (ih hr) fun a ha => ih (has a ha)
      | .send none mname args none =>
        replace h' : (args.all fragHead && args.all (fun e' => mfragB A n e')) = true := h'
        simp only [Bool.and_eq_true, List.all_eq_true] at h'
        exact .sendImplicit (fun a ha => h'.1 a ha) fun a ha => ih (h'.2 a ha)
      | .def' _ _ body =>
        replace h' : (fragHead body && mfragB A n body) = true := h'
        simp only [Bool.and_eq_true] at h'
        exact .def' h'.1 (ih h'.2)
      | .class' _ none body =>
        replace h' : (fragHead body && mfragB A n body) = true := h'
        simp only [Bool.and_eq_true] at h'
        exact .classTop h'.1 (ih h'.2)
      | .const _ => exact .const
      | .cpath none _ => exact .cpathAbs
      | .cpath (some b) _ =>
        replace h' : (fragHead b && mfragB A n b) = true := h'
        simp only [Bool.and_eq_true] at h'
        exact .cpathScoped h'.1 (ih h'.2)
      | .var .ivar _ => exact .varIvar
      | .var .gvar _ => exact .varGvar
      | .vasgn .ivar x rhs =>
        replace h' : (fragHead rhs && mfragB A n rhs) = true := h'
        simp only [Bool.and_eq_true] at h'
        exact .vasgnIvar h'.1 (ih h'.2)
      | .vasgn .gvar x rhs =>
        replace h' : (fragHead rhs && mfragB A n rhs) = true := h'
        simp only [Bool.and_eq_true] at h'
        exact .vasgnGvar h'.1 (ih h'.2)
      | .array es =>
        replace h' : (es.all fragHead && es.all (fun e' => mfragB A n e')) = true := h'
        simp only [Bool.and_eq_true, List.all_eq_true] at h'
        exact .array (fun e' he' => h'.1 e' he') fun e' he' => ih (h'.2 e' he')
      | .casgn _ _ => exact Bool.noConfusion h'
      | .cpathAsgn _ _ _ => exact Bool.noConfusion h'
      | .send (some _) _ _ (some _) => exact Bool.noConfusion h'
      | .send none _ _ (some _) => exact Bool.noConfusion h'
      | .kwargs _ => exact Bool.noConfusion h'
      | .block _ _ _ => exact Bool.noConfusion h'
      | .yield' _ => exact Bool.noConfusion h'
      | .blockpass _ => exact Bool.noConfusion h'
      | .dowhile _ _ => exact Bool.noConfusion h'
      | .for' _ _ _ => exact Bool.noConfusion h'
      | .hash _ => exact Bool.noConfusion h'
      | .splat _ => exact Bool.noConfusion h'
      | .ret _ => exact Bool.noConfusion h'
      | .brk _ => exact Bool.noConfusion h'
      | .nxt _ => exact Bool.noConfusion h'
      | .retry' => exact Bool.noConfusion h'
      | .redo' => exact Bool.noConfusion h'
      | .class' _ (some _) _ => exact Bool.noConfusion h'
      | .module' _ _ => exact Bool.noConfusion h'
      | .scopedClass _ _ _ => exact Bool.noConfusion h'
      | .scopedModule _ _ _ => exact Bool.noConfusion h'
      | .sclass _ _ => exact Bool.noConfusion h'
      | .defs _ _ _ _ => exact Bool.noConfusion h'
      | .begin' _ _ _ _ => exact Bool.noConfusion h'
      | .super' _ _ => exact Bool.noConfusion h'
      | .zsuper _ => exact Bool.noConfusion h'
      | .undef _ => exact Bool.noConfusion h'
      | .alias' _ _ => exact Bool.noConfusion h'
      | .defined _ => exact Bool.noConfusion h'
      | .var .cvar _ => exact Bool.noConfusion h'
      | .vasgn .cvar _ _ => exact Bool.noConfusion h'
      | .fwd => exact Bool.noConfusion h'

end RubyCore.Judgment
