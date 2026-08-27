import RubyCore.Judgment.Judge

/-!
# `MFrag` — the machine-typed fragment gate (J20)

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
-/

namespace RubyCore.Judgment

open RubyCore.Types

/-- The machine-typed fragment, as an inductive so preservation cases decompose it
    by `cases`. The Boolean form for the certificate checker is `mfragB` below. -/
inductive MFrag : Expr → Prop where
  | int {n} : MFrag (.int n)
  | flt {x} : MFrag (.flt x)
  | str {s} : MFrag (.str s)
  | sym {s} : MFrag (.sym s)
  | tru : MFrag .tru
  | fls : MFrag .fls
  | nil : MFrag .nil
  | varLvar {x} : MFrag (.var .lvar x)
  | vasgnLvar {x rhs} : MFrag rhs → MFrag (.vasgn .lvar x rhs)
  | seq {es} : (∀ e ∈ es, MFrag e) → MFrag (.seq es)
  | ifElse {cond t els} :
      MFrag cond → MFrag t → MFrag els → MFrag (.if' cond t (some els))
  | ifNone {cond t} :
      MFrag cond → MFrag t → MFrag (.if' cond t none)
  | while' {c b} : MFrag c → MFrag b → MFrag (.while' c b)
  -- J22: sends. Block-less only (`blk = none` in the stored shape), and an explicit
  -- send named `call` stays out — `Judge.sendCall` eliminates arrows, and no
  -- machine-typed value witnesses one (J19). Argument shapes that take their own
  -- kont path (`splat`/`kwargs`/`fwd`) are excluded by having no constructor here,
  -- which is what lets the dispatch cases prove `startArgs` takes the plain branch.
  | self' : MFrag .self'
  | vcall {mname} : MFrag (.vcall mname)
  | send {r mname args} : mname ≠ "call" →
      MFrag r → (∀ a ∈ args, MFrag a) → MFrag (.send (some r) mname args none)
  | sendImplicit {mname args} :
      (∀ a ∈ args, MFrag a) → MFrag (.send none mname args none)
  -- J23: definition forms. The body gate is what the *promotion* derivation's
  -- installed row needs (`UserConformsJ` carries `MFrag body`); a reopen's body
  -- runs, so its gate is the eval arm's own.
  | def' {name params body} : MFrag body → MFrag (.def' name params body)
  | classTop {name body} : MFrag body → MFrag (.class' name none body)
  -- J26: the table-read heads and the array literal. A splat element has no
  -- constructor here, which is what keeps the literal's loop on the plain branch
  -- (`continueArray_plain`'s side conditions fall out of `MFrag`'s own emptiness
  -- at those shapes).
  | const {n} : MFrag (.const n)
  | varIvar {x} : MFrag (.var .ivar x)
  | varGvar {x} : MFrag (.var .gvar x)
  | vasgnIvar {x rhs} : MFrag rhs → MFrag (.vasgn .ivar x rhs)
  | vasgnGvar {x rhs} : MFrag rhs → MFrag (.vasgn .gvar x rhs)
  | array {es} : (∀ e ∈ es, MFrag e) → MFrag (.array es)

/-- The `Bool` form, on fuel (the L73 discipline: the J2 checker runs it under
    `decide`, so it must kernel-reduce; a nested-list structural recursion would
    not). Sound against `MFrag`; the fuel bound `sizeOf` always suffices. -/
def mfragB : Nat → Expr → Bool
  | 0, _ => false
  | n + 1, e =>
    match e with
    | .int _ | .flt _ | .str _ | .sym _ | .tru | .fls | .nil => true
    | .var .lvar _ => true
    | .vasgn .lvar _ rhs => mfragB n rhs
    | .seq es => es.all (mfragB n)
    | .if' cond t els =>
      mfragB n cond && mfragB n t &&
      (match els with | some e' => mfragB n e' | none => true)
    | .while' c b => mfragB n c && mfragB n b
    | .self' => true
    | .vcall _ => true
    | .send (some r) mname args none =>
      (mname != "call") && mfragB n r && args.all (mfragB n)
    | .send none _ args none => args.all (mfragB n)
    | .def' _ _ body => mfragB n body
    | .class' _ none body => mfragB n body
    | .const _ => true
    | .var .ivar _ => true
    | .var .gvar _ => true
    | .vasgn .ivar _ rhs => mfragB n rhs
    | .vasgn .gvar _ rhs => mfragB n rhs
    | .array es => es.all (mfragB n)
    | _ => false

theorem mfragB_sound : ∀ {n : Nat} {e : Expr}, mfragB n e = true → MFrag e := by
  intro n
  induction n with
  | zero => intro e h; exact absurd h (by simp [mfragB])
  | succ n ih =>
    intro e h
    match e with
    | .int _ => exact .int
    | .flt _ => exact .flt
    | .str _ => exact .str
    | .sym _ => exact .sym
    | .tru => exact .tru
    | .fls => exact .fls
    | .nil => exact .nil
    | .var .lvar _ => exact .varLvar
    | .vasgn .lvar _ rhs => exact .vasgnLvar (ih (by simpa [mfragB] using h))
    | .seq es =>
      simp only [mfragB, List.all_eq_true] at h
      exact .seq fun e' he' => ih (h e' he')
    | .if' cond t els =>
      simp only [mfragB, Bool.and_eq_true] at h
      obtain ⟨⟨hc, ht⟩, he2⟩ := h
      cases els with
      | some e' => exact .ifElse (ih hc) (ih ht) (ih (by simpa using he2))
      | none => exact .ifNone (ih hc) (ih ht)
    | .while' c b =>
      simp only [mfragB, Bool.and_eq_true] at h
      exact .while' (ih h.1) (ih h.2)
    | .self' => exact .self'
    | .vcall _ => exact .vcall
    | .send (some r) mname args none =>
      simp only [mfragB, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at h
      exact .send h.1.1 (ih h.1.2) fun a ha => ih (h.2 a ha)
    | .send none mname args none =>
      simp only [mfragB, List.all_eq_true] at h
      exact .sendImplicit fun a ha => ih (h a ha)
    | .def' _ _ body => exact .def' (ih (by simpa [mfragB] using h))
    | .class' _ none body => exact .classTop (ih (by simpa [mfragB] using h))
    | .const _ => exact .const
    | .var .ivar _ => exact .varIvar
    | .var .gvar _ => exact .varGvar
    | .vasgn .ivar _ rhs => exact .vasgnIvar (ih (by simpa [mfragB] using h))
    | .vasgn .gvar _ rhs => exact .vasgnGvar (ih (by simpa [mfragB] using h))
    | .array es =>
      simp only [mfragB, List.all_eq_true] at h
      exact .array fun e' he' => ih (h e' he')

end RubyCore.Judgment
