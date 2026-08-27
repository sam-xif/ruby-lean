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

* an `if` whose condition is a **bare local read** is out until the narrowing rung —
  the same expression admits `Judge.ifNarrowElse/ifNarrowNone` derivations, whose
  delivery needs the value↔store correlation (the push-time case-split of
  `DESIGN-NOTES.md`); gating the shape defers those cases without touching the spec;
* a send named **`call`** stays out even after sends land — `Judge.sendCall`
  eliminates arrows, and no machine-typed value witnesses an arrow yet (J19).
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
  | ifElse {cond t els} : (∀ x, cond ≠ .var .lvar x) →
      MFrag cond → MFrag t → MFrag els → MFrag (.if' cond t (some els))
  | ifNone {cond t} : (∀ x, cond ≠ .var .lvar x) →
      MFrag cond → MFrag t → MFrag (.if' cond t none)
  | while' {c b} : MFrag c → MFrag b → MFrag (.while' c b)

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
      (match cond with | .var .lvar _ => false | _ => true) &&
      mfragB n cond && mfragB n t &&
      (match els with | some e' => mfragB n e' | none => true)
    | .while' c b => mfragB n c && mfragB n b
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
      obtain ⟨⟨⟨hshape, hc⟩, ht⟩, he2⟩ := h
      have hnl : ∀ x, cond ≠ .var .lvar x := by
        intro x hq
        subst hq
        simp at hshape
      cases els with
      | some e' => exact .ifElse hnl (ih hc) (ih ht) (ih (by simpa using he2))
      | none => exact .ifNone hnl (ih hc) (ih ht)
    | .while' c b =>
      simp only [mfragB, Bool.and_eq_true] at h
      exact .while' (ih h.1) (ih h.2)

end RubyCore.Judgment
