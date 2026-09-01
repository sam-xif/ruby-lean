import Denote.Den

/-!
# `Denote/Arrow.lean` — the arrow, uncurried and stabilised

`Denote/Den.lean` states the arrow one parameter at a time, because `Ty`'s arrow is a
**spine** (`arrowCons A (arrowCons B (arrow0 R))`) and the denotation has to recurse on the
spine to stay structural. Nobody wants to *use* it in that shape. This file provides the flat
statement — "for every argument list in the domain, every returned value is in the codomain"
— and proves the two agree (`denM_arrowOf`), which is the lemma any consumer of an arrow
type actually cites.

It then adds the piece the spine version cannot express: **stability under execution**
(`ArrowStable`). `denM (arrowOf ps r) m f` is a claim about calling `f` *at `m`*. A lambda is
normally called later, from a state the program ran on to, and a checker that inferred an
arrow at the creation site needs the claim to survive that. So the useful obligation is
universally quantified over machines reachable from the creation state, and `Reaches`
(`Denote/Apply.lean`) is the quantifier. Two things worth saying about it:

* It is **strictly stronger**, and provably so in the trivial direction only
  (`ArrowStable.here`): a proof of stability gives you the local claim at the start state,
  and no amount of local claims gives you stability. That asymmetry is exactly the price of
  Ruby's open classes — `define_method` on a class the lambda's body dispatches to can
  invalidate a local arrow, and a stable arrow is one that has already accounted for it.
* It is **not** what the current checker infers. `Ratchet.Ty.clos` is a reference to a block's
  *code*, and `Judge.closCall` instantiates the body at the call site's argument types
  (`Ty.clos`'s docstring says why: Ruby writes no parameter types, so there is no principal
  arrow to infer). So `ArrowStable` is the specification a future arrow-inferring rule would
  have to meet, and `ClosArrow` is the shape of the bridge from what is inferred today to it.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-- Pointwise denotation of an argument list. A length mismatch is `False`, matching
`Ratchet.subTys`'s treatment of the same situation on the syntactic side. -/
def DenAll : List Ty → Machine → List Value → Prop
  | [], _, [] => True
  | τ :: τs, m, v :: vs => denM τ m v ∧ DenAll τs m vs
  | _, _, _ => False

@[simp] theorem DenAll_nil_nil (m : Machine) : DenAll [] m [] ↔ True := Iff.rfl
@[simp] theorem DenAll_nil_cons (m : Machine) (v : Value) (vs : List Value) :
    DenAll [] m (v :: vs) ↔ False := Iff.rfl
@[simp] theorem DenAll_cons_nil (τ : Ty) (τs : List Ty) (m : Machine) :
    DenAll (τ :: τs) m [] ↔ False := Iff.rfl
@[simp] theorem DenAll_cons_cons (τ : Ty) (τs : List Ty) (m : Machine)
    (v : Value) (vs : List Value) :
    DenAll (τ :: τs) m (v :: vs) ↔ (denM τ m v ∧ DenAll τs m vs) := Iff.rfl

/-- **The flat arrow.** `f` is a Proc, and every call of it on arguments in the domain that
*returns* returns a value in the codomain — checked at the machine the call produced.

Read the two quantifier positions: `args` is a hypothesis (so the domain is contravariant)
and `v` is a conclusion (so the codomain is covariant), and neither variance is stipulated
anywhere — they are consequences of where the arguments sit. -/
def ArrowFlat (ps : List Ty) (r : Ty) (m : Machine) (f : Value) : Prop :=
  isProcV m.heap f = true ∧
  ∀ args, DenAll ps m args → ∀ v m', Returns m f args v m' → denM r m' v

/-- The spine walk, unrolled: `denApp` on `arrowOf ps r` with accumulator `acc` is the flat
statement about calls whose argument list is `acc` followed by a domain-satisfying tail. -/
theorem denApp_arrowOf : ∀ (ps : List Ty) (r : Ty) (m : Machine) (f : Value)
    (acc : List Value),
    denApp acc (arrowOf ps r) m f ↔
      ∀ args, DenAll ps m args → ∀ v m', Returns m f (acc ++ args) v m' → denM r m' v
  | [], r, m, f, acc => by
    simp only [arrowOf, denApp]
    constructor
    · intro h args ha
      match args with
      | [] => simpa using h
      | _ :: _ => simp at ha
    · intro h v m' hr
      exact h [] trivial v m' (by simpa using hr)
  | p :: ps, r, m, f, acc => by
    simp only [arrowOf, denApp]
    constructor
    · intro h args ha
      match args with
      | [] => simp at ha
      | a :: rest =>
        have := (denApp_arrowOf ps r m f (acc ++ [a])).mp (h a ha.1) rest ha.2
        intro v m' hr
        exact this v m' (by simpa using hr)
    · intro h a hpa
      refine (denApp_arrowOf ps r m f (acc ++ [a])).mpr ?_
      intro rest hrest v m' hr
      exact h (a :: rest) ⟨hpa, hrest⟩ v m' (by simpa using hr)

/-- **The agreement**: the spine denotation of an arrow is the flat one. This is the lemma to
cite; `denM`'s arrow arms are an implementation detail of staying structural. -/
theorem denM_arrowOf (ps : List Ty) (r : Ty) (m : Machine) (f : Value) :
    denM (arrowOf ps r) m f ↔ ArrowFlat ps r m f := by
  match ps with
  | [] =>
    simp only [arrowOf, denM, ArrowFlat]
    refine and_congr_right fun _ => ⟨fun h args ha => ?_, fun h v m' hr => ?_⟩
    · match args with
      | [] => simpa using h
      | _ :: _ => simp at ha
    · exact h [] trivial v m' hr
  | p :: ps =>
    simp only [arrowOf, denM, ArrowFlat]
    refine and_congr_right fun _ => ⟨fun h args ha => ?_, fun h a hpa => ?_⟩
    · match args with
      | [] => simp at ha
      | a :: rest =>
        have := (denApp_arrowOf ps r m f [a]).mp (h a ha.1) rest ha.2
        intro v m' hr
        exact this v m' (by simpa using hr)
    · refine (denApp_arrowOf ps r m f [a]).mpr ?_
      intro rest hrest v m' hr
      exact h (a :: rest) ⟨hpa, hrest⟩ v m' (by simpa using hr)

/-! ## Stability under execution -/

/-- **The stable arrow**: the flat arrow holds at *every machine reachable from `m₀`*, not
only at `m₀`. See the module docstring for why this, and not `ArrowFlat`, is what a
call-it-later arrow type has to mean. -/
def ArrowStable (ps : List Ty) (r : Ty) (m₀ : Machine) (f : Value) : Prop :=
  ∀ m, Reaches m₀ m → ArrowFlat ps r m f

theorem ArrowStable.here {ps : List Ty} {r : Ty} {m₀ : Machine} {f : Value}
    (h : ArrowStable ps r m₀ f) : ArrowFlat ps r m₀ f :=
  h m₀ (.refl m₀)

/-- Stability is inherited by every reachable state — the property that makes it usable as an
invariant rather than as a one-off claim. -/
theorem ArrowStable.mono {ps : List Ty} {r : Ty} {m₀ m : Machine} {f : Value}
    (h : ArrowStable ps r m₀ f) (hr : Reaches m₀ m) : ArrowStable ps r m f :=
  fun m' hr' => h m' (hr.trans hr')

/-- **The bridge.** What the checker infers for a lambda today is a `Ty.clos` — a reference to
the block's code plus its captured scope (`Ty.clos`'s docstring: Ruby writes no parameter
types, so there is no arrow to infer). What a caller wants is an arrow. `ClosArrow` is the
conjunction, and stating it is the point: a soundness proof for `Judge.closCall` is exactly a
proof that a value in the `clos` denotation, whose body checks at the call site's argument
types, is in the corresponding arrow denotation — i.e. that `denM κ m f → ArrowFlat ps r m f`
for the `ps`/`r` the rule computed. Not proved here; `Denote/` is the specification side. -/
def ClosArrow (κ : Ty) (ps : List Ty) (r : Ty) (m : Machine) (f : Value) : Prop :=
  denM κ m f ∧ ArrowFlat ps r m f

#print axioms denApp_arrowOf
#print axioms denM_arrowOf
#print axioms ArrowStable.mono

end Ratchet.Denote
