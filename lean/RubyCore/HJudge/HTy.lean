/-
  RubyCore.HJudge.HTy — the higher-order semantic type denotation.

  **The grammar's first four constructors are ported from `mdd/ruby-sorbet`'s
  `mdd/sorbet-lean/SorbetLean/Types.lean` (`STy`, spike S2.1)**: denotations
  are PURE heap-indexed predicates (`HTy.den : HTy → Heap → Value → Prop`),
  not iProp-native — under whole-heap `ownP` ownership every heap fact is
  pure relative to the owned σ, so `⌜τ.den h v⌝` alongside `stateIs h` is the
  honest form at this interpretation. The nominal core is `cls` via the
  machine's own `isA` ancestors walk (immediates included — `classOf` maps
  `.int` to Integer, etc.), plus `nilable` (Sorbet's `T.nilable`) and
  `untyped` (`T.untyped`, the trivially inhabited gradual type).

  Two additions beyond the sibling's grammar, each earning the H:

  * `union` — needed the moment the first-order `Ty` bridges in (`Ty.bool`
    denotes TrueClass ∪ FalseClass; Ruby has no Boolean class), and Sorbet's
    `T.any` shape besides.
  * `sem (P : Heap → Value → Prop)` — **the higher-order door.** A type IS a
    heap-indexed predicate here, so the constructor that admits an arbitrary
    one makes the denotation language semantically complete by construction.
    This is where behavioral duck typing enters today (`HTy.duck` below: "the
    heap's own `lookup` answers for these method names") and where
    heaplet/cell reasoning enters later — a separation-logic upgrade refines
    `sem`'s `Heap` parameter to a footprint (the `StateInterp.lean` gen_heap
    note is the same door seen from the Iris side), replacing this file's
    *lifting*, not its content (judgment-layer.md §1.5/§1.9: the nominal core
    stays first-order and solver-decidable; `sem` is the priced, explicit
    escape).

  What `sem` costs, stated: no `DecidableEq`, no `Repr`, no JSON transport —
  a certificate can name every `sem`-free `HTy`, and a `sem` type is exactly
  the part that must arrive as a Lean lemma instead (the J31 admission
  discipline, unchanged).

  House rules: no sorry, no new axioms.
-/
import RubyCore.Heap
import RubyCore.Types.Ty

set_option autoImplicit false

namespace RubyCore.HJudge

open RubyCore

/-- The H type grammar: the sibling's nominal core (`untyped`/`nilTy`/`cls`/
    `nilable`), plus `union`, plus the higher-order `sem` door. -/
inductive HTy where
  | untyped
  | nilTy
  | cls (c : ObjId)
  | nilable (τ : HTy)
  | union (σ τ : HTy)
  | sem (P : Heap → Value → Prop)

namespace HTy

/-- The denotation: a heap-indexed predicate on machine values. The `cls` arm
    is the machine's own `is_a?` — nominal, first-order, computable; the `sem`
    arm is the predicate itself. -/
def den : HTy → Heap → Value → Prop
  | .untyped, _, _ => True
  | .nilTy, _, v => v = .nil
  | .cls c, h, v => isA h v c = true
  | .nilable τ, h, v => v = .nil ∨ τ.den h v
  | .union σ τ, h, v => σ.den h v ∨ τ.den h v
  | .sem P, h, v => P h v

/-- Sorbet's ground types, as nominal abbreviations (the sibling's list,
    grown by the classes `Ty`'s ground arms name). -/
abbrev integer : HTy := .cls Boot.integerId
abbrev string : HTy := .cls Boot.stringId
abbrev symbol : HTy := .cls Boot.symbolId
abbrev float : HTy := .cls Boot.floatId
abbrev trueClass : HTy := .cls Boot.trueClassId
abbrev falseClass : HTy := .cls Boot.falseClassId
/-- `T::Boolean` — a union, exactly as Sorbet defines it (`TrueClass ∪
    FalseClass`); Ruby has no Boolean class, and `Ty.bool` could never say
    which half it meant. -/
abbrev boolean : HTy := .union trueClass falseClass

/-- **Behavioral duck typing, expressible today**: the values that respond to
    every named method *at this heap*, read off the machine's own `lookup`.
    A `define_method` that installs `m` moves a value INTO this type — the
    denotation is heap-indexed, so metaprogramming is visible, not assumed
    away. (What is NOT yet expressible: *behavioral* content of the methods —
    "responds to `each` with a block yielding τ" — which is the recorded
    step-indexing flip condition, judgment-layer.md §1.9.) -/
def duck (ms : List String) : HTy :=
  .sem fun h v => ∀ m ∈ ms, (lookup h v m).isSome

end HTy

/-! ## Self-membership of the ancestors walk

The fact that makes the immediate-value denotation lemmas **heap-generic**
(the sibling proved them at `Boot.initHeap` by `decide`; the H-layer needs
them at the *final heap of an arbitrary conformant run*, so they must hold at
every heap): `ancestors h k` contains `k` unconditionally — both arms of the
walk's first unfolding include the start id, and the dedup fold preserves
membership. -/

private theorem mem_of_contains {l : List ObjId} {x : ObjId}
    (hc : l.contains x = true) : x ∈ l :=
  List.mem_of_elem_eq_true hc

private theorem contains_of_mem {l : List ObjId} {x : ObjId} (hx : x ∈ l) :
    l.contains x = true :=
  List.elem_eq_true_of_mem hx

/-- The dedup fold keeps everything already in the accumulator and everything
    in the input. -/
private theorem mem_foldl_dedup :
    ∀ (l : List ObjId) (acc : List ObjId) (x : ObjId), x ∈ acc ∨ x ∈ l →
      x ∈ l.foldl (fun acc y => if acc.contains y then acc else acc ++ [y]) acc
  | [], _, _, hx => hx.elim id (fun h => absurd h (List.not_mem_nil))
  | y :: l, acc, x, hx => by
    simp only [List.foldl_cons]
    refine mem_foldl_dedup l _ x ?_
    rcases hx with hacc | hyl
    · left
      split
      · exact hacc
      · exact List.mem_append_left _ hacc
    · rcases List.mem_cons.mp hyl with rfl | hl
      · left
        split
        · next hc => exact mem_of_contains hc
        · exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      · right
        exact hl

/-- `k ∈ ancestors h k`, at **every** heap: the walk's first unfolding
    contains the start id in both `classPayload?` arms. -/
theorem self_mem_ancestors (h : Heap) (k : ObjId) : k ∈ ancestors h k := by
  unfold ancestors
  refine mem_foldl_dedup _ [] k (Or.inr ?_)
  show k ∈ ancestors.go h k (h.objs.size + 1)
  rw [ancestors.go]
  cases hcp : h.classPayload? k with
  | none => simp
  | some c => simp

/-- `is_a?` at the value's own dispatch class holds at every heap. -/
theorem isA_classOf {h : Heap} {v : Value} {k : ObjId}
    (hc : classOf h v = k) : isA h v k = true := by
  unfold isA
  rw [hc]
  exact contains_of_mem (self_mem_ancestors h k)

/-! ## Denotation introduction, heap-generic (the immediates' `classOf` reads
    no heap, so each is one `isA_classOf`) -/

namespace HTy

theorem den_int (h : Heap) (n : Int) : integer.den h (.int n) :=
  isA_classOf rfl

theorem den_flt (h : Heap) (x : Float) : float.den h (.flt x) :=
  isA_classOf rfl

theorem den_sym (h : Heap) (s : String) : symbol.den h (.sym s) :=
  isA_classOf rfl

theorem den_true (h : Heap) : trueClass.den h (.bool true) :=
  isA_classOf rfl

theorem den_false (h : Heap) : falseClass.den h (.bool false) :=
  isA_classOf rfl

theorem den_bool (h : Heap) (b : Bool) : boolean.den h (.bool b) := by
  cases b
  · exact Or.inr (den_false h)
  · exact Or.inl (den_true h)

theorem den_nil (h : Heap) : nilTy.den h .nil := rfl

/-- `nilable` introduction, both arms. -/
theorem den_nilable_nil {h : Heap} (τ : HTy) : (nilable τ).den h .nil :=
  Or.inl rfl

theorem den_nilable_of {h : Heap} {τ : HTy} {v : Value} (hv : τ.den h v) :
    (nilable τ).den h v := Or.inr hv

/-- `untyped` is trivially inhabited — the gradual type. -/
theorem den_untyped {h : Heap} (v : Value) : untyped.den h v := trivial

end HTy

/-! ## `HSub` — semantic subtyping

A subtype IS a denotation inclusion — no syntactic relation, no rules to
trust, and `sem` types participate on equal footing (this is the choice the
sibling's S5 backlog priced as "union types" and the judgment layer's `SubJ`
approximates syntactically; here the semantic definition is primary and any
syntactic checker would be an *untrusted emitter* against it). -/

/-- `σ` is a semantic subtype of `τ`: the denotation inclusion, at every heap. -/
def HSub (σ τ : HTy) : Prop :=
  ∀ (h : Heap) (v : Value), σ.den h v → τ.den h v

namespace HSub

theorem refl (τ : HTy) : HSub τ τ := fun _ _ hv => hv

theorem trans {σ τ ρ : HTy} (h₁ : HSub σ τ) (h₂ : HSub τ ρ) : HSub σ ρ :=
  fun h v hv => h₂ h v (h₁ h v hv)

/-- Everything is below `untyped` — the gradual top. -/
theorem le_untyped (τ : HTy) : HSub τ .untyped := fun _ _ _ => trivial

theorem le_nilable (τ : HTy) : HSub τ (.nilable τ) := fun _ _ hv => Or.inr hv

theorem nil_le_nilable (τ : HTy) : HSub .nilTy (.nilable τ) :=
  fun _ _ hv => Or.inl hv

theorem nilable_mono {σ τ : HTy} (hs : HSub σ τ) :
    HSub (.nilable σ) (.nilable τ) :=
  fun h v hv => hv.imp id (hs h v)

theorem nilable_lub {σ ρ : HTy} (hn : HSub .nilTy ρ) (hs : HSub σ ρ) :
    HSub (.nilable σ) ρ :=
  fun h v hv => hv.elim (fun he => hn h v he) (hs h v)

theorem le_union_left (σ τ : HTy) : HSub σ (.union σ τ) :=
  fun _ _ hv => Or.inl hv

theorem le_union_right (σ τ : HTy) : HSub τ (.union σ τ) :=
  fun _ _ hv => Or.inr hv

theorem union_lub {σ τ ρ : HTy} (h₁ : HSub σ ρ) (h₂ : HSub τ ρ) :
    HSub (.union σ τ) ρ :=
  fun h v hv => hv.elim (h₁ h v) (h₂ h v)

theorem union_mono {σ σ' τ τ' : HTy} (h₁ : HSub σ σ') (h₂ : HSub τ τ') :
    HSub (.union σ τ) (.union σ' τ') :=
  union_lub (h₁.trans (le_union_left σ' τ')) (h₂.trans (le_union_right σ' τ'))

/-- `sem` on the right: any pointwise implication is a subtyping — the
    higher-order door swings both ways. -/
theorem le_sem {σ : HTy} {P : Heap → Value → Prop}
    (h : ∀ hp v, σ.den hp v → P hp v) : HSub σ (.sem P) := h

theorem sem_le {P : Heap → Value → Prop} {τ : HTy}
    (h : ∀ hp v, P hp v → τ.den hp v) : HSub (.sem P) τ := h

end HSub

/-! ## The bridge from the first-order type language

`Ty → Option HTy`, partial on purpose — each `none` names a bill:

* `cls name` / `clsOf name` — `Ty` keys classes by **name** (a checker is a
  pure function of the program; `judgment-layer.md` §1.1) while `HTy.cls`
  keys by **`ObjId`** (a denotation reads the heap). Tying a name to an id is
  a *per-heap* resolution fact, so the honest bridge for these arms is a
  conformance-conditioned lemma (the `LitClsOk`-shape), not a pure function —
  a recorded rung, not taken here.
* `arrayOf` — the element denotation reads the heap through the payload; a
  cyclic array must denote nothing (`ValueTy`'s L238 lesson). Needs a
  fuel-graded or relationally-defined arm; recorded.
* `arrow0`/`arrowCons` — value-level behavioral types; THE step-indexing flip
  condition (§1.9). `sem` can state one today; the bridge cannot manufacture
  one from a `Ty` spine. Recorded.

Everything the machine-typed fragment can *produce* today (`valueTy?`'s range
is atoms; J1's answer types are ground) bridges. -/

/-- The nominal bridge from `Ty`. -/
def HTy.ofTy? : Types.Ty → Option HTy
  | .int => some HTy.integer
  | .bool => some HTy.boolean
  | .nilT => some .nilTy
  | .sym => some HTy.symbol
  | .float => some HTy.float
  | .any => some .untyped
  | .nilable τ => (HTy.ofTy? τ).map .nilable
  | .union σ τ =>
    match HTy.ofTy? σ, HTy.ofTy? τ with
    | some a, some b => some (.union a b)
    | _, _ => none
  | .cls _ => none
  | .clsOf _ => none
  | .arrayOf _ => none
  | .arrow0 _ => none
  | .arrowCons _ _ => none

end RubyCore.HJudge
