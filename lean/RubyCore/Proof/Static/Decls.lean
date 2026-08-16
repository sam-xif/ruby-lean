import RubyCore.Proof.Static.Locals

/-!
# F1a — the refinement invariant

`PLAN.md` **D10**, `homebrew/typing-a-mutable-method-table.md` §2 and §7. The
heap-side clause of the machine invariant, restated from an equality into a lower
bound:

> **For every method the declarations name, `lookup` resolves it to something
> conforming to its declared signature.**

## Why this, and not "the table matches the declarations"

The equality reading excludes ordinary Ruby, and — the counterexample that forced
the change — it excludes **`sorbet-runtime` itself**, which installs a `sig` by
replacing the method-table entry with a validating wrapper. So the
declaration-matching fragment could not type a single annotated method
(`Types/Fragment.lean`'s header, L139).

The lower bound has the property the equality was reaching for anyway: a
type-stuck outcome comes from a method being **missing** or **wrong-typed**, never
from one being present and unmentioned. So `DeclsOk` says nothing at all about
undeclared names, is therefore **monotone in the method table**, and every
additive step preserves it with no side condition. `DeclsOk_defineMethod` is that
statement, and the only side condition it carries is that the `def` does not
displace a *declared* name — a redefinition, which is F1c's checkable case.

## The decomposition, which is the substance rather than the restatement

Each entry splits into two clauses that behave differently under a heap write:

* **`ResolvesTo`** — resolution: the name reaches a builtin, live, public,
  unshadowed. Heap-dependent, and the *only* thing preservation has to re-derive.
  `Proof/HeapFacts.lean`'s `defineMethod` chain is exactly what discharges it.
* **`ConformsAt`** — conformance: applied to arguments of the declared parameter
  types, that builtin answers a value of the declared return type. Its two
  conclusions are **heap-uniform** (`∀ h'`), which is what makes it transport for
  free; its hypotheses read the invariant's heap, which is where F1b's nominal
  types will need to read it.

That split is why P0's three `int_*_dispatch` rewrites collapse into one
`entry_dispatch`, and why §7's *"the ~128 `builtinSig` conformance lemmas become
per-entry witnesses of the invariant rather than a parallel obligation"* is now
literally true: a new entry is a `ConformsAt` proof and nothing else.

`TableOk` is kept, unchanged, as the **certificate-shaped** form of the same fact
— `heapOkB` decides it and `scripts/heapok_probe.lean` reports it, so F0 is
untouched — and `tableOk_declsOk` is the bridge. That direction (concrete ⇒
general) is deliberate: the invariant carries the general statement, and the
runtime checks the concrete one.
-/

namespace RubyCore
namespace Proof
namespace Static

open Interp
open RubyCore.Types

set_option maxRecDepth 100000

/-! ## 1. Resolution and conformance -/

/-- **Resolution.** In heap `h`, sending `mname` to `recv` reaches the builtin
    `bid`: the table resolves it, the entry is live, public and not
    prelude-suppressed, and neither shadow gate fires.

    Generalizes `IntBuiltinResolves` from the fixed receiver `.int 0` to an
    arbitrary value, and costs **no** extra clause, which is worth recording
    because it was not obvious: `crubySingletonShadow` looked like it would need
    carrying for an abstract receiver, and does not — `invoke` consults that gate
    only when lookup did *not* resolve to a builtin, so an entry satisfying this
    predicate never reaches it. Measured by the proof of `entry_dispatch` not
    using it.

    **Re-measured at F1b and still true** (L141), against a prediction that it
    would not be: `HANDOFF.md` expected an object receiver to bring the singleton
    gate back. It does not, because the gate is a fact about which *branch* runs
    (`md.builtin = none`) and not about which *receiver* arrives, and this
    predicate pins the branch. -/
def ResolvesTo (h : Heap) (recv : Value) (mname bid : String) : Prop :=
  ∃ owner md,
    lookup h recv mname = some (owner, md) ∧
    md.builtin = some bid ∧
    md.undefined = false ∧
    md.visibility = .pub ∧
    md.fromPrelude = false ∧
    crubyShadow h ((ancestors h (classOf h recv)).takeWhile (· != owner)) mname = none

/-- **Conformance to a declared signature.** On a receiver of the declared class
    and arguments of the declared parameter types, `bid` answers a value of the
    declared return type without touching the machine, and defers to no prelude
    twin.

    The name clause excludes `send`/`public_send`/`__send__`, which `invoke` treats
    specially: their *first argument* is the real method name, so a declared
    signature for them would describe the wrong call. This is the same exclusion
    `int_bin_dispatch` carried as an explicit hypothesis, promoted to part of what
    conformance means.

    The deferral clause is `∀ h'` on purpose. L116 put a **prelude-twin deferral**
    in front of every builtin — one whose answer would need a dispatch it cannot
    perform hands the call to prelude Ruby instead of running — and `deferTwin?`
    reads the *method table*, so a heap write can change it. Requiring the
    deferral to be absent in every heap is what makes conformance survive a `def`;
    for arithmetic over two Integers it is true by computation, and an entry for
    which it is false does not belong in the table at all.

    **Heap-uniform since L146, and that is a change of statement rather than of
    strength.** It used to be indexed by the invariant's heap, with the machine
    quantified *inside* the existential — so `∀ m, run … m = .ok w m` (heap-uniform
    conclusion) sat under `ValueTy h recv τr` (heap-*dependent* hypothesis). The
    asymmetry cost a transport: `ConformsAt_defineMethod` had to read its hypotheses
    in the old heap and its conclusion in the new one, which is the only reason
    `TypeAgree` needed a backward direction at all (L143) — and the backward
    direction **does not exist for a growing heap**, so the producer could not have
    had it.

    Quantifying the machine over the whole statement fixes both: conformance is now
    a fact about a builtin and a declaration, mentioning no heap, so it is not a
    clause preservation has to re-establish. `DeclsOk`'s heap-dependent half is
    exactly `ResolvesTo` — which is what L140's split said it should be, one level
    more honestly than L140 achieved. Every witness's *proof* is unchanged: the
    hypotheses it actually used were `valueTy_int`-shaped inversions, and those are
    heap-independent. -/
def ConformsAt (τr : Ty) (mname bid : String) (d : MethodDecl) : Prop :=
  (mname == "send" || mname == "public_send" || mname == "__send__") = false ∧
  bid ≠ "Object#raise" ∧
  ∀ (m : Machine) recv args, ValueTy m.heap recv τr → ValuesTy m.heap args d.params →
    (∀ h' : Heap, Builtins.deferTwin? h' bid recv args = none) ∧
    ∃ w, ValueTy m.heap w d.ret ∧ Builtins.run bid recv args m = .ok w m

/-- One declared method, satisfied: **some** builtin both resolves for every
    receiver of the class and conforms. Existential in `bid` rather than pinning
    it, which is what makes the condition a lower bound — the invariant never says
    *which* implementation answers, only that a conforming one does. -/
def EntryOk (h : Heap) (τr : Ty) (mname : String) (d : MethodDecl) : Prop :=
  ∃ bid, (∀ recv, ValueTy h recv τr → ResolvesTo h recv mname bid) ∧
    ConformsAt τr mname bid d

/-- **The refinement invariant.** Note what is *not* here: no clause about names
    the table does not declare, and no upper bound on the heap's method table.
    That absence is the whole content of D10. -/
def DeclsOk (D : Decls) (h : Heap) : Prop :=
  ∀ τr mname d, declFor D τr mname = some d → EntryOk h τr mname d

/-! ## 2. The uniform dispatch step

What the `argsK` case of preservation needs, once per declared method instead of
once per tabulated builtin. This is `int_bin_dispatch` with the three
`Integer`-specific hypotheses replaced by `EntryOk`.
-/

theorem entry_dispatch {m : Machine} {τr : Ty} {mname : String} {d : MethodDecl}
    {recv : Value} {args : List Value}
    (he : EntryOk m.heap τr mname d)
    (hrv : ValueTy m.heap recv τr) (hargs : ValuesTy m.heap args d.params) :
    ∃ w, ValueTy m.heap w d.ret ∧
      startArgs m recv .explicit mname args [] .none
        = .next (withCtl m (.value w)) := by
  obtain ⟨bid, hres, hns, hraise, hconf⟩ := he
  obtain ⟨owner, md, hlook, hb, hu, hvis, hpre, hbtw⟩ := hres recv hrv
  obtain ⟨hdefer, w, hw, hrun⟩ := hconf m recv args hrv hargs
  refine ⟨w, hw, ?_⟩
  simp only [startArgs, finishSend]
  rw [invoke.eq_def]
  -- The receiver has to be case-split, and the reason is worth stating: `invoke`
  -- has receiver-shape special cases *before* the resolved-builtin path (a `.proc`
  -- answers `call`, a `.hsh` with a proc default answers `[]`, and a `.cls` reaches
  -- `invokeMaybeNew` or the `Math`/`Regexp` singleton arms), so an abstract
  -- receiver leaves them standing.
  --
  -- **F1a closed them by there being no inhabitant** — every one is a `.ref` and
  -- `valueTy?` had no `.ref` arm. F1b closes them by a hypothesis instead:
  -- `plainRecv` is exactly the negation of the three payload shapes, and it is part
  -- of what the class arm of `valueTy?` *means*, so the inversion hands it over
  -- (`valueTy_shapes`). The special cases are still discharged by the type
  -- judgement; what changed is that the judgement now has to say so out loud.
  rcases valueTy_shapes hrv with ⟨a, rfl⟩ | ⟨b, rfl⟩ | rfl | ⟨sy, rfl⟩ | ⟨o, rfl, hplain⟩
  -- The four immediate cases are F1a's, unchanged: `invoke`'s receiver-shape arms
  -- are all `.ref`, so the outer match falls straight through.
  case' inr.inr.inr.inr =>
    -- The `.ref` case, which is F1b's whole bill. Case on the payload: `plainRecv`
    -- refutes the three special arms and the rest reach `invokeDispatch`, which is
    -- what `ResolvesTo` describes. Note this does **not** need
    -- `crubySingletonShadow`: that gate sits on `invoke`'s `md.builtin = none`
    -- branch (`Interp/Send.lean:246`) and `ResolvesTo` pins `md.builtin = some bid`,
    -- so F1a's measurement survives an abstract object receiver unchanged.
    cases hpl : (m.heap.get o).payload
    -- The three special shapes, refuted by `plainRecv` rather than reasoned about.
    case proc => exact absurd hplain (by simp [plainRecv, hpl])
    case hsh => exact absurd hplain (by simp [plainRecv, hpl])
    case cls => exact absurd hplain (by simp [plainRecv, hpl])
    -- Everything else is the uniform path, and identical to the immediate cases.
    all_goals
      simp [invoke.invokeDispatch, hpl, hlook, hb, hu, hbtw, hpre, visError?, hvis,
        appendKwHash, hrun, hns, hdefer, hraise]
  all_goals
    simp [invoke.invokeDispatch, hlook, hb, hu, hbtw, hpre, visError?, hvis,
      appendKwHash, hrun, hns, hdefer, hraise]

/-! ## 3. Preservation: the additive step is free

The D10 claim, as a lemma. `defineMethod` of a name the declarations do not
mention leaves every declared entry alone: `lookup` is unchanged by
name-disjointness (`Proof/HeapFacts.lean`), and conformance is heap-uniform where
it has to be.
-/

/-- A declared method's name is declared. Needed to turn the *syntactic* side
    condition `declaresName D name = false` — what `infer` checks on a `def` —
    into the name-disjointness `lookup_defineMethod` wants. -/
theorem declOf?_declaresName {D : Decls} {cls name : String} {d : MethodDecl}
    (h : declOf? D cls name = some d) : declaresName D name = true := by
  unfold declOf? declsFor at h
  cases hf : D.find? (·.1 == cls) with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some cd =>
    rw [hf] at h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨e, he, _⟩ := h
    have hp := List.find?_some he
    exact List.any_eq_true.mpr
      ⟨cd, List.mem_of_find?_eq_some hf,
        List.any_eq_true.mpr ⟨e, List.mem_of_find?_eq_some he, hp⟩⟩

theorem declFor_declaresName {D : Decls} {τ : Ty} {mname : String} {d : MethodDecl}
    (h : declFor D τ mname = some d) : declaresName D mname = true := by
  have key : ∀ (c : String) (cs : List String),
      (match declOf? D c mname with
       | none => none
       | some d0 =>
         if cs.all (fun c' => declOf? D c' mname == some d0) then some d0 else none)
        = some d → declaresName D mname = true := by
    intro c cs hh
    cases hd : declOf? D c mname with
    | none => rw [hd] at hh; exact absurd hh (by simp)
    | some d0 => exact declOf?_declaresName hd
  -- The class arm (F1b) is the only one that is not immediate: the key is a
  -- variable, and `tyClassNames` can answer `[]` (for a ground name), which
  -- `declFor` reads as no declaration.
  cases τ <;> (unfold declFor at h; simp only [tyClassNames] at h)
  case cls n =>
    by_cases hg : groundClassNames.contains n = true
    · rw [if_pos hg] at h; exact absurd h (by simp)
    · rw [if_neg hg] at h; exact key n [] h
  all_goals
    first
      | exact key "Integer" [] h
      | exact key "TrueClass" ["FalseClass"] h
      | exact key "NilClass" [] h
      | exact key "Symbol" [] h

theorem ResolvesTo_defineMethod {h : Heap} {recv : Value} {mname bid : String}
    {cls : ObjId} {name : String} {md : MethodDef}
    (hr : ResolvesTo h recv mname bid) (hne : ¬ (mname = name)) :
    ResolvesTo (defineMethod h cls name md) recv mname bid := by
  obtain ⟨owner, md0, hlook, hb, hu, hvis, hpre, hbtw⟩ := hr
  have hco := classOf_defineMethod h cls name md recv
  refine ⟨owner, md0, ?_, hb, hu, hvis, hpre, ?_⟩
  · rw [lookup_defineMethod h cls name mname md recv hne hco]; exact hlook
  · rw [hco, ancestors_defineMethod, crubyShadow_defineMethod]; exact hbtw

/-- **Resolution reads the receiver only through its dispatch class** (L145), and
    this is the fact that will make an allocation harmless where a `def` is not.
    `lookup` is `lookup.go` over `ancestors h (classOf h recv)` and the shadow chain
    is the same walk, so `ResolvesTo` factors through `classOf` — two rewrites, and a
    consequence worth stating on its own:

    **a new object of an existing class carries no new resolution obligation.** Every
    receiver of a class the declarations name resolves iff any one of them does, so
    `DeclsOk`'s ∀-receiver clause is really a statement about *classes*, and
    allocation adds no class. That is what the producer's consecution case needs for
    the receiver the old heap did not have — the case `ResolvesTo_grow` below cannot
    reach — and it says the right restatement of the clause is class-indexed rather
    than inhabitant-indexed. -/
theorem ResolvesTo_classOf {h : Heap} {recv recv' : Value} {mname bid : String}
    (heq : classOf h recv' = classOf h recv)
    (hr : ResolvesTo h recv mname bid) : ResolvesTo h recv' mname bid := by
  obtain ⟨owner, md0, hlook, hb, hu, hvis, hpre, hbtw⟩ := hr
  refine ⟨owner, md0, ?_, hb, hu, hvis, hpre, ?_⟩
  · unfold lookup at hlook ⊢
    rw [heq]; exact hlook
  · rw [heq]; exact hbtw

/-- **Resolution survives an allocating step** (L145). Every clause of
    `ResolvesTo` is a fact about the method table, the ancestor walk or the shadow
    gate, and `PlainGrow` pins all three — the two congruences it needs are
    `lookup_grow` (which is where `Saturated` enters, through `ancestors`) and
    `crubyShadow_grow`.

    The receiver has to be an id the old heap had, which is exactly what a
    `ValueTy m.heap recv τr` hypothesis supplies at the use site
    (`valueTy_ref_lt`). Note what is **not** required: nothing about the fresh
    object, because resolution never looks at it.

    Contrast `ResolvesTo_defineMethod`, whose side condition is a *name*
    disjointness: a write to an existing table can displace an entry, an allocation
    cannot. That asymmetry is why the producer's step is cheaper here than the `def`
    rule's and dearer in `ConformsAt`. -/
theorem ResolvesTo_grow {h h' : Heap} {recv : Value} {mname bid : String}
    (hg : PlainGrow h h') (hsat : Saturated h)
    (hrv : ∀ o, recv = .ref o → o < h.objs.size)
    (hr : ResolvesTo h recv mname bid) : ResolvesTo h' recv mname bid := by
  obtain ⟨owner, md0, hlook, hb, hu, hvis, hpre, hbtw⟩ := hr
  refine ⟨owner, md0, ?_, hb, hu, hvis, hpre, ?_⟩
  · rw [lookup_grow hg hsat hrv mname]; exact hlook
  · rw [hg.classOf_value_eq recv hrv, hg.ancestors_eq hsat, crubyShadow_grow hg]
    exact hbtw

/-! ~~`ConformsAt_defineMethod`~~ is **withdrawn** (L146) rather than repaired.
`ConformsAt` no longer mentions a heap, so a heap-writing step has nothing to
re-establish about it and the lemma has no content. It is worth recording what it
*was*: the only consumer of `TypeAgree`'s backward direction — the one L143 had to
supply specially, and the one a growing step cannot supply at all. Deleting the
clause deleted the obligation. -/

/-- **The additive step preserves the invariant, with no condition beyond
    non-displacement.** D10's claim, and the reason `infer`'s `def` rule checks
    `declaresName` rather than a list of names. -/
theorem DeclsOk_defineMethod {D : Decls} {h : Heap} {cls : ObjId} {name : String}
    {md : MethodDef} (hd : DeclsOk D h) (hfresh : declaresName D name = false) :
    DeclsOk D (defineMethod h cls name md) := by
  intro τr mname decl hdecl
  have hne : ¬ (mname = name) := by
    intro heq
    rw [heq] at hdecl
    exact absurd (declFor_declaresName hdecl) (by simp [hfresh])
  obtain ⟨bid, hres, hconf⟩ := hd τr mname decl hdecl
  -- `hconf` passes straight through (L146): it is a fact about `bid` and `decl`, not
  -- about this heap. What is left is the resolution clause, and its `ValueTy`
  -- hypothesis still runs backwards — which `defineMethod` can supply and a growing
  -- step cannot (`DeclsOk_grow`).
  refine ⟨bid, fun recv hrv => ?_, hconf⟩
  exact ResolvesTo_defineMethod
    (hres recv (ValueTy.congr (typeAgree_defineMethod' h cls name md) hrv)) hne

/-- **The invariant survives an allocating step** (L146), and after L146's
    restatement the whole content is resolution — `hconf` passes through untouched
    because conformance no longer mentions a heap.

    The side condition is the one L145 predicted, in the form `ResolvesTo_classOf`
    consumes: *every receiver the new heap types was already typed by some receiver
    of the same dispatch class*. It is what a fresh inhabitant of a declared class
    forces, and it is the honest one — resolution is a fact about a class, so a new
    object needs no new proof provided its class is not new either.

    Note which hypothesis is **absent**: nothing about the backward type transport,
    which is what `DeclsOk_defineMethod` needs and what a growing heap cannot give
    (L143). That obligation left with `ConformsAt`'s heap index. -/
theorem DeclsOk_grow {D : Decls} {h h' : Heap} (hg : PlainGrow h h') (hsat : Saturated h)
    (hd : DeclsOk D h)
    (hnew : ∀ τr mname decl, declFor D τr mname = some decl →
      ∀ recv, ValueTy h' recv τr →
        ∃ recv₀, ValueTy h recv₀ τr ∧ (∀ o, recv₀ = .ref o → o < h.objs.size) ∧
          classOf h' recv = classOf h' recv₀) :
    DeclsOk D h' := by
  intro τr mname decl hdecl
  obtain ⟨bid, hres, hconf⟩ := hd τr mname decl hdecl
  refine ⟨bid, fun recv hrv => ?_, hconf⟩
  obtain ⟨recv₀, hrv₀, hb₀, hcls⟩ := hnew τr mname decl hdecl recv hrv
  exact ResolvesTo_classOf hcls (ResolvesTo_grow hg hsat hb₀ (hres recv₀ hrv₀))

/-- **And it survives unconditionally when no declared type is a class type**, which
    is the shape the first producer commit lands in: `baseDecls` declares three names
    on `Integer`, a declaration at a ground type can only be about immediates
    (`valueTy_ref_cls`), and an immediate's type does not depend on the heap
    (`valueTy_immediate`). So the fresh object inhabits nothing the declarations
    name, and the side condition above discharges with `recv₀ := recv`.

    This is not the general case and is not meant to be — it is the measurement of
    how far the *inert* producer gets, and the reason it gets that far is that
    nothing declares a row for a user class yet. The moment one does, `DeclsOk_grow`
    is the theorem and its side condition is a real obligation. -/
theorem DeclsOk_grow_ground {D : Decls} {h h' : Heap} (hg : PlainGrow h h')
    (hsat : Saturated h) (hd : DeclsOk D h)
    (hground : ∀ τr mname decl, declFor D τr mname = some decl → ∀ n, τr ≠ .cls n) :
    DeclsOk D h' := by
  refine DeclsOk_grow hg hsat hd ?_
  intro τr mname decl hdecl recv hrv
  have hnr : ∀ o, recv ≠ .ref o := by
    intro o hEq
    subst hEq
    obtain ⟨n, rfl⟩ := valueTy_ref_cls hrv
    exact hground _ mname decl hdecl n rfl
  exact ⟨recv, valueTy_immediate hnr hrv, fun o hEq => absurd hEq (hnr o), rfl⟩

/-! ## 4. The bridge from `TableOk`

`TableOk` stays exactly as it was, because F0's two theorems and the runtime
certificate (`heapOkB`, `scripts/heapok_probe.lean`) are stated over it. What
changes is that it is no longer what the invariant carries: it is the *concrete
witness* for `baseDecls`, and this section is the derivation.
-/

/-- Every entry of `baseDecls` still resolves in this heap, spelled out at the
    three concrete names. A *heap* condition, so preservation must re-establish
    it.

    **This is no longer what the invariant carries** (F1a): `DeclsOk` is, and this
    is its concrete witness for `baseDecls` via `tableOk_declsOk`. It is kept
    exactly as it was because it is the *certificate-shaped* form — `HeapCert.lean`
    reflects it into a `Bool`, `scripts/heapok_probe.lean` reports it per clause,
    and `check-proofs.sh` fails if it stops holding at the booted heap. Moved here
    from `Proof/Static/Konts.lean` with the rest of the heap conditions, since the
    file that defines the refinement invariant is where its instances belong. -/
def TableOk (h : Heap) : Prop :=
  IntBuiltinResolves h "+" "Integer#+" ∧
  IntBuiltinResolves h "-" "Integer#-" ∧
  IntBuiltinResolves h "*" "Integer#*"

/-- **No `def` hook is installed.** `Interp.lean:2625` fires
    `Module#method_added` on the defining module right after installing a method,
    and the hook body is arbitrary Ruby we cannot type — so the fragment has to
    exclude it rather than reason about it.

    It is excludable because the prelude installs the hook **lazily**: the
    `Object.define_singleton_method(:method_added)` in `T.__toplevel_sig`
    (`prelude/prelude.rb:1187`) runs only when a toplevel `sig` is evaluated. A
    sig-free program therefore never has one, and `lookup` simply misses [V —
    `rfl` on the boot heap].

    A pure *heap* fact, with `defmod = Boot.objectId` carried by
    `FrameConforms` instead — phrasing it at the current frame's `defmod` makes it
    unprovable across `frameK`, which resumes a different frame. -/
def NoHook (h : Heap) : Prop :=
  lookup h (.ref Boot.objectId) "method_added" = none

/-- **`TableOk` survives a user `def`.** Still needed, because `HeapOk` — F0's
    heap half — is stated over `TableOk`, and `PreludeInv.heapOk_defineMethod` is
    its `defineMethod` case. `DeclsOk_defineMethod` is the general version of the
    same claim; this one stays because the certificate does.

    The side condition is what the fragment checks syntactically — a `def` may not
    shadow a tabulated builtin name. It holds for *any* target class `cls`, so
    reopening `Integer` itself is fine as long as the name differs. -/
theorem TableOk_defineMethod {h : Heap} {cls : ObjId} {name : String}
    {md : MethodDef} (ht : TableOk h)
    (h1 : ¬ (name = "+")) (h2 : ¬ (name = "-")) (h3 : ¬ (name = "*")) :
    TableOk (defineMethod h cls name md) :=
  ⟨IntBuiltinResolves_defineMethod ht.1 (fun hh => h1 hh.symm),
   IntBuiltinResolves_defineMethod ht.2.1 (fun hh => h2 hh.symm),
   IntBuiltinResolves_defineMethod ht.2.2 (fun hh => h3 hh.symm)⟩

/-- The `Integer` entries of `baseDecls`, from the corresponding
    `IntBuiltinResolves`. The `hrun`/`hdefer` hypotheses are the ones
    `Proof/BuiltinConformance.lean` already discharges by `rfl` and `simp`. -/
theorem entryOk_int {h : Heap} {mname bid : String} {op : Int → Int → Int}
    (hres : IntBuiltinResolves h mname bid)
    (hns : (mname == "send" || mname == "public_send" || mname == "__send__") = false)
    (hraise : bid ≠ "Object#raise")
    (hrun : ∀ (x y : Int) (m' : Machine),
      Builtins.run bid (.int x) [.int y] m' = .ok (.int (op x y)) m')
    (hdefer : ∀ (h' : Heap) (x y : Int),
      Builtins.deferTwin? h' bid (.int x) [.int y] = none) :
    EntryOk h .int mname { params := [.int], ret := .int } := by
  refine ⟨bid, ?_, hns, hraise, ?_⟩
  · intro recv hrv
    obtain ⟨a, rfl⟩ := valueTy_int hrv
    obtain ⟨owner, md, hlook, hb, hu, hvis, hpre, hbtw⟩ := hres
    refine ⟨owner, md, ?_, hb, hu, hvis, hpre, ?_⟩
    · rw [lookup_int_const h a mname]; exact hlook
    · rw [classOf_int]; exact hbtw
  · -- L146: the conformance half is now quantified over the machine, and the proof
    -- did not move — every hypothesis it used was a `valueTy_int` inversion, which
    -- is heap-independent. That is the evidence the heap index was carrying nothing.
    intro m recv args hrv hargs
    obtain ⟨a, rfl⟩ := valueTy_int hrv
    -- `d.params = [.int]`, so `ValuesTy` pins the argument list to one integer.
    match args, hargs with
    | [b], ⟨hb, _⟩ =>
      obtain ⟨y, rfl⟩ := valueTy_int hb
      exact ⟨fun h' => hdefer h' a y, .int (op a y), rfl, hrun a y m⟩

/-- **The base table declares nothing at a class type.** `baseDecls`'s only key is
    `"Integer"`, and `tyClassNames` subtracts the ground names from the class arm's
    range (L141) precisely so that `.cls "Integer"` — whose inhabitants are objects
    of *some* class merely named `Integer` — cannot read `Integer`'s row.

    Pulled out of `tableOk_declsOk`'s class arm because L146 needs it a second time:
    it is what discharges `DeclsOk_grow_ground`'s side condition for the table the
    model actually carries, which is what makes "the inert producer preserves the
    invariant" a theorem rather than a plan. -/
theorem declFor_baseDecls_cls (n mname : String) :
    declFor baseDecls (.cls n) mname = none := by
  unfold declFor
  simp only [tyClassNames]
  by_cases hg : groundClassNames.contains n = true
  · rw [if_pos hg]
  · rw [if_neg hg]
    have hne : ("Integer" == n) = false := by
      by_cases he : "Integer" = n
      · exact absurd (by subst he; simp [groundClassNames]) hg
      · simpa using he
    simp [declOf?, declsFor, baseDecls, hne]

/-- So the invariant for `baseDecls` survives an allocation with **no** side
    condition. This is the producer's `DeclsOk` obligation, discharged for the table
    as it stands — and the reason it discharges is exactly the reason the producer
    lands inert: nothing declares a row for a user class yet. -/
theorem declsOk_baseDecls_grow {h h' : Heap} (hg : PlainGrow h h') (hsat : Saturated h)
    (hd : DeclsOk baseDecls h) : DeclsOk baseDecls h' :=
  DeclsOk_grow_ground hg hsat hd (fun τr mname decl hdecl n hEq => by
    subst hEq
    exact absurd hdecl (by rw [declFor_baseDecls_cls]; simp))

theorem tableOk_declsOk {h : Heap} (ht : TableOk h) : DeclsOk baseDecls h := by
  intro τr mname d hd
  -- Only `Integer` has declarations, and only three names on it, so the table
  -- lookup either pins `mname` or refutes `hd`.
  cases τr with
  | int =>
    by_cases h1 : mname = "+"
    · subst h1
      have : d = { params := [Ty.int], ret := Ty.int } := by
        simpa [declFor, tyClassNames, declOf?, declsFor, baseDecls] using hd.symm
      subst this
      exact entryOk_int ht.1 (by decide) (by decide) run_int_add
        (fun _ _ _ => by simp [Builtins.deferTwin?, Builtins.reprDefer?,
          Builtins.coerceDefer?, Builtins.toAryDefer?, Builtins.num?])
    · by_cases h2 : mname = "-"
      · subst h2
        have : d = { params := [Ty.int], ret := Ty.int } := by
          simpa [declFor, tyClassNames, declOf?, declsFor, baseDecls] using hd.symm
        subst this
        exact entryOk_int ht.2.1 (by decide) (by decide) run_int_sub
          (fun _ _ _ => by simp [Builtins.deferTwin?, Builtins.reprDefer?,
            Builtins.coerceDefer?, Builtins.toAryDefer?, Builtins.num?])
      · by_cases h3 : mname = "*"
        · subst h3
          have : d = { params := [Ty.int], ret := Ty.int } := by
            simpa [declFor, tyClassNames, declOf?, declsFor, baseDecls] using hd.symm
          subst this
          exact entryOk_int ht.2.2 (by decide) (by decide) run_int_mul
            (fun _ _ _ => by simp [Builtins.deferTwin?, Builtins.reprDefer?,
              Builtins.coerceDefer?, Builtins.toAryDefer?, Builtins.num?])
        · exact absurd hd (by
            simp [declFor, tyClassNames, declOf?, declsFor, baseDecls,
              show ("+" == mname) = false from by simp [Ne.symm h1],
              show ("-" == mname) = false from by simp [Ne.symm h2],
              show ("*" == mname) = false from by simp [Ne.symm h3]])
  | bool =>
    exact absurd hd (by simp [declFor, tyClassNames, declOf?, declsFor, baseDecls])
  | nilT =>
    exact absurd hd (by simp [declFor, tyClassNames, declOf?, declsFor, baseDecls])
  | sym =>
    exact absurd hd (by simp [declFor, tyClassNames, declOf?, declsFor, baseDecls])
  -- The class arm (F1b): refuted by `declFor_baseDecls_cls` below — `baseDecls` has
  -- one key, `"Integer"`, and `tyClassNames` subtracts it from the class arm's
  -- range, so a class type has no declarations in the base table by construction.
  | cls n => exact absurd hd (by rw [declFor_baseDecls_cls]; simp)

end Static
end Proof
end RubyCore
