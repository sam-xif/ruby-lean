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
    using it. -/
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
    which it is false does not belong in the table at all. -/
def ConformsAt (h : Heap) (τr : Ty) (mname bid : String) (d : MethodDecl) : Prop :=
  (mname == "send" || mname == "public_send" || mname == "__send__") = false ∧
  bid ≠ "Object#raise" ∧
  ∀ recv args, ValueTy h recv τr → ValuesTy h args d.params →
    (∀ h' : Heap, Builtins.deferTwin? h' bid recv args = none) ∧
    ∃ w, ValueTy h w d.ret ∧ ∀ m : Machine, Builtins.run bid recv args m = .ok w m

/-- One declared method, satisfied: **some** builtin both resolves for every
    receiver of the class and conforms. Existential in `bid` rather than pinning
    it, which is what makes the condition a lower bound — the invariant never says
    *which* implementation answers, only that a conforming one does. -/
def EntryOk (h : Heap) (τr : Ty) (mname : String) (d : MethodDecl) : Prop :=
  ∃ bid, (∀ recv, ValueTy h recv τr → ResolvesTo h recv mname bid) ∧
    ConformsAt h τr mname bid d

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
  obtain ⟨hdefer, w, hw, hrun⟩ := hconf recv args hrv hargs
  refine ⟨w, hw, ?_⟩
  simp only [startArgs, finishSend]
  rw [invoke.eq_def]
  -- The receiver has to be case-split, and the reason is worth stating: `invoke`
  -- has receiver-shape special cases *before* the resolved-builtin path (class
  -- objects reach `invokeMaybeNew`, and `Math` has its own arm), so an abstract
  -- receiver leaves them standing. Every one of them is a `.ref`, and no `.ref`
  -- has a `Ty` — `valueTy?` is `none` there — so the fragment's own type judgement
  -- is what closes them. F1b's nominal types will have to do this differently, and
  -- that is the first place this rung's shape actually bites.
  rcases valueTy_immediate hrv with ⟨a, rfl⟩ | ⟨b, rfl⟩ | rfl | ⟨sy, rfl⟩ <;>
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
  cases τ <;> (unfold declFor at h; simp only [tyClassNames] at h) <;>
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

theorem ConformsAt_defineMethod {h : Heap} {τr : Ty} {mname bid : String}
    {d : MethodDecl} {cls : ObjId} {name : String} {md : MethodDef}
    (hc : ConformsAt h τr mname bid d) :
    ConformsAt (defineMethod h cls name md) τr mname bid d := by
  have hag := typeAgree_defineMethod h cls name md
  refine ⟨hc.1, hc.2.1, fun recv args hrv hargs => ?_⟩
  obtain ⟨hdefer, w, hw, hrun⟩ :=
    hc.2.2 recv args (ValueTy.congr hag.symm hrv) (ValuesTy.congr hag.symm hargs)
  exact ⟨hdefer, w, ValueTy.congr hag hw, hrun⟩

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
  refine ⟨bid, fun recv hrv => ?_, ConformsAt_defineMethod hconf⟩
  exact ResolvesTo_defineMethod
    (hres recv (ValueTy.congr (typeAgree_defineMethod h cls name md).symm hrv)) hne

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
  · intro recv args hrv hargs
    obtain ⟨a, rfl⟩ := valueTy_int hrv
    -- `d.params = [.int]`, so `ValuesTy` pins the argument list to one integer.
    match args, hargs with
    | [b], ⟨hb, _⟩ =>
      obtain ⟨y, rfl⟩ := valueTy_int hb
      exact ⟨fun h' => hdefer h' a y, .int (op a y), rfl, fun m => hrun a y m⟩

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

end Static
end Proof
end RubyCore
