import RubyCore.Cert.Ledger
import RubyCore.Proof.Cert.Sound
import RubyCore.Proof.Static.Discharge

/-!
# C2 — the ledger is sound, and `discharge_sound`'s open premise is closed

`docs/semantics/certificate-language.md` §6 **C2**'s gate: *"`discharge_sound`'s
premise discharged mechanically […]; no search remains anywhere in `validate`."*

L262 stated that premise and declined to discharge it, in as many words:

> **The second premise is real and is not discharged here.** `SatProvs D θ st` says
> `sigOf D (θ α) n` really is the signature the `def` supplied — a fact about the
> **table**, not about `θ`. […] `Types/Program.lean`'s `def` arm is what has to record
> it faithfully.

`satProvs_ledgerStore` below is the discharge, and the shape of it is §1's thesis in
one line: **the certificate records what `discharge` had to search for.** The
requirement/provision pairing is a *choice*; `Types/Discharge.lean` finds it by
walking the store, and the ledger states it, so the validator's obligation per
cancellation is one `sigOf` lookup.

## Where this leaves `discharge_sound`

Composed (`ledger_satStore`), the chain is exactly the division of labour L262
describes and could not complete:

```
  satStoreB D θ (discharge st)      -- the untrusted solver's answer, on the SMALL store
  ledgerOk c p                      -- the validator's pairwise check, no search
  ───────────────────────────────
  SatStore D θ st                   -- every requirement `inferOpen` recorded
```

and `SatStore` is the premise `inferOpen_factors`/`inferBodyWith_sound` consume. So a
solver may be handed the cancelled store — the small thing — and its answer still
discharges the whole one.

**What this does *not* do**, stated because the temptation is to read it as more:
it does not make a whole-program open accept into a `¬ typeStuck` conclusion. That
needs `inferOpen`'s `def` arm to satisfy `infer`'s (`params.isEmpty`, 67 of the
slice's 112 bodies — L262), and no ledger changes it. What the chain delivers is the
*body-level* factoring: `SatStore` per body, hence a nominal `infer` accept per body,
which is `userConforms_of_inferBody`'s input.
-/

namespace RubyCore
namespace Proof
namespace Cert

open Interp
open RubyCore.Types
open RubyCore.Cert
open RubyCore.Proof.Static

set_option maxRecDepth 100000

/-! ## 1. `Row.insert`, inverted

The one fact the fold needs, and it is two cases of `insert`: either the name was
already there at the same signature (so the row did not change) or it was prepended
(so `find?` answers it first). Nothing else can happen — `insert` refuses a *different*
signature, which is `Row.insert`'s ★★. -/

theorem row_insert_get?_inv {R R' : Row} {n m : String} {σ' σ : ASig}
    (h : R.insert n σ' = some R') (hg : R'.get? m = some σ) :
    (m = n ∧ σ = σ') ∨ R.get? m = some σ := by
  unfold Row.insert at h
  cases hn : R.get? n with
  | none =>
    rw [hn] at h
    simp only [Option.some.injEq] at h
    subst h
    by_cases hmn : m = n
    · subst hmn
      refine Or.inl ⟨rfl, ?_⟩
      rw [show Row.get? { entries := (m, σ') :: R.entries, tail := R.tail } m = some σ' from
            by simp [Row.get?]] at hg
      exact (Option.some.inj hg).symm
    · refine Or.inr ?_
      rw [show Row.get? { entries := (n, σ') :: R.entries, tail := R.tail } m = R.get? m from
            by simp [Row.get?, show (n == m) = false from by simpa using fun hh => hmn hh.symm]] at hg
      exact hg
  | some τ =>
    rw [hn] at h
    dsimp only at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact Or.inr hg
    · exact absurd h (by simp)

/-! ## 2. The fold, inverted

Every provision in the ledger's store came from a ledger step. That is the whole
content of "the certificate records the pairing": the store is not computed from the
program, it is *read off the certificate*, so its provisions are enumerable. -/

theorem stepInto_provOf {st st' : Store} {s : DischargeStep}
    (h : stepInto st s = some st') {α : TyVar} {n : String} {σ : ASig}
    (hg : (st'.provOf α).get? n = some σ) :
    (α = s.var ∧ n = s.name ∧ σ = s.provided) ∨ (st.provOf α).get? n = some σ := by
  unfold stepInto at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨R, -, h⟩ := h
  -- `setRow` touches `rows` only, so the provisions are `st`'s.
  have hprov : ((st.setRow s.var R).provOf s.var) = st.provOf s.var := rfl
  unfold Store.addProv at h
  cases hP : ((st.setRow s.var R).provOf s.var).insert s.name s.provided with
  | none => rw [hP] at h; exact absurd h (by simp)
  | some R' =>
    rw [hP] at h
    simp only [Option.some.injEq] at h
    subst h
    by_cases hα : α = s.var
    · have hone : ({ st.setRow s.var R with
              provs := (s.var, R') :: (st.setRow s.var R).provs } : Store).provOf α = R' := by
        unfold Store.provOf
        rw [hα]
        exact rowIn_cons_self _ _ _
      rw [hone] at hg
      rw [hprov] at hP
      rcases row_insert_get?_inv hP hg with ⟨rfl, rfl⟩ | hold
      · exact Or.inl ⟨hα, rfl, rfl⟩
      · exact Or.inr (by rw [hα]; exact hold)
    · refine Or.inr ?_
      have hne : ({ st.setRow s.var R with
              provs := (s.var, R') :: (st.setRow s.var R).provs } : Store).provOf α
            = st.provOf α := by
        unfold Store.provOf
        rw [rowIn_cons_ne _ _ (fun hh => hα hh.symm)]
        rfl
      rw [hne] at hg
      exact hg

theorem ledgerFold_provOf : ∀ (steps : List DischargeStep) (st st' : Store),
    ledgerFold st steps = some st' →
    ∀ α n σ, (st'.provOf α).get? n = some σ →
      (∃ s ∈ steps, α = s.var ∧ n = s.name ∧ σ = s.provided)
        ∨ (st.provOf α).get? n = some σ
  | [], st, st', h, α, n, σ, hg => by
      simp only [ledgerFold, Option.some.injEq] at h
      subst h
      exact Or.inr hg
  | s :: rest, st, st', h, α, n, σ, hg => by
      simp only [ledgerFold] at h
      cases hs : stepInto st s with
      | none => rw [hs] at h; exact absurd h (by simp)
      | some st1 =>
        rw [hs] at h
        rcases ledgerFold_provOf rest st1 st' h α n σ hg with ⟨s', hm, hk⟩ | hg1
        · exact Or.inl ⟨s', List.mem_cons_of_mem _ hm, hk⟩
        · rcases stepInto_provOf hs hg1 with hk | hold
          · exact Or.inl ⟨s, List.mem_cons_self, hk⟩
          · exact Or.inr hold

/-! ## 3. The discharge -/

/-- **`SatProvs`, discharged by the ledger.** C2's gate.

    Read the proof: every provision the store holds is a ledger step
    (`ledgerFold_provOf`), and every ledger step's `sigOf` lookup was checked
    (`ledgerStepOk`). There is no induction over the program, no traversal of a
    typing derivation, and no search — which is the whole claim §1 makes about
    relocating the trust boundary. -/
theorem satProvs_ledgerStore {c : RubyCore.Cert.Cert} {p : Expr} {st : Store}
    (hs : c.ledgerStore? = some st) (hl : ledgerOk c p = true) :
    SatProvs (c.table p) c.thetaFn st := by
  unfold ledgerOk at hl
  simp only [Bool.and_eq_true] at hl
  intro α n σ hg
  unfold RubyCore.Cert.Cert.ledgerStore? at hs
  rcases ledgerFold_provOf c.ledger {} st hs α n σ hg with ⟨s, hm, rfl, rfl, rfl⟩ | hempty
  · have hstep := (List.all_eq_true.mp hl.2) s hm
    simp only [Bool.and_eq_true] at hstep
    have := hstep.1
    unfold ledgerStepOk at this
    simpa using this
  · exact absurd hempty (by simp [Store.provOf, Store.rowIn, Row.get?, Row.empty])

/-- **The composed chain** — L262's division of labour, completed.

    `hsol` is the untrusted solver's answer *on the cancelled store*, which is the
    small thing; the conclusion is about the whole one. `satStoreB_sound` is how a
    concrete solver answer becomes `hsol` (§4's worked example does it by `decide`). -/
theorem ledger_satStore {c : RubyCore.Cert.Cert} {p : Expr} {st : Store}
    (hs : c.ledgerStore? = some st) (hl : ledgerOk c p = true)
    (hsol : SatStore (c.table p) c.thetaFn (discharge st)) :
    SatStore (c.table p) c.thetaFn st :=
  discharge_sound hsol (satProvs_ledgerStore hs hl)

/-- …and `validateFull` gives both halves at once: the program-level conclusion and
    the store-level one. Stated so a consumer of the JSON's `ledger_ok` field has one
    theorem to point at. -/
theorem validateFull_sound {c : RubyCore.Cert.Cert} {p : Expr} {st : Store}
    (h : validateFull c p = true)
    (ha : denote (c.table p) c.thetaFn c.rowAssn (Machine.init p).heap)
    (hs : c.ledgerStore? = some st)
    (hsol : SatStore (c.table p) c.thetaFn (discharge st)) :
    (∀ r, ReachableResult (Machine.init p) r → ¬ typeStuck r) ∧
      SatStore (c.table p) c.thetaFn st := by
  unfold validateFull at h
  simp only [Bool.and_eq_true] at h
  exact ⟨validate_sound_carries h.1 ha, ledger_satStore hs h.2 hsol⟩

/-! ## 4. The worked example — L262's headline, with the pairing *stated*

```ruby
class String
  def value; 1; end
  def get;   value; end
end
```

`--assn-program` reports this as *accept, under `α₃ = Integer`* (L265's headline), and
the way it gets there is `discharge` **finding** that `get`'s requirement on `value`
is answered by the `def value` beside it. Here the certificate states that pairing and
the validator checks it, and the conclusion is `SatStore` for the store `inferOpen`
would have built — the premise `inferBodyWith_sound` consumes.

Two `decide`s and one `rfl`, which is the point: at this scale the *whole* chain is a
kernel computation, with no `native_decide` anywhere (§7 norm 5). -/

/-- The table the example runs against: `String#value : () → Integer`, which is what
    `def value; 1; end` supplies and what L264's promotion would have added. -/
def egLedgerD : Decls := addRow baseDecls "String" "value" { params := [], ret := .int }

/-- `θ`: `self` is a `String`, and what `value` returns is an `Integer` — the
    instantiation `--assn-program` prints as `α₃ = Integer`. -/
def egLedgerTheta : List (TyVar × Ty) := [(0, .cls "String"), (1, .int)]

def egLedgerCert : RubyCore.Cert.Cert :=
  { theta := egLedgerTheta,
    deltaRows := [{ cls := "String", name := "value",
                    sig := { params := [], ret := .int }, why := .assumed "def value" }],
    assumes := .decl (.cls "String") "value" { params := [], ret := .int },
    ledger := [RubyCore.Cert.egStep] }

/-- The certificate's table is the one the example needs — which is the check that the
    `deltaRows` section and the ledger are talking about the same thing. -/
theorem egLedger_table : egLedgerCert.table (.nil) = egLedgerD := by
  simp [RubyCore.Cert.Cert.table, egLedgerCert, egLedgerD, declsOf]

/-- The ledger checks out: one `sigOf` lookup and the re-derived equality `α₁ = Integer`.
    `decide`, in the kernel. -/
theorem egLedger_ok : ledgerOk egLedgerCert (.nil) = true := by
  simp only [ledgerOk, egLedger_table]
  decide

/-- The store the ledger determines. -/
theorem egLedger_store :
    egLedgerCert.ledgerStore?
      = some { rows := [(0, { entries := [("value", { params := [], ret := .var 1 })] })],
               provs := [(0, { entries := [("value", { params := [], ret := .nom .int })] })] } := by
  decide

/-- The solver's answer, on the **cancelled** store — whose rows are empty, so all
    that is left to check is the equality the cancellation owed. -/
theorem egLedger_solved :
    SatStore egLedgerD egLedgerCert.thetaFn
      (discharge { rows := [(0, { entries := [("value", { params := [], ret := .var 1 })] })],
                   provs := [(0, { entries := [("value", { params := [], ret := .nom .int })] })] }) :=
  satStoreB_sound (by decide)

/-- **And therefore `SatStore` for the whole store** — every requirement, including the
    one the cancellation removed. This is `discharge_sound` with both premises met, for
    the first time. -/
theorem egLedger_satStore :
    SatStore egLedgerD egLedgerCert.thetaFn
      { rows := [(0, { entries := [("value", { params := [], ret := .var 1 })] })],
        provs := [(0, { entries := [("value", { params := [], ret := .nom .int })] })] } := by
  have := ledger_satStore (p := .nil) egLedger_store egLedger_ok
    (by rw [egLedger_table]; exact egLedger_solved)
  rw [egLedger_table] at this
  exact this

/-! ## 5. Axiom hygiene -/

/-- info: 'RubyCore.Proof.Cert.satProvs_ledgerStore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms satProvs_ledgerStore

/-- info: 'RubyCore.Proof.Cert.ledger_satStore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ledger_satStore

/-- info: 'RubyCore.Proof.Cert.egLedger_satStore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms egLedger_satStore

end Cert
end Proof
end RubyCore
