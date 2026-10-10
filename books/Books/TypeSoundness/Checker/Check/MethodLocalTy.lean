import Books.TypeSoundness.Checker.Judgment.DMethodFlow

/-! Definition-side local types retain an opaque supplied callback code. Checking
uses this symbolic form; instantiation later proves the same judgment for every code. -/
set_option autoImplicit false
namespace Checker

inductive MethodLocalTy where
  | fixed (ty : Ty)
  | callback
deriving BEq, DecidableEq, Repr, Inhabited

def MethodLocalTy.instantiate (code : ClosureCode) : MethodLocalTy → Ty
  | .fixed τ => τ
  | .callback => .clos code .ivar0 .never

def MethodLocalTy.validB : MethodLocalTy → Bool
  | .fixed τ => FirstOrder τ && !isAliasTy τ
  | .callback => true

theorem MethodLocalTy.noAlias {τ : MethodLocalTy} (h : τ.validB = true) (code : ClosureCode) :
    isAliasTy (τ.instantiate code) = false := by
  cases τ with
  | callback => rfl
  | fixed ty =>
    simp only [MethodLocalTy.validB, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact h.2

private theorem firstOrder_ne_callback {τ : Ty} (h : FirstOrder τ = true) (code : ClosureCode) :
    τ ≠ .clos code .ivar0 .never := by
  intro he
  subst τ
  cases h

/-- Comparing a first-order component with a code-only closure cannot inspect its
code: the constructors differ. This justifies uniform capture invalidation. -/
theorem capStale_callback_code {τ : Ty} (h : FirstOrder τ = true) (x : String) (a b : ClosureCode) :
    capStale x (.clos a .ivar0 .never) τ = capStale x (.clos b .ivar0 .never) τ := by
  induction τ <;> simp_all [FirstOrder, capStale, firstOrder_ne_callback]

def MethodLocalTy.staleB (old : MethodLocalTy) (x : String) (value : MethodLocalTy) : Bool :=
  capStale x (value.instantiate default) (old.instantiate default)

theorem MethodLocalTy.stale_instantiate {old : MethodLocalTy} (ho : old.validB = true)
    (x : String) (value : MethodLocalTy) (code : ClosureCode) :
    capStale x (value.instantiate code) (old.instantiate code) = old.staleB x value := by
  cases old with
  | callback => rfl
  | fixed τ =>
    cases value with
    | fixed _ => rfl
    | callback =>
      have hf : FirstOrder τ = true := (Bool.and_eq_true_iff.mp ho).1
      exact capStale_callback_code hf x code default

abbrev MethodLocalEnv := List (String × MethodLocalTy)

def MethodLocalEnv.instantiate (Γ : MethodLocalEnv) (code : ClosureCode) : Env :=
  Γ.map (fun p => (p.1, p.2.instantiate code))

def MethodLocalEnv.validB (Γ : MethodLocalEnv) : Bool := Γ.all (fun p => p.2.validB)

def MethodLocalEnv.fixedB (Γ : MethodLocalEnv) : Bool :=
  Γ.all (fun p => match p.2 with | .fixed _ => true | .callback => false)

theorem MethodLocalEnv.fixed_instantiate {Γ : MethodLocalEnv} (h : Γ.fixedB = true)
    (code : ClosureCode) : Γ.instantiate code = Γ.instantiate default := by
  induction Γ with
  | nil => rfl
  | cons p Γ ih =>
    simp only [fixedB, List.all_cons, Bool.and_eq_true] at h
    cases ht : p.2 with
    | callback => simp [ht] at h
    | fixed τ =>
      change (p.1, p.2.instantiate code) :: MethodLocalEnv.instantiate Γ code =
        (p.1, p.2.instantiate default) :: MethodLocalEnv.instantiate Γ default
      rw [ih h.2]
      simp only [ht, MethodLocalTy.instantiate]

def MethodLocalEnv.ofEnv (Γ : Env) : MethodLocalEnv := Γ.map (fun p => (p.1, .fixed p.2))

theorem MethodLocalEnv.instantiate_ofEnv (Γ : Env) (code : ClosureCode) :
    (ofEnv Γ).instantiate code = Γ := by
  simp [ofEnv, instantiate, Function.comp_def, MethodLocalTy.instantiate]

def MethodLocalEnv.get? (Γ : MethodLocalEnv) (x : String) : Option MethodLocalTy :=
  (Γ.find? (·.1 == x)).map (·.2)

def MethodLocalEnv.put : MethodLocalEnv → String → MethodLocalTy → MethodLocalEnv
  | [], x, τ => [(x, τ)]
  | (y, σ) :: Γ, x, τ => if y == x then (x, τ) :: Γ else (y, σ) :: MethodLocalEnv.put Γ x τ

def MethodLocalEnv.after (Γ : MethodLocalEnv) (x : String) (τ : MethodLocalTy) : MethodLocalEnv :=
  MethodLocalEnv.put (Γ.map (fun p => (p.1, if p.2.staleB x τ then .fixed .any else p.2))) x τ

theorem MethodLocalEnv.get_instantiate (Γ : MethodLocalEnv) (code : ClosureCode) (x : String) :
    envGet? (Γ.instantiate code) x = (Γ.get? x).map (MethodLocalTy.instantiate code) := by
  induction Γ with
  | nil => rfl
  | cons p Γ ih =>
    rcases p with ⟨y, σ⟩
    by_cases he : y == x <;> simp [envGet?, instantiate, get?, he] at *
    exact ih

theorem MethodLocalEnv.get_valid {Γ : MethodLocalEnv} (h : Γ.validB = true)
    {x : String} {τ : MethodLocalTy} (hg : Γ.get? x = some τ) : τ.validB = true := by
  induction Γ with
  | nil => cases hg
  | cons p Γ ih =>
    simp only [validB, List.all_cons, Bool.and_eq_true] at h
    by_cases he : p.1 == x
    · have ht : p.2 = τ := by simpa [get?, he] using hg
      exact ht ▸ h.1
    · apply ih h.2
      simpa [get?, he] using hg

theorem MethodLocalEnv.set_instantiate (Γ : MethodLocalEnv) (x : String) (τ : MethodLocalTy)
    (code : ClosureCode) :
    (Γ.put x τ).instantiate code = envSet (Γ.instantiate code) x (τ.instantiate code) := by
  induction Γ with
  | nil => rfl
  | cons p Γ ih =>
    rcases p with ⟨y, σ⟩
    by_cases he : y == x <;> simp [put, instantiate, envSet, he]
    exact ih

theorem MethodLocalEnv.after_instantiate {Γ : MethodLocalEnv} (h : Γ.validB = true)
    (x : String) (τ : MethodLocalTy) (code : ClosureCode) :
    (Γ.after x τ).instantiate code = envAfter (Γ.instantiate code) x (τ.instantiate code) := by
  rw [after, set_instantiate]
  unfold envAfter
  congr 1
  induction Γ with
  | nil => rfl
  | cons p Γ ih =>
    rcases p with ⟨y, σ⟩
    simp only [validB, List.all_cons, Bool.and_eq_true] at h
    have hn := σ.noAlias h.1 code
    have hk : killAliasTy x (σ.instantiate code) = σ.instantiate code := by
      cases he : σ.instantiate code <;> simp_all [killAliasTy, isAliasTy]
    simp only [List.map_cons, instantiate, killAliasesTo, hk, killClosOver,
      σ.stale_instantiate h.1 x τ code]
    have ih' := ih h.2
    simp only [instantiate] at ih'
    rw [ih']
    split <;> rfl

theorem MethodLocalEnv.activation {Γ : MethodLocalEnv} (h : Γ.validB = true) (code : ClosureCode) :
    activationReturnB (Γ.instantiate code) = true := by
  apply List.all_eq_true.mpr
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  have hv := List.all_eq_true.mp h q hq
  have ha := q.2.noAlias hv code
  have he : stripAlias (q.2.instantiate code) = q.2.instantiate code := by
    cases ht : q.2.instantiate code <;> simp_all [stripAlias, isAliasTy]
  rw [he]
  cases ht : q.2 with
  | callback => rfl
  | fixed τ =>
    simp only [ht, MethodLocalTy.validB, Bool.and_eq_true] at hv
    simp only [MethodLocalTy.instantiate, activationStableB, hv.1, Bool.true_or]

theorem MethodLocalTy.spine_instantiate (τ : MethodLocalTy) (code : ClosureCode) {I : Ty}
    (h : FirstOrder I = true) (x : String) :
    killClosOverSpine I x (τ.instantiate code) = killClosOverSpine I x (τ.instantiate default) := by
  cases τ with
  | fixed _ => rfl
  | callback =>
    induction I <;> try rfl
    rename_i name σ rest ih ih'
    simp only [FirstOrder, Bool.and_eq_true] at h
    simp only [killClosOverSpine, MethodLocalTy.instantiate,
      capStale_callback_code h.1 x code default]
    congr 1
    exact ih' h.2

theorem callback_context_noStale {κ : Ctx} (hs : κ.selfTy = none) (hc : κ.consts = [])
    (fr : Frame) (x : String) (τ : Ty) (code : ClosureCode) :
    capStaleCtx x τ (callbackMethodCtx κ fr code) = false := by
  change (capStale x τ (κ.selfTy.getD .never) || false || κ.consts.any (fun p => capStale x τ p.2)) = false
  rw [hs, hc]
  rfl

end Checker
