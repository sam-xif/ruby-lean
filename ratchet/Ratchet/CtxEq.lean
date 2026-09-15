import Ratchet.Judge

/-! Proof-producing context compatibility for branch joins. This reuses the conservative
structural syntax comparator: unsupported syntax may compare unequal, never falsely equal.
No unchecked `BEq` result is used to cast a derivation between contexts. -/

set_option autoImplicit false
set_option maxRecDepth 4000
namespace Ratchet

theorem paramEq_sound {a b : Param} (h : paramEq a b = true) : a = b := by
  cases a <;> cases b <;> simp_all [paramEq]

theorem paramEqAll_sound {a b : List Param} (h : paramEqAll a b = true) : a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [paramEqAll]
  | cons a as ih =>
    cases b with
    | nil => cases h
    | cons b bs =>
      simp only [paramEqAll, Bool.and_eq_true] at h
      rw [paramEq_sound h.1, ih h.2]

theorem exprEq_sound (a b : Expr) : exprEq a b = true → a = b := by
  induction a, b using exprEq.induct
    (motive_2 := fun a b => exprEqPairs a b = true → a = b)
    (motive_3 := fun a b => exprEqAll a b = true → a = b) <;>
    simp_all [exprEq, exprEqAll, exprEqPairs, Bool.and_eq_true]
  all_goals intros; simp_all
  all_goals apply paramEqAll_sound; assumption

def listEqB {α : Type} (eq : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | a :: as, b :: bs => eq a b && listEqB eq as bs
  | _, _ => false

theorem listEqB_sound {α : Type} {eq : α → α → Bool}
    (hs : ∀ a b, eq a b = true → a = b) {as bs : List α}
    (h : listEqB eq as bs = true) : as = bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all [listEqB]
  | cons a as ih =>
    cases bs with
    | nil => cases h
    | cons b bs =>
      simp only [listEqB, Bool.and_eq_true] at h
      rw [hs a b h.1, ih h.2]

def defnEqB (a b : Defn) : Bool :=
  decide (a.name = b.name) && paramEqAll a.params b.params && exprEq a.body b.body

theorem defnEqB_sound (a b : Defn) (h : defnEqB a b = true) : a = b := by
  cases a; cases b
  simp only [defnEqB, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [Defn.mk.injEq]
  exact ⟨h.1.1, paramEqAll_sound h.1.2, exprEq_sound _ _ h.2⟩

/-- Membership evidence, never an unchecked cast from the syntax comparator. -/
def defnMem? (d : Defn) : (ds : List Defn) → Option (PLift (d ∈ ds))
  | [] => none
  | x :: xs =>
    if h : defnEqB d x = true then some ⟨List.mem_cons.mpr (Or.inl (defnEqB_sound _ _ h))⟩
    else (defnMem? d xs).map (fun h => ⟨List.mem_cons.mpr (Or.inr h.down)⟩)

def clsEqB (a b : Cls) : Bool :=
  decide (a.name = b.name ∧ a.super? = b.super? ∧ a.isModule = b.isModule ∧
    a.includes = b.includes ∧ a.prepends = b.prepends ∧ a.extended = b.extended) &&
  listEqB defnEqB a.methods b.methods && listEqB defnEqB a.smethods b.smethods

theorem clsEqB_sound (a b : Cls) (h : clsEqB a b = true) : a = b := by
  cases a; cases b
  simp only [clsEqB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hn, hs, hm, hi, hp, he⟩, hms⟩, hsm⟩ := h
  simp only [Cls.mk.injEq]
  exact ⟨hn, hs, listEqB_sound defnEqB_sound hms, listEqB_sound defnEqB_sound hsm, hm, hi, hp, he⟩

deriving instance DecidableEq for Frame, Asm

def closEqB (a b : Clos) : Bool := paramEqAll a.params b.params && exprEq a.body b.body

theorem closEqB_sound (a b : Clos) (h : closEqB a b = true) : a = b := by
  cases a; cases b
  simp only [closEqB, Bool.and_eq_true] at h
  simp only [Clos.mk.injEq]
  exact ⟨paramEqAll_sound h.1, exprEq_sound _ _ h.2⟩

def posEqB (a b : Pos) : Bool := listEqB clsEqB a.classes b.classes &&
  listEqB defnEqB a.defs b.defs &&
    decide (a.consts = b.consts ∧ a.privConsts = b.privConsts ∧ a.mainWorld = b.mainWorld ∧
      a.plainAlloc = b.plainAlloc)

theorem posEqB_sound (a b : Pos) (h : posEqB a b = true) : a = b := by
  cases a; cases b
  simp only [posEqB, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [Pos.mk.injEq]
  exact ⟨listEqB_sound clsEqB_sound h.1.1, listEqB_sound defnEqB_sound h.1.2, h.2⟩

def negEqB (a b : Ratchet.Neg) : Bool := listEqB clsEqB a.wholeCls b.wholeCls &&
  decide (a.ports = b.ports ∧ a.noMethod = b.noMethod ∧ a.declared = b.declared ∧
    a.unpinned = b.unpinned ∧ a.boundConsts = b.boundConsts ∧ a.freeConsts = b.freeConsts)

theorem negEqB_sound (a b : Ratchet.Neg) (h : negEqB a b = true) : a = b := by
  cases a; cases b
  simp only [negEqB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hc, hp, hn, hd, hu, hb, hf⟩ := h
  simp only [Ratchet.Neg.mk.injEq]
  exact ⟨hp, hn, hd, hu, listEqB_sound clsEqB_sound hc, hb, hf⟩

def scopeEqB (a b : Scope) : Bool := listEqB closEqB a.closures b.closures &&
  decide (a.frame = b.frame ∧ a.blockTy = b.blockTy ∧ a.selfTy = b.selfTy ∧ a.asms = b.asms ∧
    a.runtimeMain = b.runtimeMain ∧ a.runtimeClass = b.runtimeClass ∧ a.closedIvars = b.closedIvars)

theorem scopeEqB_sound (a b : Scope) (h : scopeEqB a b = true) : a = b := by
  cases a; cases b
  simp only [scopeEqB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hc, hf, hb, hs, ha, hr, hcl, hi⟩ := h
  simp only [Scope.mk.injEq]
  exact ⟨hf, listEqB_sound closEqB_sound hc, hb, hs, ha, hr, hcl, hi⟩

def ctxEqB (a b : Ctx) : Bool := posEqB a.pos b.pos && negEqB a.neg b.neg && scopeEqB a.scope b.scope

theorem ctxEqB_sound {a b : Ctx} (h : ctxEqB a b = true) : a = b := by
  cases a; cases b
  simp only [ctxEqB, Bool.and_eq_true] at h
  simp only [Ctx.mk.injEq]
  exact ⟨posEqB_sound _ _ h.1.1, negEqB_sound _ _ h.1.2, scopeEqB_sound _ _ h.2⟩

def ctxEq? (a b : Ctx) : Option (PLift (a = b)) :=
  if h : ctxEqB a b = true then some ⟨ctxEqB_sound h⟩ else none

#guard (ctxEq? ctx0 ctx0).isSome
#guard (ctxEq? ctx0 { ctx0 with scope := { ctx0.scope with runtimeMain := false } }).isNone
#guard (ctxEq? ctx0 (ctx0.withFrame (some ⟨"Object", "Object", "add"⟩))).isNone
#guard (ctxEq? ctx0 { ctx0 with neg := { ctx0.neg with declared := ["+"] } }).isNone
#print axioms ctxEqB_sound
end Ratchet
