import Denote.Typed.Context

/-! Ordinary required-positional method entry, against `enterUserMethod` itself.
This is the call boundary needed by annotated body checking, not a definition admission.
Optional/keyword/block parameters retain the interpreter's own behavior outside this lemma.
-/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem toRubyParams_required (ps : List SigParam) :
    toRubyParams (ps.map (fun p => Ratchet.Param.req p.1)) =
      (ps.map (·.1)).map RubyCore.Param.req := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simpa only [List.map_cons, toRubyParams, toRubyParam] using congrArg (RubyCore.Param.req p.1 :: ·) ih

theorem classifyFull_required (names : List String) :
    Interp.classifyFull (names.map RubyCore.Param.req) =
      some ⟨names, [], none, [], [], none, none, []⟩ := by
  have hnames : names.zipIdx.map (fun p => RubyCore.Param.req p.1) =
      names.map RubyCore.Param.req := by
    change List.map (RubyCore.Param.req ∘ Prod.fst) _ = _
    rw [← List.map_map, List.zipIdx_map_fst]
  have hd : names.dropWhile (fun _ => true) = [] := by
    clear hnames
    induction names <;> simp_all [List.dropWhile]
  have ht : names.takeWhile (fun _ => true) = names := by
    clear hnames hd
    induction names <;> simp_all [List.takeWhile]
  unfold Interp.classifyFull
  simp only [List.flatMap_map, ← List.map_eq_flatMap, List.zipIdx_map,
    List.map_map, List.filterMap_map, Function.comp_def, Prod.map]
  simp only [hnames]
  cases hr : names.reverse <;>
    simp [← List.map_reverse, hr, List.takeWhile_map, List.dropWhile_map,
      Function.comp_def, hd, ht, List.filterMap_map]

/-- Ordinary `def` binds just its own formals: no captured caller frame. -/
def requiredFrame (recv : Value) (name : String) (md : MethodDef)
    (names : List String) (args : List Value) : RubyCore.Frame :=
  { self := recv, locals := names.zip args, defmod := md.owner, kind := .method,
    meth := md.superName.getD name, runParams := md.params, cref := md.cref }

def pushMethodFrame (m : Machine) (f : RubyCore.Frame) : Machine :=
  { m with frames := m.frames.push f, stack := m.frames.size :: m.stack }

theorem enterUserMethod_required (m : Machine) (recv : Value) (name : String)
    (md : MethodDef) (names : List String) (args : List Value)
    (hp : md.params = names.map RubyCore.Param.req)
    (hc : md.capturedFrame = none) (hd : md.declared = [])
    (ha : args.length = names.length) :
    Interp.enterUserMethod m recv name md args none =
      .next (Interp.withKont (pushMethodFrame m (requiredFrame recv name md names args))
        (.eval md.body) (.frameK m.frames.size)) := by
  unfold Interp.enterUserMethod
  rw [hp, classifyFull_required]
  have hf : (names.zip args).filter (fun _ => true) = names.zip args :=
    List.filter_eq_self.mpr (fun _ _ => rfl)
  simp [Interp.appendKwHash, hc, hd, ← ha, requiredFrame, pushMethodFrame,
    Interp.withKont, Interp.withCtl, hp, hf]

theorem requiredFrame_getLocal (m : Machine) (recv : Value) (name : String)
    (md : MethodDef) (names : List String) (args : List Value) (x : String) :
    (pushMethodFrame m (requiredFrame recv name md names args)).getLocal x =
      (((names.zip args).find? (·.1 == x)).map (·.2)).getD .nil := by
  simp only [Machine.getLocal, Machine.getLocal.go, pushMethodFrame, requiredFrame]
  simp [Array.getD_eq_getD_getElem?]
  cases (names.zip args).find? (·.1 == x) <;> rfl

/-- Parameter lookup uses the same first matching name as the real binding list. -/
private theorem required_lookup {m : Machine} {ps : List SigParam} {args : List Value}
    (hargs : DenAll (ps.map (·.2)) m args) {x : String} {τ : Ty}
    (hget : envGet? ps x = some τ) :
    ∃ v, (((ps.map (·.1)).zip args).find? (·.1 == x)).map (·.2) = some v ∧ denM τ m v := by
  induction ps generalizing args with
  | nil => simp [envGet?] at hget
  | cons p ps ih =>
    rcases p with ⟨n, σ⟩
    cases args with
    | nil => cases hargs
    | cons v vs =>
      have ha : denM σ m v ∧ DenAll (ps.map (·.2)) m vs := hargs
      by_cases hn : n == x
      · simp [envGet?, hn] at hget
        subst τ
        exact ⟨v, by simp [hn], ha.1⟩
      · have ht : envGet? ps x = some τ := by simpa [envGet?, hn] using hget
        simpa [hn] using ih ha.2 ht

private theorem required_lookup_none {ps : List SigParam} {args : List Value}
    (hlen : args.length = ps.length) {x : String} (hget : envGet? ps x = none) :
    (((ps.map (·.1)).zip args).find? (·.1 == x)).map (·.2) = none := by
  induction ps generalizing args with
  | nil => cases args <;> simp_all
  | cons p ps ih =>
    rcases p with ⟨n, σ⟩
    cases args with
    | nil => simp at hlen
    | cons v vs =>
      by_cases hn : n == x
      · simp [envGet?, hn] at hget
      · have ht : envGet? ps x = none := by simpa [envGet?, hn] using hget
        simpa [hn] using ih (by simpa using hlen) ht

theorem requiredFrame_envOk (m : Machine) (recv : Value) (name : String)
    (md : MethodDef) (ps : List SigParam) (args : List Value)
    (hlen : args.length = ps.length) (hargs : DenAll (ps.map (·.2)) m args)
    (htys : ∀ p ∈ ps, FirstOrder p.2 = true ∧ isAliasTy p.2 = false) :
    EnvOk ps (pushMethodFrame m (requiredFrame recv name md (ps.map (·.1)) args)) := by
  constructor
  · intro x τ hget
    obtain ⟨v, hv, hd⟩ := required_lookup hargs hget
    obtain ⟨z, hz⟩ := envGet?_mem hget
    have ht := htys (z, τ) hz
    have hs : stripAlias τ = τ := by cases τ <;> simp_all [stripAlias, isAliasTy]
    constructor
    · rw [requiredFrame_getLocal, hv, Option.getD_some, hs]
      exact (denM_heap_only (m₁ := m)
        (m₂ := pushMethodFrame m (requiredFrame recv name md (ps.map (·.1)) args)) ht.1 rfl).mp hd
    · intro y ρ hy
      rw [hy] at ht
      simp [isAliasTy] at ht
  · intro x hx
    rw [requiredFrame_getLocal, required_lookup_none hlen hx]
    rfl

#print axioms enterUserMethod_required
#print axioms requiredFrame_envOk
end Ratchet.Denote.Typed
