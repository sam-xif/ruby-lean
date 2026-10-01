import RubyCore.Heap

/-! Congruence for the heap reads used by dispatch and diagnostics. These lemmas
follow the current recursive name rendering and visibility-forwarding lookup,
including the optional Object fallback. -/

namespace RubyCore.Proof

def nameFields (c : ClassPayload) : String × Bool × Option ObjId :=
  (c.name, c.isModule, c.attached)

section Names
variable {h h' : Heap}
    (hp : ∀ k, (h'.classPayload? k).map nameFields = (h.classPayload? k).map nameFields)
    (hk : ∀ k, (h'.get k).klass = (h.get k).klass)
    (he : ∀ k, (h'.get k).eigen = (h.get k).eigen)

include hp hk he in
theorem classPath_go_congr (fuel : Nat) :
    ∀ k, classPath.go h' fuel k = classPath.go h fuel k := by
  have hco (k) : classOf h' (.ref k) = classOf h (.ref k) := by
    simp only [classOf, hk, he]
  induction fuel with
  | zero => intro k; rfl
  | succ fuel ih =>
    intro k
    have hp := hp k
    cases h1 : h'.classPayload? k <;> cases h2 : h.classPayload? k <;>
      simp_all [nameFields, classPath.go]

include hp hk he in
theorem className_go_congr (hs : h'.objs.size = h.objs.size) (fuel : Nat) :
    ∀ k, className.go h' fuel k = className.go h fuel k := by
  have paths : ∀ k, classPath h' k = classPath h k := by
    intro k
    simp only [classPath, hs, classPath_go_congr hp hk he]
  induction fuel with
  | zero => intro k; rfl
  | succ fuel ih =>
    intro k
    have fields := hp k
    cases h1 : h'.classPayload? k with
    | none =>
      cases h2 : h.classPayload? k <;> simp_all [className.go]
    | some c' =>
      cases h2 : h.classPayload? k with
      | none => simp_all
      | some c =>
        simp only [h1, h2, Option.map_some, Option.some.injEq,
          nameFields, Prod.mk.injEq] at fields
        simp only [className.go, h1, h2, fields.2.2]
        cases ha : c.attached with
        | none => exact paths k
        | some o =>
          have fieldsO := hp o
          cases hh1 : h'.classPayload? o <;> cases hh2 : h.classPayload? o <;>
            simp_all

include hp hk he in
theorem classNames_congr' (hs : h'.objs.size = h.objs.size) :
    ∀ k, className h' k = className h k := by
  intro k
  simp only [className, hs, className_go_congr hp hk he hs]

end Names

theorem classNames_congr {h h' : Heap}
    (hs : h'.objs.size = h.objs.size)
    (hp : ∀ k, (h'.classPayload? k).map nameFields = (h.classPayload? k).map nameFields)
    (hk : ∀ k, (h'.get k).klass = (h.get k).klass)
    (he : ∀ k, (h'.get k).eigen = (h.get k).eigen) :
    ∀ k, className h' k = className h k := classNames_congr' hp hk he hs

theorem lookupInChain_go_congr {h h' : Heap} {name : String}
    (hp : ∀ k, (h'.classPayload? k).map (fun c => (c.methods.find? (·.1 == name), c.isModule)) =
      (h.classPayload? k).map (fun c => (c.methods.find? (·.1 == name), c.isModule)))
    (ha : ancestors h' Boot.objectId = ancestors h Boot.objectId) :
    ∀ fuel chain used, lookupInChain.go h' name fuel chain used =
      lookupInChain.go h name fuel chain used := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro chain used
    cases used <;> cases chain with
    | nil => rfl
    | cons k rest =>
      have hp := hp k
      cases h1 : h'.classPayload? k <;> cases h2 : h.classPayload? k <;>
        simp_all [lookupInChain.go]

theorem lookupInChain_congr {h h' : Heap} {name : String}
    (hs : h'.objs.size = h.objs.size)
    (hp : ∀ k, (h'.classPayload? k).map (fun c => (c.methods.find? (·.1 == name), c.isModule)) =
      (h.classPayload? k).map (fun c => (c.methods.find? (·.1 == name), c.isModule)))
    (ha : ancestors h' Boot.objectId = ancestors h Boot.objectId) (chain : List ObjId) :
    lookupInChain h' chain name = lookupInChain h chain name := by
  simp only [lookupInChain, hs, lookupInChain_go_congr hp ha]

/-! Separate the finite chain traversal from its execution fuel. Object fallback
is used at most once; its traversal therefore has its own non-fallback scan. -/
def lookupBare (h : Heap) (name : String) : List ObjId → Option (ObjId × MethodDef)
  | [] => none
  | k :: rest =>
    match h.classPayload? k with
    | none => lookupBare h name rest
    | some cp => match cp.methods.find? (·.1 == name) with
      | none => lookupBare h name rest
      | some (_, md) =>
        if !md.visibilityOnly then some (k, md) else
        (lookupBare h name rest).map fun (owner, actual) =>
          (owner, { actual with visibility := md.visibility })

def lookupScan (h : Heap) (name : String) : List ObjId → Option (ObjId × MethodDef)
  | [] => none
  | k :: rest =>
    match h.classPayload? k with
    | none => lookupScan h name rest
    | some cp => match cp.methods.find? (·.1 == name) with
      | none => lookupScan h name rest
      | some (_, md) =>
        if !md.visibilityOnly then some (k, md) else
        let body := (lookupScan h name rest).orElse fun _ =>
          if cp.isModule then lookupBare h name (ancestors h Boot.objectId) else none
        body.map fun (owner, actual) => (owner, { actual with visibility := md.visibility })

theorem lookup_go_bare (h : Heap) (name : String) (chain : List ObjId)
    (fuel : Nat) (hf : chain.length ≤ fuel) :
    lookupInChain.go h name fuel chain true = lookupBare h name chain := by
  induction chain generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons k rest ih =>
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have hrest : rest.length ≤ fuel := by simpa using hf
      simp only [lookupInChain.go, lookupBare]
      rw [ih fuel hrest]
      cases h.classPayload? k with
      | none => rfl
      | some cp =>
        dsimp only
        split <;> rename_i he <;> rw [he] <;> simp

theorem lookup_go_scan (h : Heap) (name : String) (chain : List ObjId)
    (fuel : Nat) (hf : chain.length + (ancestors h Boot.objectId).length ≤ fuel) :
    lookupInChain.go h name fuel chain false = lookupScan h name chain := by
  induction chain generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons k rest ih =>
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have hrest : rest.length + (ancestors h Boot.objectId).length ≤ fuel := by
        simp only [List.length_cons] at hf; omega
      simp only [lookupInChain.go, lookupScan]
      rw [ih fuel hrest, lookup_go_bare h name _ fuel (by omega)]
      cases h.classPayload? k with
      | none => rfl
      | some cp =>
        dsimp only
        split <;> rename_i he <;> rw [he] <;> simp

theorem lookupInChain_eq_scan (h : Heap) (name : String) (chain : List ObjId)
    (hf : chain.length + (ancestors h Boot.objectId).length ≤ 2 * h.objs.size + 2) :
    lookupInChain h chain name = lookupScan h name chain :=
  lookup_go_scan h name chain _ hf

theorem lookupBare_congr {h h' : Heap} {name : String} {chain : List ObjId}
    (hp : ∀ k ∈ chain, (h'.classPayload? k).map (fun c => c.methods.find? (·.1 == name)) =
      (h.classPayload? k).map (fun c => c.methods.find? (·.1 == name))) :
    lookupBare h' name chain = lookupBare h name chain := by
  induction chain with
  | nil => rfl
  | cons k rest ih =>
    have fields := hp k (by simp)
    have hr := ih (fun j hj => hp j (List.mem_cons_of_mem _ hj))
    cases h1 : h'.classPayload? k <;> cases h2 : h.classPayload? k <;>
      simp_all [lookupBare]

theorem lookupScan_congr {h h' : Heap} {name : String} {chain : List ObjId}
    (hp : ∀ k ∈ chain, (h'.classPayload? k).map
        (fun c => (c.methods.find? (·.1 == name), c.isModule)) =
      (h.classPayload? k).map (fun c => (c.methods.find? (·.1 == name), c.isModule)))
    (hb : lookupBare h' name (ancestors h' Boot.objectId) =
      lookupBare h name (ancestors h Boot.objectId)) :
    lookupScan h' name chain = lookupScan h name chain := by
  induction chain with
  | nil => rfl
  | cons k rest ih =>
    have fields := hp k (by simp)
    have hr := ih (fun j hj => hp j (List.mem_cons_of_mem _ hj))
    cases h1 : h'.classPayload? k <;> cases h2 : h.classPayload? k <;>
      simp_all [lookupScan]

/-- Different execution budgets are harmless once each can traverse both the
    supplied chain and the one permitted Object fallback. -/
theorem lookupInChain_grow_congr {h h' : Heap} {name : String} {chain : List ObjId}
    (hs : h.objs.size ≤ h'.objs.size)
    (ha : ancestors h' Boot.objectId = ancestors h Boot.objectId)
    (hf : chain.length + (ancestors h Boot.objectId).length ≤ 2 * h.objs.size + 2)
    (hp : ∀ k ∈ chain ++ ancestors h Boot.objectId, h'.classPayload? k = h.classPayload? k) :
    lookupInChain h' chain name = lookupInChain h chain name := by
  rw [lookupInChain_eq_scan h name chain hf,
    lookupInChain_eq_scan h' name chain (by rw [ha]; omega)]
  apply lookupScan_congr
  · intro k hk; rw [hp k (List.mem_append_left _ hk)]
  · rw [ha]
    apply lookupBare_congr
    intro k hk; rw [hp k (List.mem_append_right _ hk)]

/-- Lookup returns an implementation, never an unresolved visibility wrapper. -/
theorem lookupInChain_go_body (h : Heap) (name : String) :
    ∀ fuel chain used, (lookupInChain.go h name fuel chain used).all
      (fun pair => !pair.2.visibilityOnly) = true := by
  have hor {a b : Option (ObjId × MethodDef)}
      (ha : a.all (fun pair => !pair.2.visibilityOnly) = true)
      (hb : b.all (fun pair => !pair.2.visibilityOnly) = true) :
      (a.orElse (fun _ => b)).all (fun pair => !pair.2.visibilityOnly) = true := by
    cases a <;> simp_all [Option.orElse]
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro chain used
    cases chain with
    | nil => rfl
    | cons k rest =>
      simp only [lookupInChain.go]
      cases hc : h.classPayload? k with
      | none => exact ih rest used
      | some cp =>
        simp only
        cases hm : cp.methods.find? (·.1 == name) with
        | none => exact ih rest used
        | some pair =>
          dsimp only
          split
          · rename_i hv; simpa using hv
          · simp only [Option.all_map, Function.comp_def]
            apply hor (ih rest used)
            split
            · exact ih _ true
            · rfl

theorem lookupInChain_body {h : Heap} {chain : List ObjId} {name : String}
    {owner : ObjId} {md : MethodDef} (hr : lookupInChain h chain name = some (owner, md)) :
    md.visibilityOnly = false := by
  have hp := lookupInChain_go_body h name (2 * h.objs.size + 2) chain false
  change (lookupInChain h chain name).all _ = true at hp
  simpa [hr] using hp

end RubyCore.Proof
