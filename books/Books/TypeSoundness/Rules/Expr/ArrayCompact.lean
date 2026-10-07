import Books.TypeSoundness.Rules.Expr.ArrayIndex

/-! `Array#compact` and `Array#uniq`: native filters allocating a fresh Array whose
elements are drawn from the receiver's payload. -/
set_option autoImplicit false
set_option maxRecDepth 4000
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

/-- A fresh Array preserves full caller conformance and carries the supplied element
types. Shared by literals and native map's final accumulator allocation. -/
theorem array_alloc_result {κ : Ctx} {I : Ty} {Γ : Env} {m : Machine} {τ : Ty}
    (hm : StateOk κ Γ I m)
    (xs : List Value) (hd : ∀ x ∈ xs, denM τ m x) :
    ResultOk m Γ (.arrayOf τ) (.val (Builtins.allocArr m xs.toArray).1)
      (Builtins.allocArr m xs.toArray).2 κ I := by
  let obj : Object := { klass := Boot.arrayId, payload := .arr xs.toArray }
  let n : Machine := { m with heap := pushHeap m.heap obj }
  have he : Ext m n := ext_push obj hm.sat hm.core.basicSelf
    (fun c => by simp [obj]) rfl rfl hm.core.arrayBasic
  have hn : StateOk κ Γ I n := StateOk_ext hm he
    (stringPayloadOk_push hm.stringPayload (by simp [obj, Boot.arrayId, Boot.stringId]))
    (arrayPayloadOk_push hm.arrayPayload (by simp [obj]))
    (hashPayloadOk_push hm.hashPayload (by simp [obj])) rfl
  have hv : denM (.arrayOf τ) n (.ref m.heap.objs.size) := by
    rw [denM]
    refine ⟨xs.toArray, ?_, ?_⟩
    · simp [arrElems?, n, pushHeap_get_self, obj]
    · intro x hx
      exact denM_ext he (hd x (by simpa using hx))
  exact ⟨Framed.of_ext he, hv, fun _ hv => by cases hv; exact hn⟩

theorem array_filter_invoke {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine} {o : ObjId}
    {xs : Array Value} {name bid : String} (hm : StateOk κ Γ I m)
    (hp : (m.heap.get o).payload = .arr xs)
    (hrow : (Boot.arrayId, name, bid) ∈ primitiveMethods)
    (hn : (name == "send" || name == "public_send" || name == "__send__") = false)
    (hfree : nameFreeN κ name = true)
    (hproc : Interp.procCallBid bid = false) (hmap : Interp.arrayMapBid bid = false)
    (hraise : (bid == "Object#raise") = false)
    (hentry : (bid.startsWith "Main#" ||
      ["Object#inspect", "Object#raise", "Object#fail", "Exception.exception",
       "Exception#exception", "Exception#to_s", "UncaughtThrowError#to_s",
       "Object#initialize_dup", "Object#initialize_clone", "String#initialize_copy",
       "Array#initialize_copy", "Hash#initialize_copy", "Class#new", "Module#new",
       "Class#allocate", "Module#const_set", "Class#initialize", "Module#initialize",
       "String#initialize", "Array#initialize", "Hash#initialize", "Exception#initialize",
       "Object#__forwardable_compile", "String#+"].contains bid ||
      Interp.nativeDupBid bid || Interp.nativeCloneBid bid || Interp.requireBid bid ||
      Interp.enumBid bid || Interp.nativeIteratorBid bid) = false)
    (hd : Builtins.deferTwin? m.heap bid (.ref o) [] = none) :
    Interp.invoke m (.ref o) site name [] none [] =
      builtinStep (Builtins.run bid (.ref o) [] m) := by
  have hc := hm.arrayPayload o xs hp
  have hi : Interp.invoke m (.ref o) site name [] none [] =
      Interp.invoke.invokeDispatch m (.ref o) site name [] none [] := by
    rw [Interp.invoke.eq_def]
    simp only [hn, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hp]
  obtain ⟨owner, md, hl, hb, hu, hv, hpre, hs⟩ := primitive_lookup hm hrow hfree
  rw [hi]
  apply invokeDispatch_builtin (owner := owner) (md := md) _ hb hu hv hpre _ hd hraise hproc hmap hentry
  · rw [lookup_eq_methodOn, hc]; exact hl
  · simpa only [hc] using hs

/-- A fresh Array of receiver elements, all retained in `τ`. -/
theorem stepSpec_allocArr {κ : Ctx} {I : Ty} {Γ : Env} {m : Machine} {τ : Ty}
    (hm : StateOk κ Γ I m) (hk : m.kont = []) (ys : Array Value) (hd : ∀ x ∈ ys, denM τ m x) :
    StepSpec m Γ (.arrayOf τ)
      (builtinStep (.ok (Builtins.allocArr m ys).1 (Builtins.allocArr m ys).2)) κ I := by
  have h := RunSpec.answer (array_alloc_result hm ys.toList (fun x hx => hd x (by simpa using hx)))
  simpa only [StepSpec, builtinStep, Array.toArray_toList, Builtins.allocArr, Heap.alloc,
    Interp.withCtl, deliverA, Answer.ctl, reCtl, hk] using h

theorem array_compact_step {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine}
    {recv : Value} {τ : Ty} (hm : StateOk κ Γ I m) (hk : m.kont = [])
    (hd : denM (.arrayOf (.nilable τ)) m recv) (hfree : nameFreeN κ "compact" = true := by rfl) :
    StepSpec m Γ (.arrayOf τ) (Interp.invoke m recv site "compact" [] none []) κ I := by
  obtain ⟨o, xs, rfl, hp, hxs⟩ := array_payload hd
  rw [array_filter_invoke (bid := "Array#compact") hm hp (by simp [primitiveMethods]) rfl hfree
    rfl rfl rfl (by decide +kernel) (by
      simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
        Builtins.toAryDefer?, Builtins.strCmpDefer?, Builtins.strCmpTwin?])]
  have hr : Builtins.run "Array#compact" (.ref o) [] m =
      Builtins.runCollections "Array#compact" (.ref o) [] m := by
    simp only [Builtins.run, List.any_cons, List.any_nil, Builtins.unrepresentableByteStr,
      Builtins.strPayload?, hp, Bool.false_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    simp only [show ("Array#compact".endsWith "#==" || "Array#compact".endsWith "#eql?" ||
      "Array#compact".endsWith "#!=" || Builtins.pureEqualityBids.contains "Array#compact") = false
      from by decide +kernel,
      Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [hr]
  unfold Builtins.runCollections
  simp only [Builtins.arrPayload?, hp]
  apply stepSpec_allocArr hm hk
  intro x hx
  simp only [Array.mem_filter] at hx
  obtain ⟨hx, hn⟩ := hx
  have h := hxs x hx
  rw [denM] at h
  rcases h with h | h
  · cases x <;> simp_all [isNilV]
  · exact h

theorem array_uniq_step {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine}
    {recv : Value} {τ : Ty} (hm : StateOk κ Γ I m) (hk : m.kont = [])
    (hd : denM (.arrayOf τ) m recv) (hfree : nameFreeN κ "uniq" = true := by rfl) :
    StepSpec m Γ (.arrayOf τ) (Interp.invoke m recv site "uniq" [] none []) κ I := by
  obtain ⟨o, xs, rfl, hp, hxs⟩ := array_payload hd
  rw [array_filter_invoke (bid := "Array#uniq") hm hp (by simp [primitiveMethods]) rfl hfree
    rfl rfl rfl (by decide +kernel) (by
      simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
        Builtins.toAryDefer?, Builtins.strCmpDefer?, Builtins.strCmpTwin?])]
  have hfold : ∀ (l : List Value) (acc : Array Value), (∀ x ∈ acc, denM τ m x) →
      (∀ x ∈ l, denM τ m x) → ∀ x ∈ l.foldl (fun acc x =>
        if acc.any (valueEql m.heap x ·) then acc else acc.push x) acc, denM τ m x := by
    intro l
    induction l with
    | nil => intro acc ha _; simpa using ha
    | cons y l ih =>
      intro acc ha hl
      simp only [List.foldl_cons]
      apply ih _ _ (fun x hx => hl x (by simp [hx]))
      by_cases hc : acc.any (valueEql m.heap y ·) = true
      · simp only [hc, ↓reduceIte]; exact ha
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        intro x hx
        rcases Array.mem_push.mp hx with h | h
        · exact ha x h
        · subst h; exact hl x (by simp)
  have hys := hfold xs.toList #[] (by simp) (fun x hx => hxs x (by simpa using hx))
  simp only [Builtins.run, List.any_cons, List.any_nil, Builtins.unrepresentableByteStr,
    Builtins.strPayload?, hp, Bool.or_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  simp only [show ("Array#uniq" != "Complex#eql?") = true from rfl,
    show Builtins.pureEqualityBids.contains "Array#uniq" = true from by decide +kernel,
    Bool.or_true, Bool.true_and]
  split
  · trivial
  · simp only [show Builtins.zeroArgBids.contains "Array#uniq" = true from by decide +kernel,
      List.isEmpty_nil, Bool.not_true, Bool.and_false,
      show Builtins.dupBids.contains "Array#uniq" = false from by decide +kernel,
      show Builtins.cloneBids.contains "Array#uniq" = false from by decide +kernel,
      Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    change StepSpec m Γ _ (builtinStep (Builtins.runCollections "Array#uniq" (.ref o) [] m)) κ I
    unfold Builtins.runCollections
    simp only [Builtins.arrPayload?, hp]
    apply stepSpec_allocArr hm hk
    simpa only [Array.foldl_toList] using hys

#print axioms array_compact_step
#print axioms array_uniq_step
end Checker.Soundness.Typed
