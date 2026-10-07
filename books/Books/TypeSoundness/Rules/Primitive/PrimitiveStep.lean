import Books.TypeSoundness.Rules.Primitive.PrimitiveFacts

/-! A dispatch step may return a value, raise a non-type exception, or gate. All three
are represented here without discarding the answer contract. -/

set_option autoImplicit false
set_option maxRecDepth 4000
namespace Checker.Soundness.Typed
open RubyCore Checker Checker.Soundness

def StepSpec (origin : Machine) (Γ : Env) (τ : Ty) (step : StepResult)
    (κ : Ctx := ctx0) (I : Ty := .ivar0) : Prop := match step with
  | .next n => RunSpec origin n Γ τ κ I
  | .unsupported _ => True
  | _ => False

theorem StepSpec.rebase {origin middle : Machine} {Γ : Env} {τ I : Ty} {κ : Ctx}
    {step : StepResult} (h : StepSpec middle Γ τ step κ I) (hf : Framed origin middle) :
    StepSpec origin Γ τ step κ I := by
  cases step with
  | next n => exact RunSpec.rebase h hf
  | unsupported _ => trivial
  | done _ _ | uncaught _ _ | stuck _ => exact h

theorem RunSpec.of_stepSpec {origin start : Machine} {Γ : Env} {τ : Ty} {κ : Ctx} {I : Ty}
    (ha : answerPoint start = none) (h : StepSpec origin Γ τ (Interp.stepFn start) κ I) :
    RunSpec origin start Γ τ κ I := by
  cases hs : Interp.stepFn start with
  | next n => exact RunSpec.step ha hs (by simpa [hs, StepSpec] using h)
  | unsupported r => exact RunSpec.unsupported ha hs
  | done v n => simp [hs, StepSpec] at h
  | uncaught v n => simp [hs, StepSpec] at h
  | stuck msg => simp [hs, StepSpec] at h

theorem stepSpec_value {κ : Ctx} {I : Ty} {Γ : Env} {τ : Ty} {m : Machine} {v : Value}
    (hm : StateOk κ Γ I m) (hk : m.kont = []) (hd : denM τ m v) :
    StepSpec m Γ τ (.next (Interp.withCtl m (.value v))) κ I := by
  have h := RunSpec.answer (a := .val v)
    (show ResultOk m Γ τ (.val v) m κ I from ⟨.refl m, hd, fun _ hv => by cases hv; exact hm⟩)
  simpa only [StepSpec, Interp.withCtl, deliverA, Answer.ctl, hk] using h

def builtinStep (r : BRes) : StepResult :=
  match r with
  | .ok v n => .next (Interp.withCtl n (.value v))
  | .err cls msg n => .next (Interp.raiseErr n cls msg)
  | .throwV v n => .next (Interp.withCtl n (.jump (.raiseJ v)))
  | .frozen recv n => Interp.raiseFrozen n recv
  | .unsupported r => .unsupported r

theorem invoke_plain {site : SendSite} {m : Machine} {recv : Value} {name : String} {args : List Value}
    (hn : (name == "send" || name == "public_send" || name == "__send__") = false)
    (hr : ∀ o, recv = .ref o → ∃ s, (m.heap.get o).payload = .str s) :
    Interp.invoke m recv site name args none [] =
      Interp.invoke.invokeDispatch m recv site name args none [] := by
  rw [Interp.invoke.eq_def]
  simp only [hn, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  cases recv with
  | ref o => obtain ⟨s, hs⟩ := hr o rfl; simp only [hs]
  | _ => rfl

theorem primitive_invoke {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine}
    {recv : Value} {name bid : String} {args : List Value} {k : ObjId} (hm : StateOk κ Γ I m)
    (hrow : (k, name, bid) ∈ primitiveMethods) (hc : classOf m.heap recv = k)
    (hn : (name == "send" || name == "public_send" || name == "__send__") = false)
    (hr : ∀ o, recv = .ref o → ∃ s, (m.heap.get o).payload = .str s)
    (hd : Builtins.deferTwin? m.heap bid recv args = none)
    (hraise : (bid == "Object#raise") = false) (hf : nameFreeN κ name = true := by rfl)
    (hplus : bid ≠ "String#+" := by decide) :
    Interp.invoke m recv site name args none [] = builtinStep (Builtins.run bid recv args m) := by
  obtain ⟨owner, md, hl, hb, hu, hv, hp, hs⟩ := primitive_lookup hm hrow hf
  rw [invoke_plain hn hr]
  have hproc : Interp.procCallBid bid = false :=
    (show ∀ x ∈ primitiveMethods, Interp.procCallBid x.2.2 = false by decide +kernel) _ hrow
  have hmap : Interp.arrayMapBid bid = false :=
    (show ∀ x ∈ primitiveMethods, Interp.arrayMapBid x.2.2 = false by decide +kernel) _ hrow
  apply invokeDispatch_builtin (owner := owner) (md := md) (hentry := ?_) _ hb hu hv hp _ hd hraise hproc hmap
  · rw [lookup_eq_methodOn, hc]; exact hl
  · simpa only [hc] using hs
  · have hall : primitiveMethods.all (fun x => x.2.2 == "String#+" ||
        !(x.2.2.startsWith "Main#" ||
        ["Object#inspect", "Object#raise", "Object#fail", "Exception.exception",
         "Exception#exception", "Exception#to_s", "UncaughtThrowError#to_s",
         "Object#initialize_dup", "Object#initialize_clone", "String#initialize_copy",
         "Array#initialize_copy", "Hash#initialize_copy", "Class#new", "Module#new",
         "Class#allocate", "Module#const_set", "Class#initialize", "Module#initialize",
         "String#initialize", "Array#initialize", "Hash#initialize", "Exception#initialize",
         "Object#__forwardable_compile", "String#+"].contains x.2.2 ||
        Interp.nativeDupBid x.2.2 || Interp.nativeCloneBid x.2.2 || Interp.requireBid x.2.2 ||
        Interp.enumBid x.2.2 || Interp.nativeIteratorBid x.2.2)) = true := by decide +kernel
    have h := List.all_eq_true.mp hall _ hrow
    simp only [Bool.or_eq_true, beq_iff_eq, hplus, false_or, Bool.not_eq_true'] at h
    exact h

/-- String addition uses the interpreter conversion entry, whose conversion
branch is skipped only after proving the source already has a String payload. -/
theorem invoke_string_add {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine}
    (hm : StateOk κ Γ I m) {o p : ObjId} {s t : String}
    (hc : classOf m.heap (.ref o) = Boot.stringId)
    (ho : (m.heap.get o).payload = .str s) (hp : (m.heap.get p).payload = .str t)
    (hf : nameFreeN κ "+" = true := by rfl) :
    Interp.invoke m (.ref o) site "+" [.ref p] none [] =
      builtinStep (Builtins.run "String#+" (.ref o) [.ref p] m) := by
  obtain ⟨owner, md, hl, hb, hu, hv, hpre, hs⟩ :=
    primitive_lookup hm (k := Boot.stringId) (name := "+") (bid := "String#+")
      (by simp [primitiveMethods]) hf
  have hlookup : lookup m.heap (.ref o) "+" = some (owner, md) := by
    rw [lookup_eq_methodOn, hc]; exact hl
  have hvis : Interp.visError? m (.ref o) site md "+" = none := by
    cases site <;> simp [Interp.visError?, hv]
  rw [invoke_plain (by rfl) (fun k hk => by cases hk; exact ⟨s, ho⟩)]
  simp only [Interp.invoke.invokeDispatch, hlookup, hu, hpre, Interp.crubyResolvedShadow,
    hb, Option.any, show ["Class#new", "Module#new", "Class#allocate"].contains "String#+" = false from rfl,
    Bool.false_eq_true, ↓reduceIte, hc, hs, hvis]
  simp only [show "String#+".startsWith "Main#" = false from by decide +kernel,
    show Interp.nativeDupBid "String#+" = false from by decide +kernel,
    show Interp.nativeCloneBid "String#+" = false from by decide +kernel,
    show Interp.requireBid "String#+" = false from by decide +kernel,
    show Interp.enumBid "String#+" = false from by decide +kernel,
    show Interp.nativeIteratorBid "String#+" = false from by decide +kernel,
    Bool.false_eq_true, ↓reduceIte]
  change Interp.callStringPlusBuiltin m (.ref o) [.ref p] [] = _
  simp only [Interp.callStringPlusBuiltin, Interp.appendKwHash, List.isEmpty,
    ↓reduceIte, Builtins.strPayload?, hp, Option.isNone, Bool.false_eq_true]
  rfl

theorem invoke_int_add {κ : Ctx} {I : Ty} {site : SendSite} {Γ : Env} {m : Machine}
    (hm : StateOk κ Γ I m) (x y : Int) (hf : nameFreeN κ "+" = true := by rfl) :
    Interp.invoke m (.int x) site "+" [.int y] none [] =
      .next (Interp.withCtl m (.value (.int (x + y)))) := by
  rw [primitive_invoke (bid := "Integer#+") (k := Boot.integerId) hm
    (by simp [primitiveMethods]) rfl (by rfl)
    (by intro o ho; cases ho) (by rfl) (by rfl) hf, int_add_run]
  rfl

#print axioms invoke_string_add
#print axioms invoke_int_add
end Checker.Soundness.Typed
