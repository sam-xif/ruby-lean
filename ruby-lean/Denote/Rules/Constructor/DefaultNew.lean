import Denote.Rules.Expr.Send
import Denote.Sem.Names.RootLookup
import Denote.Sem.Class.ClassGuards
import Ratchet.Guards.NilFields

/-! Default construction on the actual dispatch: Class#new allocates, sends a real
reflective initialize (the native no-op), and newK yields the instance. Native shadow
gates are unsupported outcomes, not premises. -/
set_option autoImplicit false
set_option maxRecDepth 4000
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

def defaultAllocated (m : Machine) (k : ObjId) : Machine :=
  { m with heap := pushHeap m.heap { klass := k } }

theorem defaultAllocated_ext {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {k : ObjId}
    (hm : StateOk κ Γ I m) (hc : PlainAllocator m.heap k) : Ext m (defaultAllocated m k) :=
  ext_push { klass := k } hm.sat hm.core.basicSelf (by intro c; cases c; simp) rfl rfl hc.rooted

theorem defaultAllocated_state {κ : Ctx} {Γ : Env} {I : Ty} {m : Machine} {k : ObjId}
    (hm : StateOk κ Γ I m) (hc : PlainAllocator m.heap k) : StateOk κ Γ I (defaultAllocated m k) :=
  StateOk_ext hm (defaultAllocated_ext hm hc)
    (stringPayloadOk_push hm.stringPayload (by simpa using hc.notString))
    (arrayPayloadOk_push hm.arrayPayload (by simp)) (hashPayloadOk_push hm.hashPayload (by simp)) rfl

theorem denSpineFrom_nilFields {J : Ty} (hj : nilFieldsB J = true) (seen : List String) (m : Machine) :
    denSpineFrom seen J m (fun _ => .nil) := by
  induction J generalizing seen with
  | ivar0 => simp [denSpineFrom]
  | ivarCons x ty rest _ ih =>
    cases ty <;> simp only [nilFieldsB, Bool.false_eq_true] at hj
    simp only [denSpineFrom]
    exact ⟨Or.inr (by simp [denM, isNilV]), ih hj _⟩
  | _ => cases hj

theorem defaultAllocated_receiver {κ : Ctx} {Γ : Env} {I J : Ty} {m : Machine} {k : ObjId} {cn : String}
    (hm : StateOk κ Γ I m) (hc : PlainAllocator m.heap k) (hn : classNamed? m.heap cn = some k)
    (hj : nilFieldsB J = true) :
    denM (.inst cn J) (defaultAllocated m k) (.ref m.heap.objs.size) := by
  have he := defaultAllocated_ext hm hc
  rw [denM]
  simp only [isExactInst, he.classNamed?_eq, hn]
  simp only [defaultAllocated, pushHeap_get_self]
  refine ⟨by simp [pushHeap], ?_⟩
  have hg : ivarOf (pushHeap m.heap { klass := k }) (.ref m.heap.objs.size) = fun _ => .nil := by
    funext x
    simp [ivarOf, pushHeap_get_self]
  rw [hg]
  exact denSpineFrom_nilFields hj [] _

theorem stepSpec_defaultAllocated {κ : Ctx} {Γ : Env} {I J : Ty} {m : Machine} {k : ObjId} {cn : String}
    (hm : StateOk κ Γ I m) (hc : PlainAllocator m.heap k) (hn : classNamed? m.heap cn = some k)
    (hk : m.kont = []) (hj : nilFieldsB J = true) :
    StepSpec m Γ (.inst cn J)
      (.next (Interp.withCtl (defaultAllocated m k) (.value (.ref m.heap.objs.size)))) κ I := by
  have hs := defaultAllocated_state hm hc
  have hd := defaultAllocated_receiver hm hc hn hj
  have hf := Framed.of_ext (defaultAllocated_ext hm hc)
  have h := RunSpec.answer (a := .val (.ref m.heap.objs.size))
    (show ResultOk m Γ (.inst cn J) _ _ κ I from ⟨hf, hd, fun _ hv => by cases hv; exact hs⟩)
  simpa only [StepSpec, defaultAllocated, Interp.withCtl, deliverA, Answer.ctl, reCtl, hk] using h

theorem finishSend_new {m : Machine} {k : ObjId} (hc : PlainAllocator m.heap k) :
    Interp.finishSend m (.ref k) .explicit "new" [] .none =
      Interp.invoke.invokeDispatch m (.ref k) .explicit "new" [] none [] := by
  obtain ⟨cp, hp, _⟩ := hc.payload
  simp only [Interp.finishSend]
  rw [Interp.invoke.eq_def]
  simp only [show ("new" == "send") = false from rfl,
    show ("new" == "public_send") = false from rfl,
    show ("new" == "__send__") = false from rfl,
    Bool.false_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hp,
    beq_eq_false_iff_ne.mpr hc.notMath]
  simp only [show ("new" == "escape" || "new" == "quote" || "new" == "union") = false from rfl,
    Bool.and_false, Bool.false_eq_true, ↓reduceIte]

theorem invokeDispatch_classNew {m : Machine} {recv : Value} {site : SendSite} {name : String}
    {args : List Value} {owner : ObjId} {md : MethodDef}
    (hl : lookup m.heap recv name = some (owner, md))
    (hb : md.builtin = some "Class#new") (hu : md.undefined = false) (hv : md.visibility = .pub) :
    (∃ msg, Interp.invoke.invokeDispatch m recv site name args none [] = .unsupported msg) ∨
      Interp.invoke.invokeDispatch m recv site name args none [] =
        Interp.callConstruct m recv args none [] := by
  have hvis : Interp.visError? m recv site md name = none := by
    cases site <;> simp [Interp.visError?, hv]
  simp only [Interp.invoke.invokeDispatch, hl, hu, Bool.false_eq_true, ↓reduceIte]
  split
  · exact Or.inl ⟨_, rfl⟩
  · right
    simp only [hvis, hb, show "Class#new".startsWith "Main#" = false from by decide +kernel,
      show Interp.nativeDupBid "Class#new" = false from by decide +kernel,
      show Interp.nativeCloneBid "Class#new" = false from by decide +kernel,
      Bool.false_eq_true, ↓reduceIte]
    simp

theorem _root_.Ratchet.Denote.PlainAllocator.chain_free {h : Heap} {k a : ObjId} (hc : PlainAllocator h k)
    (ha : a ∈ constructBlockers) : (ancestors h k).contains a = false ∧ k ≠ a := by
  have hall := List.all_eq_true.mp hc.plainChain
  constructor
  · cases he : (ancestors h k).contains a with
    | false => rfl
    | true =>
      have := hall a (List.mem_cons_of_mem _ (List.contains_iff_mem.mp he))
      simp at this
      exact absurd ha this
  · intro hk
    subst hk
    have := hall k (List.mem_cons_self ..)
    simp at this
    exact absurd ha this

theorem callConstruct_plain {m : Machine} {k : ObjId} (hc : PlainAllocator m.heap k) :
    Interp.callConstruct m (.ref k) [] none [] =
      .next { defaultAllocated m k with
        ctl := .send (.ref m.heap.objs.size) .reflective "initialize" [] none [],
        kont := .newK (.ref m.heap.objs.size) :: m.kont } := by
  obtain ⟨cp, hp, hatt, hinit, _, hunav⟩ := hc.metadata
  obtain ⟨cp', hp', hmod⟩ := hc.payload
  rw [hp] at hp'; cases hp'
  have hcp : m.heap.classPayload? k = some cp := by simp [Heap.classPayload?, hp]
  have f (a : ObjId) (ha : a ∈ constructBlockers) := hc.chain_free ha
  unfold Interp.callConstruct
  simp only [hcp, hmod, hatt, hinit, hunav, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
    Bool.not_true, (f Boot.moduleId (by decide)).1]
  have hany (L : List ObjId) (hL : ∀ x ∈ L, x ∈ constructBlockers) :
      (ancestors m.heap k).any (fun x => L.contains x) = false := by
    apply List.any_eq_false.mpr
    intro x hx hl
    have := (f x (hL x (List.contains_iff_mem.mp hl))).1
    rw [List.contains_iff_mem.mpr hx] at this
    cases this
  have hk : [Boot.randomId, Boot.regexpId].contains k = false := by
    simp [(f Boot.randomId (by decide)).2, (f Boot.regexpId (by decide)).2]
  rw [hany _ (by decide), (f Boot.procId (by decide)).1, hk, hany _ (by decide), hany _ (by decide)]
  simp only [Bool.false_eq_true, ↓reduceIte, hc.noCore]
  rfl

theorem invokeDispatch_builtin_or {site : SendSite} {m : Machine} {recv : Value} {name bid : String}
    {args : List Value} {owner : ObjId} {md : MethodDef}
    (hl : lookup m.heap recv name = some (owner, md))
    (hb : md.builtin = some bid) (hu : md.undefined = false)
    (hvis : Interp.visError? m recv site md name = none)
    (hd : Builtins.deferTwin? m.heap bid recv args = none) (hn : (bid == "Object#raise") = false)
    (hc : Interp.procCallBid bid = false := by rfl)
    (hm : Interp.arrayMapBid bid = false := by rfl)
    (hentry : (bid.startsWith "Main#" ||
      ["Object#inspect", "Object#raise", "Object#fail", "Exception.exception",
       "Exception#exception", "Exception#to_s", "UncaughtThrowError#to_s",
       "Object#initialize_dup", "Object#initialize_clone", "String#initialize_copy",
       "Array#initialize_copy", "Hash#initialize_copy", "Class#new", "Module#new",
       "Class#allocate", "Module#const_set", "Class#initialize", "Module#initialize",
       "String#initialize", "Array#initialize", "Hash#initialize", "Exception#initialize",
       "Object#__forwardable_compile", "String#+"].contains bid ||
      Interp.nativeDupBid bid || Interp.nativeCloneBid bid || Interp.requireBid bid ||
      Interp.enumBid bid || Interp.nativeIteratorBid bid) = false := by decide +kernel) :
    (∃ msg, Interp.invoke.invokeDispatch m recv site name args none [] = .unsupported msg) ∨
    Interp.invoke.invokeDispatch m recv site name args none [] =
      match Builtins.run bid recv args m with
      | .ok v n => .next (Interp.withCtl n (.value v))
      | .err cls msg n => .next (Interp.raiseErr n cls msg)
      | .throwV v n => .next (Interp.withCtl n (.jump (.raiseJ v)))
      | .frozen recv n => Interp.raiseFrozen n recv
      | .unsupported r => .unsupported r := by
  simp only [Bool.or_eq_false_iff, List.contains_cons, List.contains_nil] at hentry
  rcases hentry with ⟨⟨⟨⟨⟨⟨hmain, hnames⟩, hdup⟩, hclone⟩, hrequire⟩, henum⟩, hiter⟩
  simp only [Interp.invoke.invokeDispatch, hl, hu, Bool.false_eq_true, ↓reduceIte]
  split
  · exact Or.inl ⟨_, rfl⟩
  · right
    simp only [hb, hmain, hdup, hclone, hrequire, henum, hiter, hvis, hc, hm, hd, hn,
      Option.isSome, Bool.false_and, Interp.appendKwHash, List.isEmpty, ↓reduceIte]
    simp_all only [Bool.or_eq_false_iff, Bool.false_or, Bool.or_false, Bool.false_eq_true,
      List.contains_cons, List.contains_nil, ↓reduceIte]
    cases Builtins.run bid recv args m <;> rfl

theorem invoke_payloadNone {site : SendSite} {m : Machine} {o : ObjId} {name : String}
    {args : List Value} (hn : (name == "send" || name == "public_send" || name == "__send__") = false)
    (hp : (m.heap.get o).payload = .none) :
    Interp.invoke m (.ref o) site name args none [] =
      Interp.invoke.invokeDispatch m (.ref o) site name args none [] := by
  rw [Interp.invoke.eq_def]
  simp only [hn, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hp]

theorem basic_initialize_run (m : Machine) (o : ObjId) (hp : (m.heap.get o).payload = .none) :
    Builtins.run "BasicObject#initialize" (.ref o) [] m = .ok .nil m := by
  simp only [Builtins.run, List.any_cons, List.any_nil, Builtins.unrepresentableByteStr,
    Builtins.strPayload?, hp, Builtins.complexEqualityImpure, Bool.false_or, Bool.or_false,
    Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- After allocation: the reflective initialize send and newK yield the instance. -/
theorem default_new_run {κ : Ctx} {Γ : Env} {I J : Ty} {m : Machine} {k : ObjId} {cn : String}
    (hm : StateOk κ Γ I m) (hc : PlainAllocator m.heap k) (hn : classNamed? m.heap cn = some k)
    (hk : m.kont = []) (hj : nilFieldsB J = true) (hinit : initDispatchB m.heap k = true) :
    RunSpec m { defaultAllocated m k with
        ctl := .send (.ref m.heap.objs.size) .reflective "initialize" [] none [],
        kont := .newK (.ref m.heap.objs.size) :: m.kont } Γ (.inst cn J) κ I := by
  let s := m.heap.objs.size
  let n1 : Machine := { defaultAllocated m k with
    ctl := .send (.ref s) .reflective "initialize" [] none [], kont := .newK (.ref s) :: m.kont }
  have hget : n1.heap.get s = { klass := k } := pushHeap_get_self m.heap _
  have he := defaultAllocated_ext hm hc
  have hlk : lookup n1.heap (.ref s) "initialize" = Interp.methodOn m.heap k "initialize" := by
    rw [lookup_eq_methodOn]
    change Interp.methodOn (defaultAllocated m k).heap (classOf n1.heap (.ref s)) "initialize" = _
    simp only [classOf, hget]
    exact he.methodOn_eq hm.core.classReady.chains _ _
  unfold initDispatchB at hinit
  cases hl : Interp.methodOn m.heap k "initialize" with
  | none => rw [hl] at hinit; cases hinit
  | some p =>
    obtain ⟨owner, md⟩ := p
    rw [hl] at hinit
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hinit
    have hs1 : Interp.stepFn n1 = Interp.invoke.invokeDispatch n1 (.ref s) .reflective "initialize" [] none [] :=
      invoke_payloadNone rfl (by rw [hget])
    rcases invokeDispatch_builtin_or (m := n1) (site := .reflective) (bid := "BasicObject#initialize") (args := [])
      (hlk.trans hl) hinit.1 hinit.2 (by simp [Interp.visError?])
      (by simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?, Builtins.toAryDefer?,
        Builtins.strCmpDefer?, Builtins.strCmpTwin?, Builtins.num?]) rfl with ⟨msg, h⟩ | h
    · exact RunSpec.unsupported rfl (hs1.trans h)
    · rw [basic_initialize_run n1 s (by rw [hget])] at h
      apply RunSpec.step rfl (hs1.trans h)
      apply RunSpec.step rfl (show Interp.stepFn _ = .next
        (Interp.withCtl (defaultAllocated m k) (.value (.ref s))) by
          simp only [Interp.stepFn, Interp.withCtl, Interp.applyKont, n1, defaultAllocated, hk])
      exact stepSpec_defaultAllocated hm hc hn hk hj

/-- Both the declared prefix and root table are checked; root dispatch comes from RootInitOk. -/
theorem declared_default_new {κ : Ctx} {Γ : Env} {I J : Ty} {m : Machine} {c : Cls} {k : ObjId}
    (hm : StateOk κ Γ I m) (hc : c ∈ κ.classes) (hn : classNamed? m.heap c.name = some k)
    (halloc : c.name ∈ κ.pos.plainAlloc) (hnew : smroGet? κ.classes c.name "new" = none)
    (hprefix : noDeclaredSelectorB κ.classes c.name "initialize" = true)
    (hroot : rootInitFreeB κ.defs = true) (hk : m.kont = []) (hj : nilFieldsB J = true) :
    StepSpec m Γ (.inst c.name J) (Interp.finishSend m (.ref k) .explicit "new" [] .none) κ I := by
  obtain ⟨j, hjn, hp⟩ := hm.allocators c.name halloc
  have he : j = k := Option.some.inj (hjn.symm.trans hn)
  subst j
  have hkind := hm.ordinary_decl hc halloc
  have hd := (hm.declCls c hc k hn).2.2.2.2.1 hkind hnew
  obtain ⟨owner, md, hl⟩ := hd.2
  obtain ⟨hb, hu, hv, _, _⟩ := hd.1 owner md hl
  have hinit : initDispatchB m.heap k = true := by
    unfold initDispatchB
    rw [hm.methodOn_root_of_absent hc hn hkind hprefix]
    exact hm.rootInit hroot
  rw [finishSend_new hp]
  rcases invokeDispatch_classNew (site := .explicit) (args := [])
    (by rw [lookup_eq_methodOn]; exact hl) hb hu hv with ⟨msg, h⟩ | h
  · rw [h]; trivial
  · rw [h, callConstruct_plain hp]
    exact default_new_run hm hp hn hk hj hinit

theorem SemSafeCtxA.newDefault {κ κ₁ κ₂ : Ctx} {Γ Γ₁ Γ₂ : Env} {I I₁ I₂ J : Ty}
    {c : Cls} {recv : Ratchet.Expr} {args : List Ratchet.Expr}
    (hr : SemSafeCtxA κ Γ I recv (.clsOf c.name) κ₁ Γ₁ I₁)
    (ha : SemAllCtxA κ₁ Γ₁ I₁ args [] κ₂ Γ₂ I₂)
    (hs : explicitReceiverB recv = true) (hc : c ∈ κ₂.classes)
    (hnew : smroGet? κ₂.classes c.name "new" = none) (halloc : c.name ∈ κ₂.pos.plainAlloc)
    (hprefix : noDeclaredSelectorB κ₂.classes c.name "initialize" = true)
    (hroot : rootInitFreeB κ₂.defs = true) (hj : nilFieldsB J = true) :
    SemSafeCtxA κ Γ I (.send (some recv) "new" args none) (.inst c.name J) κ₂ Γ₂ I₂ := by
  apply hr.sendVia ha (explicitReceiverB_sound hs) rfl (by simp)
  intro m hm hk recv hv args hargs
  have he : args = [] := by simpa using denAll_length hargs
  subst args
  obtain ⟨k, hn, _⟩ := hm.classes c hc
  have he : recv = .ref k := by cases recv <;> simp_all [denM, isClassRefNamed]
  rw [he]
  exact declared_default_new hm hc hn halloc hnew hprefix hroot hk hj

#print axioms callConstruct_plain
#print axioms default_new_run
#print axioms SemSafeCtxA.newDefault
end Ratchet.Denote.Typed
