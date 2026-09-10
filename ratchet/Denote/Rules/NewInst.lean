import Denote.Rules.ClassOf
import Denote.Rules.Lit

/-!
# `Denote/Rules/NewInst.lean` — `C.new` for a class with no `initialize`

`Judge.newInstNoInit` is the allocator: `C.new` where the context records no `initialize`, so
the object starts with no instance variables and its spine is `.ivar0`. It is the first rung
that **allocates through a class the program declared** rather than through a literal, and the
three things that makes different are worth naming.

**The dispatch cannot be a `ClsQueryOk` row.** `===` and `to_s` are clean at all 87 boot class
objects, which is what let clink 55 state them for *any* class object. `new` is not: 16 of the
87 do not resolve it to `Class#new` (14 modules, plus `Range` and `Struct`, whose `new` is
prelude Ruby). So the fact has to be keyed on the **context's own table** —
`DeclClassOk` (`../Sem/State.lean`), quantified over `κ.classes` and therefore vacuous at
`ctx0`, exactly as `ClassesOk` and `DefsOk` are.

**The rule was missing the allocator's own premise**, and this rung is what found it: a declared
`def self.new` wins over `Class#new` in CRuby, and `invoke`'s `userNew` check honours that, so
`smroGet? κ.classes n "new" = none` has to be *stated*. `validate` consulted `smroGet?` before
the allocator anyway, so no derivation on file changed — the same shape as §F6/§F7, a premise
the checker supplied by accident of control flow.

**`newImpl` has eleven arms and five of them allocate.** They are stated as one disjunction
(`run_new`): either the result is a fresh object with `k` as its class, no ivars, no eigenclass
and a non-class payload — which is exactly what `ext_push` asks for — or the builtin gated. The
uniformity is real rather than a convenience: `Exception`, `String`, `Array` and `Hash`
subclasses each start with *that* class's empty payload so a later `super` can fill it, and all
four keep `k` as `klass`, which is the only thing the conclusion reads.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## `Class#new` -/

theorem runObjects_new (m : Machine) (k : ObjId) (args : List Value) :
    Builtins.runObjects "Class#new" (.ref k) args m
      = Builtins.runModules "Class#new" (.ref k) args m := rfl

theorem runModules_new (m : Machine) (k : ObjId) (args : List Value) :
    Builtins.runModules "Class#new" (.ref k) args m = Builtins.newImpl m (.ref k) args := rfl

/-- **`Class#new` at a declared class, with no arguments: a fresh object of that class, or a
gate.** The five allocating arms differ only in the payload they start with, and the three
things `ext_push` reads — the class, the (empty) ivars, the (absent) eigenclass — are the same
in all five.

The three hypotheses are `DeclClassOk`'s: the receiver really is a non-module class, and it is
neither `Class` nor `Module`. Those last two are the arms that answer with a **class object**,
and an allocation that adds a class is not an `Ext`. -/
theorem run_new (m : Machine) {k : ObjId} {c : ClassPayload}
    (hcp : m.heap.classPayload? k = some c) (hmod : c.isModule = false)
    (hk : ¬ (k = Boot.classId)) (hkm : ¬ (k = Boot.moduleId)) :
    (∃ obj : Object, obj.klass = k ∧ obj.ivars = [] ∧ obj.eigen = none ∧
        (∀ cp, obj.payload ≠ .cls cp) ∧
        Builtins.run "Class#new" (.ref k) [] m
          = .ok (.ref m.heap.objs.size) { m with heap := pushHeap m.heap obj }) ∨
      (∃ r, Builtins.run "Class#new" (.ref k) [] m = .unsupported r) := by
  rw [Builtins.run.eq_def]
  dsimp only
  split
  · exact Or.inr ⟨_, rfl⟩
  split
  · rename_i hz; exact absurd hz (by simp)
  split
  · rename_i hd
    exact absurd hd (by simp [Builtins.dupBids, Builtins.cloneBids])
  rw [runObjects_new, runModules_new, Builtins.newImpl.eq_def]
  dsimp only
  rw [hcp]
  dsimp only
  -- **the arms, in `newImpl`'s own order.** `by_cases`/`if_neg` rather than `split`: the
  -- residual term still contains every later arm, and `split`'s internal `simp` runs out of
  -- steps on it (`Denote/Sem/notes.md` §Tactics — the same size problem `run_clsToS` hit from
  -- the other direction)
  rw [if_neg (by simp [hmod] : ¬ (c.isModule = true))]
  by_cases hexc : (ancestors m.heap k).contains Boot.exceptionId = true
  · rw [if_pos hexc]
    exact Or.inl ⟨{ klass := k, payload := .exc (className m.heap k) },
      rfl, rfl, rfl, by simp, rfl⟩
  rw [if_neg hexc]
  by_cases hstr : (ancestors m.heap k).contains Boot.stringId = true
  · rw [if_pos hstr]
    exact Or.inl ⟨{ klass := k, payload := .str "" }, rfl, rfl, rfl, by simp, rfl⟩
  rw [if_neg hstr]
  by_cases harr : (ancestors m.heap k).contains Boot.arrayId = true
  · rw [if_pos harr]
    exact Or.inl ⟨{ klass := k, payload := .arr #[] }, rfl, rfl, rfl, by simp, rfl⟩
  rw [if_neg harr]
  by_cases hhsh : (ancestors m.heap k).contains Boot.hashId = true
  · rw [if_pos hhsh]
    exact Or.inl ⟨{ klass := k, payload := .hsh #[] }, rfl, rfl, rfl, by simp, rfl⟩
  rw [if_neg hhsh]
  by_cases hrnd : (k == Boot.randomId) = true
  · rw [if_pos hrnd]; exact Or.inr ⟨_, rfl⟩
  rw [if_neg hrnd]
  by_cases hrx : (k == Boot.regexpId) = true
  · rw [if_pos hrx]; exact Or.inr ⟨_, rfl⟩
  rw [if_neg hrx]
  rw [if_neg (by simpa using hk : ¬ ((k == Boot.classId) = true))]
  rw [if_neg (by simpa using hkm : ¬ ((k == Boot.moduleId) = true))]
  by_cases him : ([Boot.integerId, Boot.floatId, Boot.symbolId, Boot.nilClassId,
      Boot.trueClassId, Boot.falseClassId].contains k) = true
  · rw [if_pos him]; exact Or.inr ⟨_, rfl⟩
  rw [if_neg him]
  by_cases hpc : ((ancestors m.heap k).any Builtins.payloadCoreClasses.contains) = true
  · rw [if_pos hpc]; exact Or.inr ⟨_, rfl⟩
  rw [if_neg hpc]
  -- a plain object: the default payload, no ivars, no eigenclass
  exact Or.inl ⟨{ klass := k }, rfl, rfl, rfl, by simp, rfl⟩

/-! ## `invoke` at `new`, which is the one name it does **not** simply pass through

`is_a?`/`===`/`to_s`/`class` all fall through to `invokeDispatch` (`../Sem/Query.lean`). `new`
is the interception: `invokeMaybeNew` allocates *and enters `initialize`* when the class has a
user one, which is a frame this rung cannot follow. `DeclClassOk`'s `noUserInit` clause is what
rules that out, and it is the rule's `ctorGet? = none` premise cashed at the heap. -/

theorem invoke_new {m : Machine} {k : ObjId} {c : ClassPayload} (site : SendSite)
    (args : List Value) (kw : List (Value × Value))
    (hcp : m.heap.classPayload? k = some c) (hmod : c.isModule = false)
    (hui : Interp.userInit? m.heap k = none) :
    Interp.invoke m (.ref k) site "new" args none kw
      = Interp.invoke.invokeDispatch m (.ref k) site "new" args none kw := by
  rw [Interp.invoke.eq_def]
  have hpay : (m.heap.get k).payload = .cls c := by
    simp only [Heap.classPayload?] at hcp
    cases hp : (m.heap.get k).payload with
    | cls c' =>
      rw [hp] at hcp
      simp only [Option.some.injEq] at hcp
      rw [hcp]
    | _ => rw [hp] at hcp; exact absurd hcp (by simp)
  simp only [hpay]
  -- **three arms, and all three reach `invokeDispatch` at `new`.** The two gates before
  -- `invokeMaybeNew` are `Regexp.escape`/`quote`/`union` and the `Math` functions, and `new`
  -- is none of the six names; inside `invokeMaybeNew`, a class with a `def self.new` declines
  -- the interception (that is CRuby's order) and a class with no user `initialize` falls
  -- through — so the only arm this rung has to *exclude* is the one `DeclClassOk` excludes.
  -- **four gates before `invokeMaybeNew`, and `new` is not one of their names.** The first
  -- two die on string literals (`send`/`public_send`/`__send__`, then
  -- `Regexp.escape`/`quote`/`union`); the `Math` arm survives as a `split` because the
  -- receiver could in principle *be* `Math`, and its own match on `("new", args)` falls to
  -- `invokeDispatch` anyway. Inside `invokeMaybeNew`, a class with a `def self.new` declines
  -- the interception (CRuby's order) and a class with no user `initialize` falls through — so
  -- the only arm this rung has to exclude is the one `DeclClassOk` excludes.
  split
  · rename_i h1; exact absurd h1 (by simp)
  split
  · rename_i h2; exact absurd h2 (by simp)
  split
  · rfl
  · rw [Interp.invoke.invokeMaybeNew.eq_def]
    -- the `userNew` binding is a `have`; `dsimp only` zeta-reduces it so the `if` is visible
    dsimp only
    -- the interception's own condition reads the eigenclass (a `def self.new` **declines** the
    -- interception, which is CRuby's order), so it is a nest of matches rather than one `if`;
    -- every leaf either is `invokeDispatch` already or is the `userInit?` match, which `hui`
    -- collapses
    repeat' split
    all_goals first
      | rfl
      | rw [hui]
      | simp_all

/-- The dispatch, given `DeclClassOk`'s `new` clause. Mirrors `invokeDispatch_clsToS`: the
builtin allocates, so the post-machine carries one more object. -/
theorem invokeDispatch_new {m : Machine} {k : ObjId} {c : ClassPayload} {site : SendSite}
    {owner : ObjId} {md : MethodDef}
    (hfound : Interp.methodOn m.heap (classOf m.heap (.ref k)) "new" = some (owner, md))
    (hb : md.builtin = some "Class#new") (hu : md.undefined = false)
    (hv : md.visibility = .pub) (hp : md.fromPrelude = false)
    (hsh : Interp.crubyShadow m.heap
      ((ancestors m.heap (classOf m.heap (.ref k))).takeWhile (fun x => x != owner)) "new"
      = none)
    (hcp : m.heap.classPayload? k = some c) (hmod : c.isModule = false)
    (hk : ¬ (k = Boot.classId)) (hkm : ¬ (k = Boot.moduleId)) :
    (∃ obj : Object, obj.klass = k ∧ obj.ivars = [] ∧ obj.eigen = none ∧
        (∀ cp, obj.payload ≠ .cls cp) ∧
        Interp.invoke.invokeDispatch m (.ref k) site "new" [] none []
          = .next (Interp.withCtl { m with heap := pushHeap m.heap obj }
              (.value (.ref m.heap.objs.size)))) ∨
      ∃ r, Interp.invoke.invokeDispatch m (.ref k) site "new" [] none [] = .unsupported r := by
  rw [Interp.invoke.invokeDispatch.eq_def, lookup_eq_methodOn, hfound]
  simp only [hu, hp, if_false, Bool.false_eq_true, hsh, visError?_pub hv, hb,
    show Builtins.deferTwin? m.heap "Class#new" (.ref k) [] = none from by
      simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
        Builtins.toAryDefer?, Builtins.coerceTwin?]]
  rcases run_new m hcp hmod hk hkm with ⟨obj, h1, h2, h3, h4, hr⟩ | ⟨r, hr⟩
  · exact Or.inl ⟨obj, h1, h2, h3, h4, by simp [appendKwHash_nil, hr]⟩
  · exact Or.inr ⟨r, by simp [appendKwHash_nil, hr]⟩

theorem dispatchMiss_new_no_value (m : Machine) (recv : Value) (site : SendSite)
    (args : List Value)
    (hmm : ∀ o md, Interp.methodOn m.heap (classOf m.heap recv) "method_missing"
        = some (o, md) → md.builtin.isSome = true) :
    (∃ r, Interp.dispatchMiss m recv site "new" args none = .unsupported r) ∨
    (∃ cls msg, Interp.dispatchMiss m recv site "new" args none
      = .next (Interp.raiseErr m cls msg)) := by
  unfold Interp.dispatchMiss
  simp only [Interp.tryIterator, Interp.tryMixin, Interp.tryReflect]
  repeat' split
  all_goals (try (simp only [Interp.missNoMethod]))
  all_goals (try split)
  all_goals first
    | (right; exact ⟨_, _, rfl⟩)
    | (left; exact ⟨_, rfl⟩)
    | simp_all [Interp.missNoMethod]

theorem invokeDispatch_new_miss {m : Machine} {recv : Value} {site : SendSite}
    {args : List Value}
    (hnone : Interp.methodOn m.heap (classOf m.heap recv) "new" = none)
    (hmm : ∀ o md, Interp.methodOn m.heap (classOf m.heap recv) "method_missing"
        = some (o, md) → md.builtin.isSome = true) :
    (∃ r, Interp.invoke.invokeDispatch m recv site "new" args none [] = .unsupported r) ∨
    (∃ cls msg, Interp.invoke.invokeDispatch m recv site "new" args none []
      = .next (Interp.raiseErr m cls msg)) := by
  rw [Interp.invoke.invokeDispatch.eq_def, lookup_eq_methodOn, hnone]
  simp only [appendKwHash_nil]
  exact dispatchMiss_new_no_value m recv site args hmm


/-! ## The rung -/

theorem Sem.Judge.newInstNoInit : Obl.Judge.newInstNoInit := by
  intro κ Γ Γ₁ Γ₂ I I₁ I₂ recv n args c hrecv hargs hinst hctor hsmro
  refine ⟨trivial, ?_⟩
  intro m hm v m' hev
  obtain ⟨fuel, hrun⟩ := hev
  rcases fuel with _ | f
  · rw [run_zero] at hrun; exact absurd hrun (by simp)
  · rw [run_succ, stepFn_send_push] at hrun
    dsimp only at hrun
    obtain ⟨nb, v₀, m₀, hin, hc₀, hk₀, hout⟩ :=
      run_split _ (catchFree_recvK "new" (toRubyList args) .none _)
        (jumpOpaque_recvK "new" (toRubyList args) .none _) f (evalFrom m recv) v m' hrun
    obtain ⟨hframe₁, hdenR, hok₁, -⟩ := hrecv.2 m hm v₀ m₀ ⟨nb, hin⟩
    obtain ⟨k, hcn, rfl, hkp⟩ := denM_clsOf_ref hdenR
    obtain ⟨f₂, hf₂⟩ := hout
    revert hf₂
    rcases f₂ with _ | f₃
    · intro hf₂; rw [run_zero] at hf₂; exact absurd hf₂ (by simp)
    · intro hf₂
      have hsr : StepRunsTo (Interp.stepFn
          (deliver m₀ (.ref k) [.recvK "new" (toRubyList args) .none
            (match toRuby recv with | .self' => .selfRecv | _ => .explicit)])) v m' := by
        refine stepRunsTo_of_run ?_ hf₂
        exact RubyCore.Proof.applyKont_notDone
          (deliver m₀ (.ref k) [.recvK "new" (toRubyList args) .none
            (match toRuby recv with | .self' => .selfRecv | _ => .explicit)]) (.ref k)
          (by simp [deliver])
      rw [stepFn_recvK] at hsr
      have hm₀ : ({ m₀ with ctl := .value (.ref k), kont := [] } : Machine) = m₀ := by
        rw [← hc₀, ← hk₀]
      rw [hm₀] at hsr
      obtain ⟨vs, m₁, hallEv, hk₁, hfin⟩ :=
        run_args _ "new" (.ref k) .none args [] m₀ v m' hk₀ hargs.1 hsr
      obtain ⟨hframe₂, hden, hok₂⟩ := hargs.2 m₀ hok₁ vs m₁ hallEv
      rcases args with _ | ⟨a, arest⟩
      · rcases vs with _ | ⟨av, vrest⟩
        · have hma : m₁ = m₀ := hden
          subst hma
          -- **the four facts about the receiver's class object**, all from `DeclClassOk` at
          -- the class the context declares
          have hmem : c ∈ κ.classes ∧ c.name = n := by
            -- `instClsGet?` is `clsGet?` (a `find?`) plus the module refusal, so both facts
            -- come out of `List.find?`'s two properties
            simp only [Ratchet.instClsGet?] at hinst
            cases hcg : Ratchet.clsGet? κ.classes n with
            | none => rw [hcg] at hinst; exact absurd hinst (by simp)
            | some c' =>
              rw [hcg] at hinst
              dsimp only at hinst
              by_cases hm2 : c'.isModule = true
              · rw [if_pos hm2] at hinst; exact absurd hinst (by simp)
              · rw [if_neg hm2] at hinst
                have hcc : c' = c := by simpa using hinst
                subst hcc
                simp only [Ratchet.clsGet?] at hcg
                exact ⟨List.mem_of_find?_eq_some hcg, by simpa using List.find?_some hcg⟩
          obtain ⟨hclsmem, hname⟩ := hmem
          obtain ⟨hroot, hkc, hkm, hism, hnewOk, hnoInit, _⟩ :=
            hok₂.declCls c hclsmem k (by rw [hname]; exact hcn)
          have hcp : ∃ cp, m₁.heap.classPayload? k = some cp ∧ cp.isModule = false := by
            cases hp : m₁.heap.classPayload? k with
            | none => rw [hp] at hism; exact absurd hism (by simp)
            | some cp => exact ⟨cp, rfl, by rw [hp] at hism; simpa using hism⟩
          obtain ⟨cp, hcpk, hcpmod⟩ := hcp
          have hui : Interp.userInit? m₁.heap k = none := hnoInit (by rw [hname]; exact hctor)
          obtain ⟨hnew1, hnew2⟩ := hnewOk (by rw [hname]; exact hsmro)
          -- **the dispatch**
          simp only [List.nil_append] at hfin
          obtain ⟨m₂, hstep, f₄, hf₄⟩ := hfin
          rw [show Interp.finishSend m₁ (.ref k) _ "new" [] .none
                = Interp.invoke m₁ (.ref k) _ "new" [] none [] from rfl,
             invoke_new _ [] [] hcpk hcpmod hui] at hstep
          cases hlk : Interp.methodOn m₁.heap (RubyCore.classOf m₁.heap (.ref k)) "new" with
          | some p =>
            obtain ⟨owner, md⟩ := p
            obtain ⟨hb, hu, hv, hp, hsh⟩ := hnew1 owner md hlk
            rcases invokeDispatch_new hlk hb hu hv hp hsh hcpk hcpmod hkc hkm with
              ⟨obj, hoc, hoi, hoe, hop, hd⟩ | ⟨r, hd⟩
            · rw [hd] at hstep
              cases hstep
              -- **the allocation is an `Ext`**, and the fresh object is an instance of `k`
              have hext : Ext m₁ (reCtl { m₁ with heap := pushHeap m₁.heap obj }
                  (.value (.ref m₁.heap.objs.size)) []) :=
                (ext_push (m := m₁) obj hok₂.sat hok₂.core.basicSelf hop hoi hoe
                  (by rw [hoc]; exact hroot)).trans (Ext_toReCtl _ _ _)
              have hwc : Interp.withCtl { m₁ with heap := pushHeap m₁.heap obj }
                  (Ctl.value (.ref m₁.heap.objs.size))
                  = reCtl { m₁ with heap := pushHeap m₁.heap obj }
                    (.value (.ref m₁.heap.objs.size)) [] := by
                rw [Interp.withCtl, reCtl, hk₁]
              revert hf₄
              rcases f₄ with _ | f₅
              · intro hf₄; rw [run_zero] at hf₄; exact absurd hf₄ (by simp)
              · intro hf₄
                rw [run_succ, hwc, stepFn_value_nil] at hf₄
                dsimp only at hf₄
                cases hf₄
                refine ⟨hframe₁.trans (Framed.of_ext hext), ?_, ⟨StateOk_ext hok₂ hext, StateOk_ext hok₂ hext⟩⟩
                -- `.inst n .ivar0`: exactly `k`'s instance, live, and with no ivars at all
                rw [denM]
                refine ⟨?_, by rw [denSpineFrom]; trivial⟩
                unfold isExactInst
                rw [show (reCtl { m₁ with heap := pushHeap m₁.heap obj }
                      (Ctl.value (Value.ref m₁.heap.objs.size)) []).heap
                    = pushHeap m₁.heap obj from rfl, hext.classNamed?_eq, hcn]
                simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
                  Option.isNone_iff_eq_none]
                refine ⟨⟨by simp, by rw [pushHeap_get_self]; exact hoe⟩, ?_⟩
                rw [pushHeap_get_self, hoc]
            · rw [hd] at hstep; exact absurd hstep (by simp)
          | none =>
            rcases invokeDispatch_new_miss hlk (hnew2 hlk) with ⟨r, hd⟩ | ⟨cls, msg, hd⟩
            · rw [hd] at hstep; exact absurd hstep (by simp)
            · rw [hd] at hstep
              cases hstep
              exact absurd hf₄ (jump_empty_never_value f₄ _ v m'
                ⟨_, raiseErr_ctl _ _ _⟩ (by rw [raiseErr_kont, hk₁]))
        · exact absurd hden (by simp [DenAllAt])
      · exact absurd hden (by cases vs <;> simp [DenAllAt])

#print axioms Sem.Judge.newInstNoInit

#print axioms invoke_new
#print axioms invokeDispatch_new
#print axioms invokeDispatch_new_miss
#print axioms run_new

end Ratchet.Denote
