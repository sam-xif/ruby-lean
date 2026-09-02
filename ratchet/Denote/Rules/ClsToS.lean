import Denote.Rules.CaseEq
import Denote.Rules.Lit

/-!
# `Denote/Rules/ClsToS.lean` — `C.to_s`, and the first builtin that allocates

`Judge.clsToS` is `Module#to_s`: a class object's name, as a String. It is `caseEqQuery`'s
recipe (`Denote/Rules/CaseEq.lean`) with one thing added and one taken away.

Added: the builtin **allocates**. The two query rungs answer a `Bool`, an immediate, so their
post-machine was their pre-machine; here the answer is a fresh String object, so all three
conjuncts have to move across a heap push. That transport already exists — it is what
`Denote/Rules/Lit.lean`'s string literal does — so the cost is one `Ext` and the three lines
that read the fresh object's class off it, lifted from `strLit`.

Taken away: the argument list is empty, so there is no argument walk at all — but the
receiver's class-ness still has to reach the dispatch, because `run_args` threads the machine
through even for `[]`. The `Framed` transport (`../Sem/Judge.lean`) is used the same way.

The rule's guard needed §F7's fix for exactly the reason `caseEqQuery`'s did: `smroGet?
κ.classes n "to_s" = none` asks about singleton methods on `n` itself, while the dispatch walks
the eigenclass chain, so a `def self.to_s` on a superclass — or a `class Module; def to_s` —
gets past it. Both now excluded by `nameFree κ "to_s"`.
-/

set_option autoImplicit false

namespace Ratchet.Denote

open RubyCore

/-! ## `C.to_s` — the same chain, and the first rung whose builtin *allocates*

`Module#to_s` is the class's name, and it answers it as a **fresh String object**. So unlike
the two query rungs the post-machine is not the pre-machine, and the rung's three conjuncts all
have to move across a heap push — which is exactly what `Denote/Rules/Lit.lean`'s string literal
already does (`ext_push`), so the extra cost is one `Ext` rather than a new transport. -/

/-- The result of `Module#to_s`, in the shape `ext_push` wants: `allocStr` is a `pushHeap` of
`Lit.lean`'s `strObj`, and the value is the fresh id. Which *string* it is does not matter to
the rung — `Ty.cls "String"` says the answer is a String, not which one — so it is
existential. -/
theorem okStr_eq (m : Machine) (s : String) :
    Builtins.okStr m s = .ok (.ref m.heap.objs.size) { m with heap := pushHeap m.heap (strObj s) } :=
  rfl

theorem invokeMaybeNew_clsToS (m : Machine) (recv : Value) (o : ObjId) (c : ClassPayload)
    (site : SendSite) (args : List Value) (blk : Option Value) (kw : List (Value × Value)) :
    Interp.invoke.invokeMaybeNew m recv o c site "to_s" args blk kw
      = Interp.invoke.invokeDispatch m recv site "to_s" args blk kw := by
  rw [Interp.invoke.invokeMaybeNew.eq_def, if_neg (by simp)]

theorem invoke_clsToS (m : Machine) (recv : Value) (site : SendSite) (args : List Value)
    (blk : Option Value) (kw : List (Value × Value)) :
    Interp.invoke m recv site "to_s" args blk kw
      = Interp.invoke.invokeDispatch m recv site "to_s" args blk kw := by
  rw [Interp.invoke.eq_def]
  cases recv with
  | ref o =>
    cases hp : (m.heap.get o).payload <;> simp only [hp] <;>
      first
        | rfl
        | (split <;> simp_all [invokeMaybeNew_clsToS])
        | simp_all [invokeMaybeNew_clsToS]
  | _ => rfl

/-- **`Module#to_s` is not one of the deferring bids.** Worth stating rather than assuming:
`reprDefer?` *does* list four `to_s` bids (`Object#to_s`, `Array#to_s`, `Hash#to_s`,
`Range#to_s`), each of which hands off to prelude Ruby when the receiver is impure. A class
object's `to_s` renders its own name and reads nothing else, so it is not among them — and if
it were, this rung would be typing a user method's body instead of a builtin. -/
theorem deferTwin?_clsToS (h : Heap) (recv : Value) (args : List Value) :
    Builtins.deferTwin? h "Module#to_s" recv args = none := by
  simp [Builtins.deferTwin?, Builtins.reprDefer?, Builtins.coerceDefer?,
    Builtins.toAryDefer?, Builtins.coerceTwin?]
  rcases args with _ | ⟨a, rest⟩
  · rfl
  · cases rest <;> rfl

/-- **The bid chain at a literal, in one `rfl`.** `Builtins.run` hands an unrecognised bid down
five files (`runObjects` → `runNumerics` → `runStrings` → `runCollections` → `runModules`), and
at a literal bid every one of those matches reduces — so the whole descent is a definitional
step and the kernel does it without any tactic help. Stating it separately is what keeps
`run_clsToS` off the `simp only` chain that `run_caseEq` needed: those matches are large, and
`simp only`'s literal-string `isDefEq` work over them is what times out. -/
theorem runObjects_toS (m : Machine) (k : ObjId) (args : List Value) :
    Builtins.runObjects "Module#to_s" (.ref k) args m
      = Builtins.runModules "Module#to_s" (.ref k) args m := rfl

/-- `Module#to_s`'s own arm, reduced: it shares a match arm with `Module#name` and
`Module#inspect`, and the `bid == "Module#name"` test inside it is what the literal settles. -/
theorem runModules_toS (m : Machine) (k : ObjId) (args : List Value) :
    Builtins.runModules "Module#to_s" (.ref k) args m
      = (match m.heap.classPayload? k with
         | some c =>
           if c.name.isEmpty then
             (match Builtins.inspectP m (.ref k) with
              | .ok r => Builtins.okStr m r
              | .error e => .unsupported e)
           else Builtins.okStr m c.name
         | none => .unsupported "name") := rfl

/-- **`Module#to_s` at a class receiver allocates a String** — which one is existential (the
class's own name, or `inspect`'s address form for an anonymous class), and the `unsupported`
alternative covers both `Builtins.run`'s byte-string gate and `inspectP` declining. -/
theorem run_clsToS (m : Machine) {k : ObjId}
    (hk : (m.heap.classPayload? k).isSome = true) :
    (∃ s, Builtins.run "Module#to_s" (.ref k) [] m
        = .ok (.ref m.heap.objs.size) { m with heap := pushHeap m.heap (strObj s) }) ∨
      ∃ r, Builtins.run "Module#to_s" (.ref k) [] m = .unsupported r := by
  -- `Builtins.run`'s prologue asks three questions before any bid is looked at: the
  -- byte-string safety net, a zero-argument arity gate, and the class-generic `dup`/`clone`
  -- rule. Only the first can fire here, and it is the `unsupported` alternative.
  rw [Builtins.run.eq_def]
  dsimp only
  split
  · exact Or.inr ⟨_, rfl⟩
  split
  · rename_i hz; exact absurd hz (by simp)
  split
  · rename_i hd
    exact absurd hd (by simp [Builtins.dupBids, Builtins.cloneBids])
  rw [runObjects_toS, runModules_toS]
  -- the receiver *is* a class, so the payload match takes the `some` arm; then it is the
  -- anonymous/named split, and `inspectP` on the anonymous side
  split
  · rename_i c hcp
    split
    · -- anonymous (`Class.new`): `to_s` is `inspect`'s address form
      cases hi : Builtins.inspectP m (Value.ref k) with
      | ok r => exact Or.inl ⟨r, okStr_eq m r⟩
      | error e => exact Or.inr ⟨e, rfl⟩
    · exact Or.inl ⟨_, okStr_eq m _⟩
  · -- the receiver *is* a class, so the payload match cannot miss
    rename_i hcp
    exact absurd hcp (by rw [Option.isSome_iff_ne_none] at hk; exact hk)

theorem invokeDispatch_clsToS {m : Machine} {site : SendSite} {k : ObjId}
    {owner : ObjId} {md : MethodDef}
    (hfound : Interp.methodOn m.heap (classOf m.heap (.ref k)) "to_s" = some (owner, md))
    (hb : md.builtin = some "Module#to_s") (hu : md.undefined = false)
    (hv : md.visibility = .pub) (hp : md.fromPrelude = false)
    (hsh : Interp.crubyShadow m.heap
      ((ancestors m.heap (classOf m.heap (.ref k))).takeWhile (fun x => x != owner)) "to_s"
      = none)
    (hk : (m.heap.classPayload? k).isSome = true) :
    (∃ s, Interp.invoke.invokeDispatch m (.ref k) site "to_s" [] none []
        = .next (Interp.withCtl { m with heap := pushHeap m.heap (strObj s) }
            (.value (.ref m.heap.objs.size)))) ∨
      ∃ r, Interp.invoke.invokeDispatch m (.ref k) site "to_s" [] none []
        = .unsupported r := by
  rw [Interp.invoke.invokeDispatch.eq_def, lookup_eq_methodOn, hfound]
  simp only [hu, hp, if_false, Bool.false_eq_true, hsh, visError?_pub hv, hb,
    deferTwin?_clsToS]
  rcases run_clsToS m hk with ⟨s, hr⟩ | ⟨r, hr⟩
  · exact Or.inl ⟨s, by simp [appendKwHash_nil, hr]⟩
  · exact Or.inr ⟨r, by simp [appendKwHash_nil, hr]⟩

theorem dispatchMiss_clsToS_no_value (m : Machine) (recv : Value) (site : SendSite)
    (args : List Value)
    (hmm : ∀ o md, Interp.methodOn m.heap (classOf m.heap recv) "method_missing"
        = some (o, md) → md.builtin.isSome = true) :
    (∃ r, Interp.dispatchMiss m recv site "to_s" args none = .unsupported r) ∨
    (∃ cls msg, Interp.dispatchMiss m recv site "to_s" args none
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

theorem invokeDispatch_clsToS_miss {m : Machine} {recv : Value} {site : SendSite}
    {args : List Value}
    (hnone : Interp.methodOn m.heap (classOf m.heap recv) "to_s" = none)
    (hmm : ∀ o md, Interp.methodOn m.heap (classOf m.heap recv) "method_missing"
        = some (o, md) → md.builtin.isSome = true) :
    (∃ r, Interp.invoke.invokeDispatch m recv site "to_s" args none [] = .unsupported r) ∨
    (∃ cls msg, Interp.invoke.invokeDispatch m recv site "to_s" args none []
      = .next (Interp.raiseErr m cls msg)) := by
  rw [Interp.invoke.invokeDispatch.eq_def, lookup_eq_methodOn, hnone]
  simp only [appendKwHash_nil]
  exact dispatchMiss_clsToS_no_value m recv site args hmm

#print axioms invoke_clsToS
#print axioms run_clsToS
#print axioms invokeDispatch_clsToS
#print axioms invokeDispatch_clsToS_miss


/-! ## The rung -/

theorem Sem.Judge.clsToS : Obl.Judge.clsToS := by
  intro κ Γ Γ₁ Γ₂ I I₁ I₂ recv args n hrecv hargs _hsmro hts _hmmfree
  refine ⟨trivial, ?_⟩
  intro m hm v m' hev
  obtain ⟨fuel, hrun⟩ := hev
  rcases fuel with _ | f
  · rw [run_zero] at hrun; exact absurd hrun (by simp)
  · -- **the receiver link**
    rw [run_succ, stepFn_send_push] at hrun
    dsimp only at hrun
    obtain ⟨nb, v₀, m₀, hin, hc₀, hk₀, hout⟩ :=
      run_split _ (catchFree_recvK "to_s" (toRubyList args) .none _)
        (jumpOpaque_recvK "to_s" (toRubyList args) .none _) f (evalFrom m recv) v m' hrun
    obtain ⟨hframe₁, hdenR, hok₁⟩ := hrecv.2 m hm v₀ m₀ ⟨nb, hin⟩
    obtain ⟨k, _, rfl, hk⟩ := denM_clsOf_ref hdenR
    obtain ⟨f₂, hf₂⟩ := hout
    revert hf₂
    rcases f₂ with _ | f₃
    · intro hf₂; rw [run_zero] at hf₂; exact absurd hf₂ (by simp)
    · intro hf₂
      have hsr : StepRunsTo (Interp.stepFn
          (deliver m₀ (.ref k) [.recvK "to_s" (toRubyList args) .none
            (match toRuby recv with | .self' => .selfRecv | _ => .explicit)])) v m' := by
        refine stepRunsTo_of_run ?_ hf₂
        exact RubyCore.Proof.applyKont_notDone
          (deliver m₀ (.ref k) [.recvK "to_s" (toRubyList args) .none
            (match toRuby recv with | .self' => .selfRecv | _ => .explicit)]) (.ref k)
          (by simp [deliver])
      rw [stepFn_recvK] at hsr
      have hm₀ : ({ m₀ with ctl := .value (.ref k), kont := [] } : Machine) = m₀ := by
        rw [← hc₀, ← hk₀]
      rw [hm₀] at hsr
      obtain ⟨vs, m₁, hallEv, hk₁, hfin⟩ :=
        run_args _ "to_s" (.ref k) .none args [] m₀ v m' hk₀ hargs.1 hsr
      obtain ⟨hframe₂, hden, hok₂⟩ := hargs.2 m₀ hok₁ vs m₁ hallEv
      -- **no arguments**, so the argument walk ends where it started
      rcases args with _ | ⟨a, arest⟩
      · rcases vs with _ | ⟨av, vrest⟩
        · have hma : m₁ = m₀ := hden
          subst hma
          have hka : (m₁.heap.classPayload? k).isSome = true := hframe₂.cls k hk
          simp only [List.nil_append] at hfin
          obtain ⟨m₂, hstep, f₄, hf₄⟩ := hfin
          rw [show Interp.finishSend m₁ (.ref k) _ "to_s" [] .none
                = Interp.invoke m₁ (.ref k) _ "to_s" [] none [] from rfl,
             invoke_clsToS] at hstep
          cases hlk : Interp.methodOn m₁.heap (classOf m₁.heap (.ref k)) "to_s" with
          | some p =>
            obtain ⟨owner, md⟩ := p
            obtain ⟨hq1, _⟩ := hok₂.clsQuery "to_s" "Module#to_s" (by simp [clsQueryBuiltins])
              hts k hka
            obtain ⟨hb, hu, hv, hp, hsh⟩ := hq1 owner md hlk
            rcases invokeDispatch_clsToS hlk hb hu hv hp hsh hka with ⟨str, hd⟩ | ⟨r, hd⟩
            · rw [hd] at hstep
              cases hstep
              -- **the push is an `Ext`** — `strLit`'s, at `m₁` instead of at `m`
              have hext : Ext m₁ (reCtl { m₁ with heap := pushHeap m₁.heap (strObj str) }
                  (.value (.ref m₁.heap.objs.size)) []) :=
                (ext_push (m := m₁) (strObj str) hok₂.sat hok₂.core.basicSelf
                  (fun c => by simp [strObj]) rfl rfl
                  (by simpa [strObj] using hok₂.core.stringBasic)).trans (Ext_toReCtl _ _ _)
              have hwc : Interp.withCtl { m₁ with heap := pushHeap m₁.heap (strObj str) }
                  (Ctl.value (.ref m₁.heap.objs.size))
                  = reCtl { m₁ with heap := pushHeap m₁.heap (strObj str) }
                    (.value (.ref m₁.heap.objs.size)) [] := by
                rw [Interp.withCtl, reCtl, hk₁]
              revert hf₄
              rcases f₄ with _ | f₅
              · intro hf₄; rw [run_zero] at hf₄; exact absurd hf₄ (by simp)
              · intro hf₄
                rw [run_succ, hwc, stepFn_value_nil] at hf₄
                dsimp only at hf₄
                cases hf₄
                refine ⟨hframe₁.trans (Framed.of_ext hext), ?_, StateOk_ext hok₂ hext⟩
                -- `.ref size` is a `String`, by `strLit`'s three lines at `m₁`
                have hanc : ∀ j, ancestors (pushHeap m₁.heap (strObj str)) j
                    = ancestors m₁.heap j :=
                  Proof.ancestors_congr_grow hext.shapeAgree hext.size hok₂.sat
                have hcls : classOf (pushHeap m₁.heap (strObj str))
                    (.ref m₁.heap.objs.size) = Boot.stringId := by
                  simp [classOf, pushHeap_get_self, strObj]
                rw [denM, isAName, hext.classNamed?_eq, hok₂.core.stringNamed]
                show (ancestors (pushHeap m₁.heap (strObj str)) _).contains _ = true
                rw [hcls, hanc]
                exact hok₂.core.stringSelf
            · rw [hd] at hstep; exact absurd hstep (by simp)
          | none =>
            obtain ⟨_, hq2⟩ := hok₂.clsQuery "to_s" "Module#to_s" (by simp [clsQueryBuiltins])
              hts k hka
            rcases invokeDispatch_clsToS_miss hlk (hq2 hlk) with ⟨r, hd⟩ | ⟨cls, msg, hd⟩
            · rw [hd] at hstep; exact absurd hstep (by simp)
            · rw [hd] at hstep
              cases hstep
              exact absurd hf₄ (jump_empty_never_value f₄ _ v m'
                ⟨_, raiseErr_ctl _ _ _⟩ (by rw [raiseErr_kont, hk₁]))
        · exact absurd hden (by simp [DenAllAt])
      · exact absurd hden (by cases vs <;> simp [DenAllAt])

#print axioms Sem.Judge.clsToS

end Ratchet.Denote
