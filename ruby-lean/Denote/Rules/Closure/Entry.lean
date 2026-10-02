import Denote.Rules.Method.MethodEntry
import Denote.Sem.Closure.Capture

/-! Required-positional lambda entry against the real call engine. Parameters shadow
explicit block locals, which shadow the captured chain. Proc padding and auto-splatting
are different contracts and are not assumed here. -/
set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

theorem classifySimple_required (names : List String) :
    Interp.classifySimple (names.map RubyCore.Param.req) =
      some ⟨names, none, [], none, []⟩ := by
  unfold Interp.classifySimple
  simp [List.any_map, classifyFull_required]

private theorem values_in_order (args : List Value) :
    (List.range args.length).map (fun i => args[i]?.getD .nil) = args := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp [h₂]

/-- All metadata copied by callClosure, including its optional scope overrides. -/
def requiredClosureFrame (m : Machine) (cl : Closure) (names : List String)
    (args : List Value) (selfOv : Option Value := none)
    (defmodOv : Option ObjId := none) : RubyCore.Frame :=
  let cap := m.frames.getD (cl.captured.getD 0) default
  { self := selfOv.getD cap.self, defmod := defmodOv.getD cap.defmod,
    definitionFrame := if defmodOv.isSome then none else
      some (m.definitionFrameId (cl.captured.getD 0)),
    blk := cap.blk,
    locals := names.zip args ++ cl.locals.map (fun x => (x, Value.nil)),
    kind := .block, captured := cl.captured, home := cl.home, lam := cl.lam,
    cref := cap.cref, libraryOrigin := cl.libraryOrigin }

/-- The break target callClosure actually installs: a literal's own scope while live. -/
def closureBrk (m : Machine) (cl : Closure) (brk : Option FrameId) : Option FrameId :=
  match cl.breakScope with
  | none => brk
  | some scope => if m.liveBreakScopes.contains scope then some scope else none

theorem CaptureLive.pushFrame {m : Machine} {cap : Option FrameId}
    (h : CaptureLive m cap) (f : RubyCore.Frame) : CaptureLive (pushMethodFrame m f) cap :=
  h.frames_preserved (by simp [pushMethodFrame]) (by
    intro i hi
    simp [pushMethodFrame, Array.getD, hi, Nat.lt_succ_of_lt hi, Array.getElem_push_lt])

theorem requiredClosureFrame_slots (m : Machine) (cl : Closure)
    (names : List String) (args : List Value) (ha : args.length = names.length) (x : String) :
    (requiredClosureFrame m cl names args).locals.any (·.1 == x) =
      (names ++ cl.locals).contains x := by
  have hz : (names.zip args).any (·.1 == x) = names.contains x := by
    induction names generalizing args with
    | nil => cases args with
      | nil => rfl
      | cons _ _ => cases ha
    | cons name names ih => cases args with
      | nil => cases ha
      | cons v vs =>
        have hlen : vs.length = names.length := Nat.succ.inj ha
        change (name == x || (names.zip vs).any (·.1 == x)) = (x == name || names.contains x)
        rw [ih vs hlen, show (name == x) = (x == name) from BEq.comm]
  simp only [requiredClosureFrame, List.any_append, hz, List.any_map,
    List.contains_append, Function.comp_def]
  congr 1
  rw [List.contains_eq_any_beq]
  simp only [BEq.comm]

/-- At exact required arity, Proc padding/truncation and auto-splatting leave the
argument vector unchanged. This is the Proc arity Sorbet accepts (clink 222). -/
theorem callClosure_required (m : Machine) (cl : Closure)
    (names : List String) (args : List Value) (brk : Option FrameId)
    (selfOv : Option Value) (defmodOv : Option ObjId)
    (hp : cl.params = names.map RubyCore.Param.req)
    (ha : args.length = names.length)
    (henum : cl.enumYield = none) (hfor : cl.forTargets = none) :
    Interp.callClosure m cl args brk selfOv defmodOv =
      .next (Interp.withKont
        (pushMethodFrame m (requiredClosureFrame m cl names args selfOv defmodOv))
        (.eval cl.body) (.blkFrameK m.frames.size cl.lam (closureBrk m cl brk) cl args)) := by
  have hauto : ¬ ((cl.lam = false ∧ args.length = 1) ∧ 2 ≤ args.length) := by
    intro h
    omega
  have hft : ∀ l : List (String × Value), l.filter (fun _ => true) = l := fun l => by
    induction l <;> simp_all [List.filter]
  unfold Interp.callClosure Interp.enterClosure
  rw [henum, hfor, hp, classifySimple_required]
  simp [hauto, ← ha, values_in_order, requiredClosureFrame, pushMethodFrame,
    Interp.withKont, Interp.queueParamBindings, Interp.withCtl, hft]
  cases h : cl.breakScope <;> simp [closureBrk, h]

theorem callClosure_required_lambda (m : Machine) (cl : Closure)
    (names : List String) (args : List Value) (brk : Option FrameId)
    (selfOv : Option Value) (defmodOv : Option ObjId)
    (hp : cl.params = names.map RubyCore.Param.req) (hl : cl.lam = true)
    (ha : args.length = names.length)
    (henum : cl.enumYield = none) (hfor : cl.forTargets = none) :
    Interp.callClosure m cl args brk selfOv defmodOv =
      .next (Interp.withKont
        (pushMethodFrame m (requiredClosureFrame m cl names args selfOv defmodOv))
        (.eval cl.body) (.blkFrameK m.frames.size true (closureBrk m cl brk) cl args)) := by
  simpa only [hl] using callClosure_required m cl names args brk selfOv defmodOv hp ha henum hfor

/-- Entering the body consumes the extra lookup fuel contributed by the new frame.
Unbound names therefore read the live capture at exactly its original fuel. -/
theorem requiredClosureFrame_getLocal (m : Machine) (cl : Closure)
    (names : List String) (args : List Value) (selfOv : Option Value)
    (defmodOv : Option ObjId) (hcap : CaptureLive m cl.captured) (x : String) :
    (pushMethodFrame m (requiredClosureFrame m cl names args selfOv defmodOv)).getLocal x =
      match (names.zip args ++ cl.locals.map (fun n => (n, Value.nil))).find? (·.1 == x) with
      | some (_, v) => v
      | none => closLocal m cl x := by
  let f := requiredClosureFrame m cl names args selfOv defmodOv
  have hframes (i : FrameId) (hi : i < m.frames.size) :
      (pushMethodFrame m f).frames.getD i default = m.frames.getD i default := by
    simp [pushMethodFrame, Array.getD, hi, Nat.lt_succ_of_lt hi, Array.getElem_push_lt]
  change Machine.getLocal.go (pushMethodFrame m f) x m.frames.size
    ((m.frames.push f).size + 1) = _
  rw [Array.size_push]
  rw [Machine.getLocal.go]
  have hhead : (pushMethodFrame m f).frames.getD m.frames.size default = f := by
    simp [pushMethodFrame, Array.getD_eq_getD_getElem?]
  have hla : (pushMethodFrame m f).localFrameId m.frames.size = m.frames.size :=
    localFrameId_of_noAlias (by rw [hhead]; rfl)
  rw [hla, hhead]
  change (match f.locals.find? (·.1 == x) with
    | some (_, v) => v
    | none => match cl.captured with
      | some p => Machine.getLocal.go (pushMethodFrame m f) x p (m.frames.size + 1)
      | none => .nil) = match f.locals.find? (·.1 == x) with
        | some (_, v) => v
        | none => closLocal m cl x
  cases hb : f.locals.find? (·.1 == x) with
  | some p => rfl
  | none =>
    change (match cl.captured with
      | some p => Machine.getLocal.go (pushMethodFrame m f) x p (m.frames.size + 1)
      | none => .nil) = closLocal m cl x
    cases hp : cl.captured with
    | none => simp [closLocal, frameLocal?, hp]
    | some p =>
      simp only [closLocal, hp, frameLocal?, frameLocal]
      exact (getLocal_go_eq_frameLocal_go _ x _ p (hp ▸ CaptureLive.pushFrame hcap f)).trans
        (frameLocal_go_preserved hframes x _ p (hp ▸ hcap))

#print axioms callClosure_required_lambda
#print axioms callClosure_required
#print axioms requiredClosureFrame_getLocal
end Ratchet.Denote.Typed
