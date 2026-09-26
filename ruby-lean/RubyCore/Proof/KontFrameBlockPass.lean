import RubyCore.Proof.KontFrameSend

/-! L275: effectful block conversion preserves the continuation tail. -/

set_option autoImplicit false

namespace RubyCore.Proof
open Interp

@[simp, frameLem] theorem blockPassProc_frame (K : List Kont) (m : Machine) (v : Value) :
    blockPassProc (pushK K m) v = blockPassProc m v := rfl

@[simp, frameLem] theorem blockPassMethod_frame (K : List Kont) (m : Machine)
    (v : Value) (name : String) :
    blockPassMethod (pushK K m) v name = blockPassMethod m v name := rfl

@[simp, frameLem] theorem blockPassNoConversion_frame (K : List Kont) (m : Machine)
    (source : Value) :
    blockPassNoConversion (pushK K m) source = frameR K (blockPassNoConversion m source) := by
  simp only [blockPassNoConversion, frameLem]

@[simp, frameLem] theorem blockPassInvalid_frame (K : List Kont) (m : Machine)
    (source result : Value) :
    blockPassInvalid (pushK K m) source result = frameR K (blockPassInvalid m source result) := by
  simp only [blockPassInvalid, frameLem]

theorem blockPassMissing_frame (K : List Kont) (hK : CatchFree K) (m : Machine)
    (call : BlockPassCall) (source : Value) (respond respondMissing : Bool) :
    blockPassMissing (pushK K m) call source respond respondMissing =
      frameR K (blockPassMissing m call source respond respondMissing) := by
  simp only [blockPassMissing, frameLem]
  split
  · split
    · rfl
    · rw [invoke_frame K hK]
  · rfl

theorem blockPassChecked_frame (K : List Kont) (hK : CatchFree K) (m : Machine)
    (call : BlockPassCall) (source : Value) (promised : Bool) :
    blockPassChecked (pushK K m) call source promised =
      frameR K (blockPassChecked m call source promised) := by
  simp only [blockPassChecked, frameLem]
  split
  · rw [invoke_frame K hK]
  · split
    · split
      · exact blockPassMissing_frame K hK _ _ _ _ _
      · rw [invoke_frame K hK]
    · exact blockPassMissing_frame K hK _ _ _ _ _

theorem blockPassRespond_frame (K : List Kont) (hK : CatchFree K) (m : Machine)
    (call : BlockPassCall) (source : Value) (md : MethodDef) :
    blockPassRespond (pushK K m) call source md =
      frameR K (blockPassRespond m call source md) := by
  simp only [blockPassRespond, frameLem]
  repeat' first | rfl | (rw [invoke_frame K hK]) | split

theorem coerceBlockPass_frame (K : List Kont) (hK : CatchFree K) (m : Machine)
    (call : BlockPassCall) (source : Value) :
    coerceBlockPass (pushK K m) call source = frameR K (coerceBlockPass m call source) := by
  simp only [coerceBlockPass, frameLem]
  repeat' first
    | rfl
    | (rw [invoke_frame K hK])
    | exact blockPassRespond_frame K hK _ _ _ _
    | exact blockPassChecked_frame K hK _ _ _ _
    | split

theorem resumeBlockPass_frame (K : List Kont) (hK : CatchFree K) (m : Machine)
    (call : BlockPassCall) (source : Value) (phase : BlockPassPhase) (result : Value) :
    resumeBlockPass (pushK K m) call source phase result =
      frameR K (resumeBlockPass m call source phase result) := by
  cases phase <;> simp only [resumeBlockPass, frameLem]
  all_goals repeat' first
    | rfl
    | (rw [invoke_frame K hK])
    | exact blockPassChecked_frame K hK _ _ _ _
    | exact blockPassMissing_frame K hK _ _ _ _ _
    | split

@[simp, frameLem] theorem unwindBlockPass_frame (K : List Kont) (m : Machine)
    (source : Value) (phase : BlockPassPhase) (j : Jump) :
    unwindBlockPass (pushK K m) source phase j =
      frameR K (unwindBlockPass m source phase j) := by
  simp only [unwindBlockPass, frameLem]
  repeat' first | rfl | split

end RubyCore.Proof
