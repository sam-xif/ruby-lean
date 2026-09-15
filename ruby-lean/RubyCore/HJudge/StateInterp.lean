/-
  RubyCore.HJudge.StateInterp — whole-heap ownership via iris-lean's `OwnP`.

  **Ported from `mdd/sorbet-lean/SorbetLean/StateInterp.lean`** (spike S1;
  cerberus arc-9 adoption, `RelSem/IrisState.lean` shape, verbatim).
  `stateIs h` is the ExclAuth fragment over the full `Heap`.

  Upgrade path (recorded, not taken): swapping this file for a gen_heap
  interpretation (`ObjId ↦ Obj` points-to, the golean `Ghost.lean`/
  `HeapBridge.lean` pattern) replaces THIS file without touching the
  `Language` instance or any adequacy statement — which is exactly the
  heaplet/cell door the H-layer's `HTy.sem` constructor keeps open
  (judgment-layer.md J36).

  House rules: no sorry, no new axioms.
-/
import Iris.ProgramLogic.OwnP
import RubyCore.HJudge.Lang

set_option autoImplicit false

namespace RubyCore.HJudge

open RubyCore
open Iris Iris.ProgramLogic

/-- Functor-inclusion prerequisite (pre-allocation form) at `Heap`. -/
abbrev RubyGpreS (GF : BundledGFunctors) : Type := OwnPGpreS Heap GF

/-- The allocated form at `Heap`. -/
abbrev RubyGS (GF : BundledGFunctors) : Type := OwnPGS Heap GF

variable {GF : BundledGFunctors}

/-- The proof-side state assertion: ownership of the whole heap. -/
abbrev stateIs [RubyGS GF] (h : Heap) : IProp GF := ownP h

/-- A closed functor bundle carrying the prerequisites (the cerberus `CerbS`
    pattern): indices 0–3 the invariant/credit machinery, index 4 the OwnP
    ExclAuth cell over `Heap`. Closed corollaries instantiate at `RubyS`. -/
def RubyS : BundledGFunctors
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF CoPsetDisjL, by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨Auth.AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨ownPRF Heap, by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

instance instRubyGpreS_RubyS : RubyGpreS RubyS where
  toWsatGpreS := by
    constructor
    · exists 0
    · exists 1
    · exists 2
  toLcGpreS := by
    constructor
    · exists 3
  inG := ⟨4, rfl⟩

end RubyCore.HJudge
