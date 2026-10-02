import Ratchet.Static.CtxEq
import Ratchet.Lang.ExprEq
import Ratchet.Check.Deriv

/-! Recognizing one trailing optional parameter, and finding a definition by name. -/
namespace Ratchet

def optShape? (formals : List Param) (ps : List SigParam) (n : String) :
    Option ((d : Expr) ×' formals = ps.map (fun p => Param.req p.1) ++ [.opt n d]) :=
  match hl : formals.getLast? with
  | some (.opt n' d) =>
    if hn : n' = n then
      if h : paramEqAll formals.dropLast (ps.map (fun p => Param.req p.1)) = true then
        some ⟨d, by
          obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hl
          rw [hys, List.dropLast_concat] at h
          rw [hys, ← paramEqAll_sound h, ← hn]⟩
      else none
    else none
  | _ => none

def defnNamed? (name : String) : (ds : List Defn) → Option ((d : Defn) ×' (d ∈ ds ∧ d.name = name))
  | [] => none
  | x :: xs =>
    if h : x.name = name then some ⟨x, List.mem_cons_self, h⟩
    else (defnNamed? name xs).map (fun r => ⟨r.1, List.mem_cons_of_mem _ r.2.1, r.2.2⟩)

end Ratchet
