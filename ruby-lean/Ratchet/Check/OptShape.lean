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

namespace Ratchet

/-- Call-site keyword pairs `k: e`, keys and values aligned. -/
def kwPairs : List String → List Expr → List KwEntry
  | k :: ks, e :: es => .pair k e :: kwPairs ks es
  | _, _ => []

/-- The call-site values of `k: e` pairs whose keys are exactly `ks`, in order. -/
def kwArgs? : List String → List KwEntry → Option (List Expr)
  | [], [] => some []
  | k :: ks, .pair k' e :: rest => if k = k' then (kwArgs? ks rest).map (e :: ·) else none
  | _, _ => none

theorem kwArgs?_sound : ∀ {ks : List String} {es : List KwEntry} {args : List Expr},
    kwArgs? ks es = some args → es = kwPairs ks args ∧ args.length = ks.length
  | [], [], args, h => by simp [kwArgs?] at h; subst h; exact ⟨rfl, rfl⟩
  | k :: ks, .pair k' e :: rest, args, h => by
    simp only [kwArgs?] at h
    split at h
    · rename_i hk
      subst hk
      cases hr : kwArgs? ks rest with
      | none => rw [hr] at h; cases h
      | some as =>
        rw [hr] at h
        simp at h
        subst h
        obtain ⟨h1, h2⟩ := kwArgs?_sound hr
        exact ⟨by rw [h1]; rfl, by simp [h2]⟩
    · cases h
  | [], _ :: _, _, h => by simp [kwArgs?] at h
  | _ :: _, [], _, h => by simp [kwArgs?] at h
  | _ :: _, .dyn _ _ :: _, _, h => by simp [kwArgs?] at h
  | _ :: _, .splat _ :: _, _, h => by simp [kwArgs?] at h

end Ratchet
