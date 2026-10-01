-- Generated from Ratchet/Check/SingletonCache.lean by scripts/generate_audited_checker.py.
-- Edit the raw source and regenerate; Lean checks the indexed proof and trace.
import Ratchet.Audit.Erase
import Ratchet.Audit.ReceiverCache

/-! Own singleton artifacts retain annotations and exact code/context, independently of
instance methods. Inherited singleton bodies need a separate receiver/owner contract. -/
set_option autoImplicit false
namespace Ratchet.Audit
open Ratchet

structure CallableSingleton (κ : Ctx) (c : Cls) (name : String) where
  decl : Defn
  nameOk : decl.name = name
  installed : decl ∈ c.smethods
  body : CheckedBody (singletonBodyCtx κ c.name decl.name) .ivar0 decl

def findSingleton (κ : Ctx) (c : Cls) (name : String) :
    List CachedSingleton → Option (CallableSingleton κ c name)
  | [] => none
  | b :: bs =>
    let found : Option (CallableSingleton κ c name) := do
      if b.owner != c.name then none else do
      if hn : b.decl.name = name then do
      if hi : b.spine = .ivar0 then do
        let ⟨hc⟩ ← ctxEq? b.ctx (singletonBodyCtx κ c.name b.decl.name)
        let ⟨hd⟩ ← defnMem? b.decl c.smethods
        some ⟨b.decl, hn, hd, by simpa only [hc, hi] using b.body⟩
      else none
      else none
    found.orElse (fun _ => findSingleton κ c name bs)

def singletonCacheCompleteB (κ : Ctx) (cache : CheckedCache) : Bool :=
  (κ.classes.map (·.name)).eraseDups.all fun cn =>
    match findClass cn κ.classes with
    | none => false
    | some c => c.cls.smethods.all fun d => (findSingleton κ c.cls d.name cache.singletons).isSome

end Ratchet.Audit
