/-! Method-local aliases of the supplied callback. These facts describe actual
value identity, independently of the local type and callback signature. -/
namespace Ratchet

structure CallbackFacts where
  aliases : List String := []
deriving BEq, DecidableEq, Repr, Inhabited

namespace CallbackFacts
def empty : CallbackFacts := ⟨[]⟩

/-- Sorbet 0.6.13405 accepts copying &b and calling the copy after b=nil, but rejects
calling b itself after that overwrite (clinks 240–241). Other aliases remain valid. -/
def write (f : CallbackFacts) (x : String) (callback : Bool) : CallbackFacts :=
  ⟨(if callback then [x] else []) ++ f.aliases.filter (· != x)⟩

def copy (f : CallbackFacts) (x y : String) : CallbackFacts :=
  f.write x (f.aliases.contains y)
end CallbackFacts
end Ratchet
