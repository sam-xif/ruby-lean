import Ratchet.Static.All

/-! The builtin chains `is_a?` narrowing over an Integer/String union consults. -/
namespace Ratchet

def intChain : List String := ["Integer", "Numeric", "Comparable"] ++ rootAncestors
def strChain : List String := ["String", "Comparable"] ++ rootAncestors

end Ratchet
