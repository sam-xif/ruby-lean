import Ratchet.Static.All
import Ratchet.Guards.NilFields

/-! Candidate nil fields for default construction, collected from receiver-body reads.
This scan grants no typing fact: allocation and every body are independently checked.
Unvisited syntax can cost completeness only. -/
namespace Ratchet

mutual
def fieldReads : Expr → List String
  | .var .ivar x => [x]
  | .vasgn _ _ e | .casgn _ e | .defined e => fieldReads e
  | .send recv _ args blk => fieldReadsOpt recv ++ fieldReadsAll args ++ fieldReadsOpt blk
  | .seq es | .array es | .yield' es => fieldReadsAll es
  | .hash ps => fieldReadsPairs ps
  | .if' c t e => fieldReads c ++ fieldReads t ++ fieldReadsOpt e
  | .while' c b | .dowhile b c | .for' _ c b => fieldReads c ++ fieldReads b
  | .block _ _ b => fieldReads b
  | .splat e | .ret e | .brk e | .nxt e | .blockpass e | .cpath e _ => fieldReadsOpt e
  | .super' es blk => fieldReadsAll es ++ fieldReadsOpt blk
  | .zsuper blk => fieldReadsOpt blk
  | _ => []

def fieldReadsAll : List Expr → List String
  | [] => []
  | e :: es => fieldReads e ++ fieldReadsAll es

def fieldReadsOpt : Option Expr → List String
  | none => []
  | some e => fieldReads e

def fieldReadsPairs : List (Expr × Expr) → List String
  | [] => []
  | (k, v) :: ps => fieldReads k ++ fieldReads v ++ fieldReadsPairs ps
end

def defaultReceiverFields (κ : Ctx) (cn : String) : Ty :=
  let chain := (ancestors? κ.classes cn).getD []
  let names := κ.classes.flatMap fun c =>
    if c.name ∈ chain then c.methods.flatMap (fun d => fieldReads d.body) else []
  nilFields (names.eraseDups.mergeSort (· ≤ ·))

end Ratchet
