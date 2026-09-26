import Ratchet.Check.Check

/-! Certificates never supply trusted closure code, capture identity or return types. -/
namespace Ratchet.ClosureCheckControls

def literal (body : Expr := .int 1) (params : List Param := [])
    (locals : List String := []) (name : String := "lambda") : Expr :=
  .send none name [] (some (.block params locals body))
def call (name : String := "f") (args : List Expr := []) : Expr :=
  .send (some (.var .lvar name)) "call" args none
def program (body : Expr := .int 1) : Expr :=
  .seq [.vasgn .lvar "f" (literal body), call]
def hint (body : Deriv := .intLit 1) (ret : Ty := .int) : Deriv :=
  .flow (.seq [.vasgn .lvar "f" .closureLiteral, .closureCall body ret])

#guard validateD program hint
#guard validateD (program (.int 7)) (hint (.intLit 7))
#guard validateD (program .tru) (hint .truLit .bool)
#guard !validateD program (hint (.intLit 2))
#guard !validateD program (hint (.intLit 1) .bool)
#guard !validateD (program (.send (some (.int 1)) "missing" [] none)) hint
#guard !validateD (.seq [.vasgn .lvar "f" literal, call "f" [.int 1]]) hint
#guard !validateD (.seq [.vasgn .lvar "f" (literal (.int 1) [.req "x"]), call]) hint
#guard !validateD (.seq [.vasgn .lvar "f" (literal (.int 1) [] ["x"]), call]) hint
#guard !validateD (.seq [.vasgn .lvar "f" (literal (.int 1) [] [] "proc"), call]) hint

-- Copies retain an origin; overwriting the source does not invalidate the copy.
#guard validateD (.seq [.vasgn .lvar "f" literal, .vasgn .lvar "g" (.var .lvar "f"),
  .vasgn .lvar "f" .nil, call "g"])
  (.flow (.seq [.vasgn .lvar "f" .closureLiteral, .vasgn .lvar "g" (.var .lvar "f"),
    .vasgn .lvar "f" .nilLit, .closureCall (.intLit 1) .int]))
#guard !validateD (.seq [.vasgn .lvar "f" literal, .vasgn .lvar "f" .nil, call])
  (.flow (.seq [.vasgn .lvar "f" .closureLiteral, .vasgn .lvar "f" .nilLit,
    .closureCall (.intLit 1) .int]))

-- Ordinary expression effects deliberately forget origins. No silent preservation.
#guard !validateD (.seq [.vasgn .lvar "f" literal, .str "effect", call])
  (.flow (.seq [.vasgn .lvar "f" .closureLiteral, .strLit "effect", .closureCall (.intLit 1) .int]))
#guard !validateD (program (.var .lvar "missing")) (hint (.var .lvar "missing"))
#guard !validateD (program (.var .lvar "f")) (hint (.var .lvar "f"))

-- The entry wrapper claims no origin even when a caller supplies the exact code type.
def code : ClosureCode := ⟨[], [], .int 1, true, rfl⟩
#guard (check 50 [("f", .clos code .ivar0 .never)] call
  (.flow (.closureCall (.intLit 1) .int))).isNone
#guard (check 100 [] program hint
  { ctx0 with neg := { ctx0.neg with declared := ["call"] } }).isNone

-- Call-time body checking consumes the current local type, including newly bound slots.
def plusX : Expr := .send (some (.var .lvar "x")) "+" [.int 1] none
def plusHint : Deriv := .prim (.var .lvar "x") "+" [.intLit 1] .int .int
#guard validateD (.seq [.vasgn .lvar "f" (literal plusX), .vasgn .lvar "x" (.int 7), call])
  (.flow (.seq [.vasgn .lvar "f" .closureLiteral, .vasgn .lvar "x" (.intLit 7),
    .closureCall plusHint .int]))
#guard !validateD (.seq [.vasgn .lvar "f" (literal plusX), .vasgn .lvar "x" .nil, call])
  (.flow (.seq [.vasgn .lvar "f" .closureLiteral, .vasgn .lvar "x" .nilLit,
    .closureCall plusHint .int]))
end Ratchet.ClosureCheckControls
