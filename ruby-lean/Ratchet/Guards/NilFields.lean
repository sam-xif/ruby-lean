import Ratchet.Lang.Ty

namespace Ratchet

/-- Finite field facts supplied by a fresh, empty allocation. This does not close the
instance annotation: unlisted fields still carry no information at ordinary entry. -/
def nilFieldsB : Ty → Bool
  | .ivar0 => true
  | .ivarCons _ .nilT rest => nilFieldsB rest
  | _ => false

def nilFields (names : List String) : Ty :=
  names.foldr (fun x rest => .ivarCons x .nilT rest) .ivar0

theorem nilFields_valid (names : List String) : nilFieldsB (nilFields names) = true := by
  induction names with
  | nil => rfl
  | cons x xs ih => exact ih

end Ratchet
