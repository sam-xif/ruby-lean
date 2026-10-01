import Lean

/-! Completion proofs erase machine contents. Keep their simplification set
separate so simplification never evaluates an irrelevant heap or dispatch test. -/
register_simp_attr ndLem
