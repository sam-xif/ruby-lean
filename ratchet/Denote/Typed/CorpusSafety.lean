import Denote.Typed.Derivations
import Denote.Typed.MethodDerivations
import Denote.Typed.RecursiveDerivations
import Denote.Typed.ClassDerivations
import Denote.Typed.RectDerivations

/-! Concrete corpus programs and their derivations. `SemLadder` compares each program
against the current stripped corpus; `RuleAudit` reads the clinks from these proofs. -/

set_option autoImplicit false
namespace Ratchet.Denote.Typed
open RubyCore Ratchet Ratchet.Denote

def program_001_int_lit : Ratchet.Expr :=
  .int (1)

theorem safe_001_int_lit (hb : bootOkB = true) : StuckFree bootMachine program_001_int_lit :=
  dregistry_safe (derivD_intLit) (stateOk_boot hb)

def program_002_bool_true : Ratchet.Expr :=
  .tru

theorem safe_002_bool_true (hb : bootOkB = true) : StuckFree bootMachine program_002_bool_true :=
  dregistry_safe (derivD_truLit) (stateOk_boot hb)

def program_003_bool_false : Ratchet.Expr :=
  .fls

theorem safe_003_bool_false (hb : bootOkB = true) : StuckFree bootMachine program_003_bool_false :=
  dregistry_safe (derivD_flsLit) (stateOk_boot hb)

def program_004_str_lit : Ratchet.Expr :=
  .str "hello"

theorem safe_004_str_lit (hb : bootOkB = true) : StuckFree bootMachine program_004_str_lit :=
  dregistry_safe (derivD_strLit) (stateOk_boot hb)

def program_005_sym_lit : Ratchet.Expr :=
  .sym "ok"

theorem safe_005_sym_lit (hb : bootOkB = true) : StuckFree bootMachine program_005_sym_lit :=
  dregistry_safe (derivD_symLit) (stateOk_boot hb)

def program_006_nil_lit : Ratchet.Expr :=
  .nil

theorem safe_006_nil_lit (hb : bootOkB = true) : StuckFree bootMachine program_006_nil_lit :=
  dregistry_safe (derivD_nilLit) (stateOk_boot hb)

def program_007_flt_lit : Ratchet.Expr :=
  .flt (1.5 : Float).toBits

theorem safe_007_flt_lit (hb : bootOkB = true) : StuckFree bootMachine program_007_flt_lit :=
  dregistry_safe (derivD_fltLit) (stateOk_boot hb)

def program_008_neg_int_lit : Ratchet.Expr :=
  .int (-5)

theorem safe_008_neg_int_lit (hb : bootOkB = true) : StuckFree bootMachine program_008_neg_int_lit :=
  dregistry_safe (derivD_intLit) (stateOk_boot hb)

def program_009_add : Ratchet.Expr :=
  .send (some (.int (1))) "+" [.int (2)] none

theorem safe_009_add (hb : bootOkB = true) : StuckFree bootMachine program_009_add :=
  dregistry_safe (derivD_prim (derivD_intLit) (derivD_allCons (derivD_intLit) (derivD_allNil) rfl) .intAdd) (stateOk_boot hb)

def program_010_sub : Ratchet.Expr :=
  .send (some (.int (5))) "-" [.int (3)] none

theorem safe_010_sub (hb : bootOkB = true) : StuckFree bootMachine program_010_sub :=
  dregistry_safe (derivD_prim (derivD_intLit) (derivD_allCons (derivD_intLit) (derivD_allNil) rfl) .intSub) (stateOk_boot hb)

def program_011_mul : Ratchet.Expr :=
  .send (some (.int (4))) "*" [.int (3)] none

theorem safe_011_mul (hb : bootOkB = true) : StuckFree bootMachine program_011_mul :=
  dregistry_safe (derivD_prim (derivD_intLit) (derivD_allCons (derivD_intLit) (derivD_allNil) rfl) .intMul) (stateOk_boot hb)

def program_012_div : Ratchet.Expr :=
  .send (some (.int (10))) "/" [.int (2)] none

theorem safe_012_div (hb : bootOkB = true) : StuckFree bootMachine program_012_div :=
  dregistry_safe (derivD_prim (derivD_intLit) (derivD_allCons (derivD_intLit) (derivD_allNil) rfl) .intDiv) (stateOk_boot hb)

def program_013_str_concat : Ratchet.Expr :=
  .send (some (.str "a")) "+" [.str "b"] none

theorem safe_013_str_concat (hb : bootOkB = true) : StuckFree bootMachine program_013_str_concat :=
  dregistry_safe (derivD_prim (derivD_strLit) (derivD_allCons (derivD_strLit) (derivD_allNil) rfl) .strAdd) (stateOk_boot hb)

def program_014_cmp_lt : Ratchet.Expr :=
  .send (some (.int (3))) "<" [.int (5)] none

theorem safe_014_cmp_lt (hb : bootOkB = true) : StuckFree bootMachine program_014_cmp_lt :=
  dregistry_safe (derivD_prim (derivD_intLit) (derivD_allCons (derivD_intLit) (derivD_allNil) rfl) .intLt) (stateOk_boot hb)

def program_015_not_expr : Ratchet.Expr :=
  .send (some (.tru)) "!" [] none

theorem safe_015_not_expr (hb : bootOkB = true) : StuckFree bootMachine program_015_not_expr :=
  dregistry_safe (derivD_prim (derivD_truLit) (derivD_allNil) .notBool) (stateOk_boot hb)

def program_016_bool_and : Ratchet.Expr :=
  .seq [.vasgn .lvar "__dt_t1" (.tru), .if' (.var .lvar "__dt_t1") (.fls) (some (.var .lvar "__dt_t1"))]

theorem safe_016_bool_and (hb : bootOkB = true) : StuckFree bootMachine program_016_bool_and :=
  dregistry_safe (derivD_seq (derivD_seqCons (derivD_vasgn (derivD_truLit) rfl rfl) (derivD_seqLast (derivD_if (derivD_var rfl rfl) (derivD_flsLit) (derivD_var rfl rfl))))) (stateOk_boot hb)

def program_017_bool_or : Ratchet.Expr :=
  .seq [.vasgn .lvar "__dt_t1" (.fls), .if' (.var .lvar "__dt_t1") (.var .lvar "__dt_t1") (some (.tru))]

theorem safe_017_bool_or (hb : bootOkB = true) : StuckFree bootMachine program_017_bool_or :=
  dregistry_safe (derivD_seq (derivD_seqCons (derivD_vasgn (derivD_flsLit) rfl rfl) (derivD_seqLast (derivD_if (derivD_var rfl rfl) (derivD_var rfl rfl) (derivD_truLit))))) (stateOk_boot hb)

def program_019_to_s_call : Ratchet.Expr :=
  .send (some (.int 5)) "to_s" [] none

theorem safe_019_to_s_call (hb : bootOkB = true) : StuckFree bootMachine program_019_to_s_call :=
  dregistry_safe (derivD_prim derivD_intLit derivD_allNil .intToS) (stateOk_boot hb)

def program_020_eq_same_type : Ratchet.Expr :=
  .send (some (.int 1)) "==" [.int 1] none

theorem safe_020_eq_same_type (hb : bootOkB = true) : StuckFree bootMachine program_020_eq_same_type :=
  dregistry_safe (derivD_prim derivD_intLit (derivD_allCons derivD_intLit derivD_allNil rfl)
    .intEq) (stateOk_boot hb)

def program_021_eq_different_type : Ratchet.Expr :=
  .send (some (.int 1)) "==" [.str "a"] none

theorem safe_021_eq_different_type (hb : bootOkB = true) : StuckFree bootMachine program_021_eq_different_type :=
  dregistry_safe (derivD_prim derivD_intLit (derivD_allCons derivD_strLit derivD_allNil rfl)
    .intEq) (stateOk_boot hb)

def program_022_unmodeled_builtin_zero_p : Ratchet.Expr :=
  .send (some (.int 5)) "zero?" [] none

theorem safe_022_unmodeled_builtin_zero_p (hb : bootOkB = true) : StuckFree bootMachine program_022_unmodeled_builtin_zero_p :=
  dregistry_safe (derivD_prim derivD_intLit derivD_allNil .intZero) (stateOk_boot hb)

def program_024_cmp_le : Ratchet.Expr :=
  .send (some (.int 1)) "<=" [.int 2] none

theorem safe_024_cmp_le (hb : bootOkB = true) : StuckFree bootMachine program_024_cmp_le :=
  dregistry_safe (derivD_prim derivD_intLit (derivD_allCons derivD_intLit derivD_allNil rfl) .intLe) (stateOk_boot hb)

def program_025_cmp_ge : Ratchet.Expr :=
  .send (some (.int 1)) ">=" [.int 2] none

theorem safe_025_cmp_ge (hb : bootOkB = true) : StuckFree bootMachine program_025_cmp_ge :=
  dregistry_safe (derivD_prim derivD_intLit (derivD_allCons derivD_intLit derivD_allNil rfl) .intGe) (stateOk_boot hb)

def program_026_nil_eq_nil : Ratchet.Expr :=
  .send (some .nil) "==" [.nil] none

theorem safe_026_nil_eq_nil (hb : bootOkB = true) : StuckFree bootMachine program_026_nil_eq_nil :=
  dregistry_safe (derivD_prim derivD_nilLit (derivD_allCons derivD_nilLit derivD_allNil rfl) .nilEq) (stateOk_boot hb)

def program_027_nested_arith : Ratchet.Expr :=
  .send (some (.send (some (.int (1))) "+" [.int (2)] none)) "*" [.int (3)] none

theorem safe_027_nested_arith (hb : bootOkB = true) : StuckFree bootMachine program_027_nested_arith :=
  dregistry_safe (derivD_prim (derivD_prim (derivD_intLit) (derivD_allCons (derivD_intLit) (derivD_allNil) rfl) .intAdd) (derivD_allCons (derivD_intLit) (derivD_allNil) rfl) .intMul) (stateOk_boot hb)

def program_028_str_length : Ratchet.Expr :=
  .send (some (.str "abc")) "length" [] none

theorem safe_028_str_length (hb : bootOkB = true) : StuckFree bootMachine program_028_str_length :=
  dregistry_safe (derivD_prim derivD_strLit derivD_allNil .strLength) (stateOk_boot hb)

def program_029_simple_assign : Ratchet.Expr :=
  .seq [.vasgn .lvar "x" (.int (5)), .send (some (.var .lvar "x")) "+" [.int (1)] none]

theorem safe_029_simple_assign (hb : bootOkB = true) : StuckFree bootMachine program_029_simple_assign :=
  dregistry_safe (derivD_seq (derivD_seqCons (derivD_vasgn (derivD_intLit) rfl rfl) (derivD_seqLast (derivD_prim (derivD_var rfl rfl) (derivD_allCons (derivD_intLit) (derivD_allNil) rfl) .intAdd)))) (stateOk_boot hb)

def program_030_reassign_same_type : Ratchet.Expr :=
  .seq [.vasgn .lvar "x" (.int (1)), .vasgn .lvar "x" (.int (2)), .send (some (.var .lvar "x")) "+" [.int (3)] none]

theorem safe_030_reassign_same_type (hb : bootOkB = true) : StuckFree bootMachine program_030_reassign_same_type :=
  dregistry_safe (derivD_seq (derivD_seqCons (derivD_vasgn (derivD_intLit) rfl rfl) (derivD_seqCons (derivD_vasgn (derivD_intLit) rfl rfl) (derivD_seqLast (derivD_prim (derivD_var rfl rfl) (derivD_allCons (derivD_intLit) (derivD_allNil) rfl) .intAdd))))) (stateOk_boot hb)

def program_031_reassign_different_type : Ratchet.Expr :=
  .seq [.vasgn .lvar "x" (.int (1)), .vasgn .lvar "x" (.tru), .var .lvar "x"]

theorem safe_031_reassign_different_type (hb : bootOkB = true) : StuckFree bootMachine program_031_reassign_different_type :=
  dregistry_safe (derivD_seq (derivD_seqCons (derivD_vasgn (derivD_intLit) rfl rfl) (derivD_seqCons (derivD_vasgn (derivD_truLit) rfl rfl) (derivD_seqLast (derivD_var rfl rfl))))) (stateOk_boot hb)

def program_032_bare_undeclared_var : Ratchet.Expr := .vcall "x"

theorem safe_032_bare_undeclared_var (hb : bootOkB = true) :
    StuckFree bootMachine program_032_bare_undeclared_var :=
  dregistry_safe derivD_bareName (stateOk_boot hb)

def program_033_seq_multiple_stmts : Ratchet.Expr :=
  .seq [.vasgn .lvar "x" (.int (1)), .vasgn .lvar "y" (.int (2)), .send (some (.var .lvar "x")) "+" [.var .lvar "y"] none]

theorem safe_033_seq_multiple_stmts (hb : bootOkB = true) : StuckFree bootMachine program_033_seq_multiple_stmts :=
  dregistry_safe (derivD_seq (derivD_seqCons (derivD_vasgn (derivD_intLit) rfl rfl) (derivD_seqCons (derivD_vasgn (derivD_intLit) rfl rfl) (derivD_seqLast (derivD_prim (derivD_var rfl rfl) (derivD_allCons (derivD_var rfl rfl) (derivD_allNil) rfl) .intAdd))))) (stateOk_boot hb)

def program_034_assignment_chain : Ratchet.Expr :=
  .seq [.vasgn .lvar "x" (.int (1)), .vasgn .lvar "y" (.send (some (.var .lvar "x")) "+" [.int (1)] none), .vasgn .lvar "z" (.send (some (.var .lvar "y")) "+" [.int (1)] none), .var .lvar "z"]

theorem safe_034_assignment_chain (hb : bootOkB = true) : StuckFree bootMachine program_034_assignment_chain :=
  dregistry_safe (derivD_seq (derivD_seqCons (derivD_vasgn (derivD_intLit) rfl rfl) (derivD_seqCons (derivD_vasgn (derivD_prim (derivD_var rfl rfl) (derivD_allCons (derivD_intLit) (derivD_allNil) rfl) .intAdd) rfl rfl) (derivD_seqCons (derivD_vasgn (derivD_prim (derivD_var rfl rfl) (derivD_allCons (derivD_intLit) (derivD_allNil) rfl) .intAdd) rfl rfl) (derivD_seqLast (derivD_var rfl rfl)))))) (stateOk_boot hb)

def program_035_if_true_branch : Ratchet.Expr :=
  .if' (.tru) (.int (1)) (some (.int (2)))

theorem safe_035_if_true_branch (hb : bootOkB = true) : StuckFree bootMachine program_035_if_true_branch :=
  dregistry_safe (derivD_if (derivD_truLit) (derivD_intLit) (derivD_intLit)) (stateOk_boot hb)

def program_036_if_no_else : Ratchet.Expr :=
  .if' .tru (.int 1) none

theorem safe_036_if_no_else (hb : bootOkB = true) : StuckFree bootMachine program_036_if_no_else :=
  dregistry_safe (derivD_ifNoElse derivD_truLit derivD_intLit) (stateOk_boot hb)

def program_037_if_condition_not_bool : Ratchet.Expr :=
  .if' (.int (5)) (.int (1)) (some (.int (2)))

theorem safe_037_if_condition_not_bool (hb : bootOkB = true) : StuckFree bootMachine program_037_if_condition_not_bool :=
  dregistry_safe (derivD_if (derivD_intLit) (derivD_intLit) (derivD_intLit)) (stateOk_boot hb)

def program_038_if_branch_mismatch : Ratchet.Expr :=
  .if' (.tru) (.int (1)) (some (.str "a"))

theorem safe_038_if_branch_mismatch (hb : bootOkB = true) : StuckFree bootMachine program_038_if_branch_mismatch :=
  dregistry_safe (derivD_if (derivD_truLit) (derivD_intLit) (derivD_strLit)) (stateOk_boot hb)

def program_040_if_nil_condition : Ratchet.Expr :=
  .if' (.nil) (.int (1)) (some (.int (2)))

theorem safe_040_if_nil_condition (hb : bootOkB = true) : StuckFree bootMachine program_040_if_nil_condition :=
  dregistry_safe (derivD_if (derivD_nilLit) (derivD_intLit) (derivD_intLit)) (stateOk_boot hb)

def program_041_nested_if : Ratchet.Expr :=
  .if' (.tru) (.if' (.fls) (.int (1)) (some (.int (2)))) (some (.int (3)))

theorem safe_041_nested_if (hb : bootOkB = true) : StuckFree bootMachine program_041_nested_if :=
  dregistry_safe (derivD_if (derivD_truLit) (derivD_if (derivD_flsLit) (derivD_intLit) (derivD_intLit)) (derivD_intLit)) (stateOk_boot hb)

def program_043_elsif_chain : Ratchet.Expr :=
  .if' (.tru) (.int (1)) (some (.if' (.fls) (.int (2)) (some (.int (3)))))

theorem safe_043_elsif_chain (hb : bootOkB = true) : StuckFree bootMachine program_043_elsif_chain :=
  dregistry_safe (derivD_if (derivD_truLit) (derivD_intLit) (derivD_if (derivD_flsLit) (derivD_intLit) (derivD_intLit))) (stateOk_boot hb)

def program_189_ctl_ternary : Ratchet.Expr :=
  .seq [.vasgn .lvar "x" (.int 1),
    .if' (.send (some (.var .lvar "x")) "zero?" [] none)
      (.str "zero") (some (.str "nonzero"))]

theorem safe_189_ctl_ternary (hb : bootOkB = true) : StuckFree bootMachine program_189_ctl_ternary :=
  dregistry_safe (derivD_seq (derivD_seqCons (derivD_vasgn derivD_intLit rfl rfl)
    (derivD_seqLast (derivD_if (derivD_prim (derivD_var rfl rfl) derivD_allNil .intZero)
      derivD_strLit derivD_strLit)))) (stateOk_boot hb)

def program_044_array_int : Ratchet.Expr := .array [.int 1, .int 2, .int 3]

theorem safe_044_array_int (hb : bootOkB = true) : StuckFree bootMachine program_044_array_int :=
  dregistry_safe (derivD_arrayLit
    (derivD_allCons derivD_intLit
      (derivD_allCons derivD_intLit (derivD_allCons derivD_intLit derivD_allNil rfl) rfl) rfl)
    rfl) (stateOk_boot hb)

def program_048_hash_lit : Ratchet.Expr := .hash [(.str "a", .int 1), (.str "b", .int 2)]

theorem safe_048_hash_lit (hb : bootOkB = true) : StuckFree bootMachine program_048_hash_lit :=
  dregistry_safe (derivD_hashLit
    (derivD_pairsCons derivD_strLit derivD_intLit
      (derivD_pairsCons derivD_strLit derivD_intLit derivD_pairsNil))
    rfl rfl) (stateOk_boot hb)

def program_050_array_index : Ratchet.Expr :=
  .send (some (.array [.int 1, .int 2, .int 3])) "[]" [.int 0] none

theorem safe_050_array_index (hb : bootOkB = true) : StuckFree bootMachine program_050_array_index :=
  dregistry_safe (derivD_prim (derivD_arrayLit
    (derivD_allCons derivD_intLit
      (derivD_allCons derivD_intLit (derivD_allCons derivD_intLit derivD_allNil rfl) rfl) rfl) rfl)
    (derivD_allCons derivD_intLit derivD_allNil rfl) (.arrayIndex rfl)) (stateOk_boot hb)

def program_051_hash_index : Ratchet.Expr :=
  .send (some (.hash [(.str "a", .int 1)])) "[]" [.str "a"] none

theorem safe_051_hash_index (hb : bootOkB = true) : StuckFree bootMachine program_051_hash_index :=
  dregistry_safe (derivD_prim
    (derivD_hashLit (derivD_pairsCons derivD_strLit derivD_intLit derivD_pairsNil) rfl rfl)
    (derivD_allCons derivD_strLit derivD_allNil rfl) (.hashIndex rfl)) (stateOk_boot hb)

def safeRungs : List (String × Ratchet.Expr) :=
  [("001-int-lit", program_001_int_lit),
   ("002-bool-true", program_002_bool_true),
   ("003-bool-false", program_003_bool_false),
   ("004-str-lit", program_004_str_lit),
   ("005-sym-lit", program_005_sym_lit),
   ("006-nil-lit", program_006_nil_lit),
   ("007-flt-lit", program_007_flt_lit),
   ("008-neg-int-lit", program_008_neg_int_lit),
   ("009-add", program_009_add),
   ("010-sub", program_010_sub),
   ("011-mul", program_011_mul),
   ("012-div", program_012_div),
   ("013-str-concat", program_013_str_concat),
   ("014-cmp-lt", program_014_cmp_lt),
   ("015-not-expr", program_015_not_expr),
   ("016-bool-and", program_016_bool_and),
   ("017-bool-or", program_017_bool_or),
   ("019-to-s-call", program_019_to_s_call),
   ("020-eq-same-type", program_020_eq_same_type),
   ("021-eq-different-type", program_021_eq_different_type),
   ("022-unmodeled-builtin-zero-p", program_022_unmodeled_builtin_zero_p),
   ("024-cmp-le", program_024_cmp_le),
   ("025-cmp-ge", program_025_cmp_ge),
   ("026-nil-eq-nil", program_026_nil_eq_nil),
   ("027-nested-arith", program_027_nested_arith),
   ("028-str-length", program_028_str_length),
   ("029-simple-assign", program_029_simple_assign),
   ("030-reassign-same-type", program_030_reassign_same_type),
   ("031-reassign-different-type", program_031_reassign_different_type),
   ("032-bare-undeclared-var", program_032_bare_undeclared_var),
   ("033-seq-multiple-stmts", program_033_seq_multiple_stmts),
   ("034-assignment-chain", program_034_assignment_chain),
   ("035-if-true-branch", program_035_if_true_branch),
   ("036-if-no-else", program_036_if_no_else),
   ("037-if-condition-not-bool", program_037_if_condition_not_bool),
   ("038-if-branch-mismatch", program_038_if_branch_mismatch),
   ("040-if-nil-condition", program_040_if_nil_condition),
   ("041-nested-if", program_041_nested_if),
   ("043-elsif-chain", program_043_elsif_chain),
   ("189-ctl-ternary", program_189_ctl_ternary),
   ("044-array-int", program_044_array_int),
   ("048-hash-lit", program_048_hash_lit),
   ("050-array-index", program_050_array_index),
   ("051-hash-index", program_051_hash_index),
   ("052-simple-fun", program_052_simple_fun),
   ("060-fun-recursive-factorial", program_060_fun_recursive_factorial),
   ("061-class-basic", program_061_class_basic),
   ("064-class-method-calls-method", program_064_class_method_calls_method)]

theorem safeRungs_safe (hb : bootOkB = true) :
    ∀ q ∈ safeRungs, StuckFree bootMachine q.2 := by
  intro q hq
  simp only [safeRungs, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact safe_001_int_lit hb
  · exact safe_002_bool_true hb
  · exact safe_003_bool_false hb
  · exact safe_004_str_lit hb
  · exact safe_005_sym_lit hb
  · exact safe_006_nil_lit hb
  · exact safe_007_flt_lit hb
  · exact safe_008_neg_int_lit hb
  · exact safe_009_add hb
  · exact safe_010_sub hb
  · exact safe_011_mul hb
  · exact safe_012_div hb
  · exact safe_013_str_concat hb
  · exact safe_014_cmp_lt hb
  · exact safe_015_not_expr hb
  · exact safe_016_bool_and hb
  · exact safe_017_bool_or hb
  · exact safe_019_to_s_call hb
  · exact safe_020_eq_same_type hb
  · exact safe_021_eq_different_type hb
  · exact safe_022_unmodeled_builtin_zero_p hb
  · exact safe_024_cmp_le hb
  · exact safe_025_cmp_ge hb
  · exact safe_026_nil_eq_nil hb
  · exact safe_027_nested_arith hb
  · exact safe_028_str_length hb
  · exact safe_029_simple_assign hb
  · exact safe_030_reassign_same_type hb
  · exact safe_031_reassign_different_type hb
  · exact safe_032_bare_undeclared_var hb
  · exact safe_033_seq_multiple_stmts hb
  · exact safe_034_assignment_chain hb
  · exact safe_035_if_true_branch hb
  · exact safe_036_if_no_else hb
  · exact safe_037_if_condition_not_bool hb
  · exact safe_038_if_branch_mismatch hb
  · exact safe_040_if_nil_condition hb
  · exact safe_041_nested_if hb
  · exact safe_043_elsif_chain hb
  · exact safe_189_ctl_ternary hb
  · exact safe_044_array_int hb
  · exact safe_048_hash_lit hb
  · exact safe_050_array_index hb
  · exact safe_051_hash_index hb
  · exact safe_052_simple_fun hb
  · exact safe_060_fun_recursive_factorial hb
  · exact safe_061_class_basic hb
  · exact safe_064_class_method_calls_method hb

#print axioms safeRungs_safe
end Ratchet.Denote.Typed
