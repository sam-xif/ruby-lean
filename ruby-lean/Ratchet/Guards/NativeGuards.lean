import Ratchet.Static.All

/-! Compact dispatch metadata copied from the model's CRuby-name tables. Denote proves
coverage of this projection; the checker imports neither RubyCore nor the interpreter. -/
namespace Ratchet

def nativeQueryNames : List String := ["is_a?", "class", "raise", "===", "to_s", "nil?", "new"]
def nativeQueryRows : List (String × List String) :=
  [("Object", ["is_a?", "class", "raise", "===", "to_s", "nil?"]),
   ("Module", ["===", "to_s"]), ("Class", ["new"]), ("NilClass", ["===", "to_s", "nil?"]),
   ("TrueClass", ["===", "to_s"]), ("FalseClass", ["===", "to_s"]),
   ("Integer", ["===", "to_s"]), ("Float", ["===", "to_s"]),
   ("String", ["===", "to_s"]), ("Symbol", ["===", "to_s"]),
   ("Array", ["to_s"]), ("Hash", ["to_s"]), ("Proc", ["===", "to_s"]),
   ("Range", ["===", "to_s"]), ("Exception", ["to_s"])]

def nativeQueryHasB (cn mn : String) : Bool :=
  (nativeQueryRows.find? (·.1 == cn)).any (fun p => p.2.contains mn)
def nativeQueryFreeB (cn mn : String) : Bool :=
  nativeQueryNames.contains mn && !nativeQueryHasB cn mn
def classNativeQuietB (cn mn : String) : Bool :=
  nativeQueryFreeB cn mn && nativeQueryFreeB ("#<Class:" ++ cn ++ ">") mn
def classNativeFrameB (κ : Ctx) (cn : String) : Bool :=
  ["is_a?", "class", "raise", "===", "to_s", "nil?"].all fun mn =>
    !nameFreeN κ mn || classNativeQuietB cn mn

def singletonSendNames : List String :=
  ["constants", "nesting", "used_modules", "used_refinements", "allocate", "sqrt",
   "try_convert", "new", "all_symbols", "[]", "ruby2_keywords_hash", "ruby2_keywords_hash?",
   "bytes", "left", "new_seed", "rand", "seed", "srand", "state", "urandom", "exception", "to_tty?"]
def interceptedSendNames : List String :=
  ["call", "()", "[]", "yield", "new", "escape", "quote", "union", "sqrt", "exp", "log"]
def directCallNameB (mn : String) : Bool :=
  !interceptedSendNames.contains mn && !singletonSendNames.contains mn

end Ratchet
