/-! A finite upper bound on global constant bindings, not a table of their types.
The semantic boot gate checks this data against the actual prelude heap. -/
namespace Ratchet

def bootGlobalConsts : List String :=
  ["T", "Struct", "Encoding", "File", "URI", "Pathname", "JSON", "Forwardable",
   "Enumerable", "Comparable", "BasicObject", "Object", "Module", "Class", "NilClass",
   "TrueClass", "FalseClass", "Integer", "Float", "String", "Symbol", "Array", "Hash",
   "Exception", "StandardError", "RuntimeError", "ArgumentError", "TypeError", "NameError",
   "NoMethodError", "ZeroDivisionError", "LocalJumpError", "FrozenError", "IndexError",
   "KeyError", "RangeError", "StopIteration", "NotImplementedError", "ScriptError", "Proc",
   "Random", "Math", "Range", "Kernel", "Numeric", "UncaughtThrowError", "Regexp",
   "MatchData", "RegexpError"]

end Ratchet
