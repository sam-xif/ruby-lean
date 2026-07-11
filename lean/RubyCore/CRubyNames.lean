/-
GENERATED from the CRuby oracle (ruby 4.0.5) by
`scripts/gen_cruby_names.rb` — do not hand-edit. Regenerate when the
oracle version bumps.

Purpose (dispatch fidelity, not behavior): the L0 model implements only a
slice of each core class, but lookup must know which names EXIST in CRuby
so that (a) an unmodeled builtin that would shadow a user method on Object
gates as Unsupported instead of mis-dispatching, and (b) a genuine
lookup-total-miss can be answered with a real NoMethodError.

Modules our L0 ancestors chain omits are folded into the nearest class
below them: Kernel→Object, Comparable→String/Symbol/Integer/Float,
Numeric→Integer/Float, Enumerable→Array/Hash.
-/
namespace RubyCore

/-- Method names each bootstrap class defines directly in CRuby
    (instance_methods(false) ∪ private_instance_methods(false), modules
    folded as above). -/
def crubyMethodNames : List (String × List String) := [
  ("BasicObject", [
    "!", "!=", "==", "__id__", "__send__", "equal?", "initialize", "instance_eval",
    "instance_exec", "method_missing", "singleton_method_added", "singleton_method_removed", "singleton_method_undefined"
  ]),
  ("Object", [
    "!~", "<=>", "===", "Array", "Complex", "Float", "Hash", "Integer",
    "Pathname", "Rational", "String", "__callee__", "__dir__", "__method__", "`", "abort",
    "at_exit", "autoload", "autoload?", "binding", "block_given?", "caller", "caller_locations", "catch",
    "class", "clone", "define_method", "define_singleton_method", "display", "dup", "enum_for", "eql?",
    "eval", "exec", "exit", "exit!", "extend", "fail", "fork", "format",
    "freeze", "frozen?", "gem", "gem_original_require", "gets", "global_variables", "hash", "include",
    "initialize_clone", "initialize_copy", "initialize_dup", "inspect", "instance_of?", "instance_variable_defined?", "instance_variable_get", "instance_variable_set",
    "instance_variables", "instance_variables_to_inspect", "is_a?", "iterator?", "itself", "kind_of?", "lambda", "load",
    "local_variables", "loop", "method", "methods", "nil?", "object_id", "open", "p",
    "pp", "print", "printf", "private", "private_methods", "proc", "protected_methods", "public",
    "public_method", "public_methods", "public_send", "putc", "puts", "raise", "rand", "readline",
    "readlines", "remove_instance_variable", "require", "require_relative", "respond_to?", "respond_to_missing?", "ruby2_keywords", "select",
    "send", "set_trace_func", "singleton_class", "singleton_method", "singleton_methods", "sleep", "spawn", "sprintf",
    "srand", "syscall", "system", "tap", "test", "then", "throw", "to_enum",
    "to_s", "trace_var", "trap", "untrace_var", "using", "warn", "yield_self"
  ]),
  ("Module", [
    "<", "<=", "<=>", "==", "===", ">", ">=", "alias_method",
    "ancestors", "append_features", "attr", "attr_accessor", "attr_reader", "attr_writer", "autoload", "autoload?",
    "class_eval", "class_exec", "class_variable_defined?", "class_variable_get", "class_variable_set", "class_variables", "const_added", "const_defined?",
    "const_get", "const_missing", "const_set", "const_source_location", "constants", "define_method", "deprecate_constant", "extend_object",
    "extended", "freeze", "include", "include?", "included", "included_modules", "initialize", "initialize_clone",
    "inspect", "instance_method", "instance_methods", "method_added", "method_defined?", "method_removed", "method_undefined", "module_eval",
    "module_exec", "module_function", "name", "prepend", "prepend_features", "prepended", "private", "private_class_method",
    "private_constant", "private_instance_methods", "private_method_defined?", "protected", "protected_instance_methods", "protected_method_defined?", "public", "public_class_method",
    "public_constant", "public_instance_method", "public_instance_methods", "public_method_defined?", "refine", "refinements", "remove_class_variable", "remove_const",
    "remove_method", "ruby2_keywords", "set_temporary_name", "singleton_class?", "to_s", "undef_method", "undefined_instance_methods", "using"
  ]),
  ("Class", [
    "allocate", "attached_object", "inherited", "initialize", "new", "subclasses", "superclass"
  ]),
  ("NilClass", [
    "&", "===", "=~", "^", "inspect", "nil?", "rationalize", "to_a",
    "to_c", "to_f", "to_h", "to_i", "to_r", "to_s", "|"
  ]),
  ("TrueClass", [
    "&", "===", "^", "inspect", "to_s", "|"
  ]),
  ("FalseClass", [
    "&", "===", "^", "inspect", "to_s", "|"
  ]),
  ("Integer", [
    "%", "&", "*", "**", "+", "+@", "-", "-@",
    "/", "<", "<<", "<=", "<=>", "==", "===", ">",
    ">=", ">>", "[]", "^", "abs", "abs2", "allbits?", "angle",
    "anybits?", "arg", "between?", "bit_length", "ceil", "ceildiv", "chr", "clamp",
    "clone", "coerce", "conj", "conjugate", "denominator", "digits", "div", "divmod",
    "downto", "dup", "eql?", "even?", "fdiv", "finite?", "floor", "gcd",
    "gcdlcm", "i", "imag", "imaginary", "infinite?", "inspect", "integer?", "lcm",
    "magnitude", "modulo", "negative?", "next", "nobits?", "nonzero?", "numerator", "odd?",
    "ord", "phase", "polar", "positive?", "pow", "pred", "quo", "rationalize",
    "real", "real?", "rect", "rectangular", "remainder", "round", "singleton_method_added", "size",
    "step", "succ", "times", "to_c", "to_f", "to_i", "to_int", "to_r",
    "to_s", "truncate", "upto", "zero?", "|", "~"
  ]),
  ("Float", [
    "%", "*", "**", "+", "+@", "-", "-@", "/",
    "<", "<=", "<=>", "==", "===", ">", ">=", "abs",
    "abs2", "angle", "arg", "between?", "ceil", "clamp", "clone", "coerce",
    "conj", "conjugate", "denominator", "div", "divmod", "dup", "eql?", "fdiv",
    "finite?", "floor", "hash", "i", "imag", "imaginary", "infinite?", "inspect",
    "integer?", "magnitude", "modulo", "nan?", "negative?", "next_float", "nonzero?", "numerator",
    "phase", "polar", "positive?", "prev_float", "quo", "rationalize", "real", "real?",
    "rect", "rectangular", "remainder", "round", "singleton_method_added", "step", "to_c", "to_f",
    "to_i", "to_int", "to_r", "to_s", "truncate", "zero?"
  ]),
  ("String", [
    "%", "*", "+", "+@", "-@", "<", "<<", "<=",
    "<=>", "==", "===", "=~", ">", ">=", "[]", "[]=",
    "append_as_bytes", "ascii_only?", "b", "between?", "byteindex", "byterindex", "bytes", "bytesize",
    "byteslice", "bytesplice", "capitalize", "capitalize!", "casecmp", "casecmp?", "center", "chars",
    "chomp", "chomp!", "chop", "chop!", "chr", "clamp", "clear", "codepoints",
    "concat", "count", "crypt", "dedup", "delete", "delete!", "delete_prefix", "delete_prefix!",
    "delete_suffix", "delete_suffix!", "downcase", "downcase!", "dump", "dup", "each_byte", "each_char",
    "each_codepoint", "each_grapheme_cluster", "each_line", "empty?", "encode", "encode!", "encoding", "end_with?",
    "eql?", "force_encoding", "freeze", "getbyte", "grapheme_clusters", "gsub", "gsub!", "hash",
    "hex", "include?", "index", "initialize", "initialize_copy", "insert", "inspect", "intern",
    "length", "lines", "ljust", "lstrip", "lstrip!", "match", "match?", "next",
    "next!", "oct", "ord", "partition", "prepend", "replace", "reverse", "reverse!",
    "rindex", "rjust", "rpartition", "rstrip", "rstrip!", "scan", "scrub", "scrub!",
    "setbyte", "size", "slice", "slice!", "split", "squeeze", "squeeze!", "start_with?",
    "strip", "strip!", "sub", "sub!", "succ", "succ!", "sum", "swapcase",
    "swapcase!", "to_c", "to_f", "to_i", "to_r", "to_s", "to_str", "to_sym",
    "tr", "tr!", "tr_s", "tr_s!", "undump", "unicode_normalize", "unicode_normalize!", "unicode_normalized?",
    "unpack", "unpack1", "upcase", "upcase!", "upto", "valid_encoding?"
  ]),
  ("Symbol", [
    "<", "<=", "<=>", "==", "===", "=~", ">", ">=",
    "[]", "between?", "capitalize", "casecmp", "casecmp?", "clamp", "downcase", "empty?",
    "encoding", "end_with?", "id2name", "inspect", "intern", "length", "match", "match?",
    "name", "next", "size", "slice", "start_with?", "succ", "swapcase", "to_proc",
    "to_s", "to_sym", "upcase"
  ]),
  ("Array", [
    "&", "*", "+", "-", "<<", "<=>", "==", "[]",
    "[]=", "all?", "any?", "append", "assoc", "at", "bsearch", "bsearch_index",
    "chain", "chunk", "chunk_while", "clear", "collect", "collect!", "collect_concat", "combination",
    "compact", "compact!", "concat", "count", "cycle", "deconstruct", "delete", "delete_at",
    "delete_if", "detect", "difference", "dig", "drop", "drop_while", "each", "each_cons",
    "each_entry", "each_index", "each_slice", "each_with_index", "each_with_object", "empty?", "entries", "eql?",
    "fetch", "fetch_values", "fill", "filter", "filter!", "filter_map", "find", "find_all",
    "find_index", "first", "flat_map", "flatten", "flatten!", "freeze", "grep", "grep_v",
    "group_by", "hash", "include?", "index", "initialize", "initialize_copy", "inject", "insert",
    "inspect", "intersect?", "intersection", "join", "keep_if", "last", "lazy", "length",
    "map", "map!", "max", "max_by", "member?", "min", "min_by", "minmax",
    "minmax_by", "none?", "one?", "pack", "partition", "permutation", "pop", "prepend",
    "product", "push", "rassoc", "reduce", "reject", "reject!", "repeated_combination", "repeated_permutation",
    "replace", "reverse", "reverse!", "reverse_each", "rfind", "rindex", "rotate", "rotate!",
    "sample", "select", "select!", "shift", "shuffle", "shuffle!", "size", "slice",
    "slice!", "slice_after", "slice_before", "slice_when", "sort", "sort!", "sort_by", "sort_by!",
    "sum", "take", "take_while", "tally", "to_a", "to_ary", "to_h", "to_s",
    "to_set", "transpose", "union", "uniq", "uniq!", "unshift", "values_at", "zip",
    "|"
  ]),
  ("Hash", [
    "<", "<=", "==", ">", ">=", "[]", "[]=", "all?",
    "any?", "assoc", "chain", "chunk", "chunk_while", "clear", "collect", "collect_concat",
    "compact", "compact!", "compare_by_identity", "compare_by_identity?", "count", "cycle", "deconstruct_keys", "default",
    "default=", "default_proc", "default_proc=", "delete", "delete_if", "detect", "dig", "drop",
    "drop_while", "each", "each_cons", "each_entry", "each_key", "each_pair", "each_slice", "each_value",
    "each_with_index", "each_with_object", "empty?", "entries", "eql?", "except", "fetch", "fetch_values",
    "filter", "filter!", "filter_map", "find", "find_all", "find_index", "first", "flat_map",
    "flatten", "freeze", "grep", "grep_v", "group_by", "has_key?", "has_value?", "hash",
    "include?", "initialize", "initialize_copy", "inject", "inspect", "invert", "keep_if", "key",
    "key?", "keys", "lazy", "length", "map", "max", "max_by", "member?",
    "merge", "merge!", "min", "min_by", "minmax", "minmax_by", "none?", "one?",
    "partition", "rassoc", "reduce", "rehash", "reject", "reject!", "replace", "reverse_each",
    "select", "select!", "shift", "size", "slice", "slice_after", "slice_before", "slice_when",
    "sort", "sort_by", "store", "sum", "take", "take_while", "tally", "to_a",
    "to_h", "to_hash", "to_proc", "to_s", "to_set", "transform_keys", "transform_keys!", "transform_values",
    "transform_values!", "uniq", "update", "value?", "values", "values_at", "zip"
  ]),
  ("Proc", [
    "<<", "==", "===", ">>", "[]", "arity", "binding", "call",
    "clone", "curry", "dup", "eql?", "hash", "inspect", "lambda?", "parameters",
    "ruby2_keywords", "source_location", "to_proc", "to_s", "yield"
  ]),
  ("Exception", [
    "==", "backtrace", "backtrace_locations", "cause", "detailed_message", "exception", "full_message", "initialize",
    "inspect", "message", "method_missing", "respond_to?", "respond_to_missing?", "set_backtrace", "to_s"
  ]),
  ("StandardError", [

  ]),
  ("RuntimeError", [

  ]),
  ("ArgumentError", [

  ]),
  ("TypeError", [

  ]),
  ("NameError", [
    "initialize", "local_variables", "name", "receiver"
  ]),
  ("NoMethodError", [
    "args", "initialize", "private_call?"
  ]),
  ("ZeroDivisionError", [

  ]),
  ("LocalJumpError", [
    "exit_value", "reason"
  ]),
  ("FrozenError", [
    "initialize", "receiver"
  ]),
  ("IndexError", [

  ]),
  ("KeyError", [
    "initialize", "key", "receiver"
  ]),
  ("RangeError", [

  ]),
  ("StopIteration", [
    "result"
  ]),
  ("NotImplementedError", [

  ]),
  ("ScriptError", [

  ])
]

/-- Singleton (class-side) method names each bootstrap class defines in
    CRuby (e.g. Hash.ruby2_keywords_hash, Array.[]): a send to a class
    object resolving past these must gate. -/
def crubySingletonNames : List (String × List String) := [
  ("BasicObject", [

  ]),
  ("Object", [

  ]),
  ("Module", [
    "constants", "nesting", "used_modules", "used_refinements"
  ]),
  ("Class", [
    "allocate"
  ]),
  ("NilClass", [

  ]),
  ("TrueClass", [

  ]),
  ("FalseClass", [

  ]),
  ("Integer", [
    "sqrt", "try_convert"
  ]),
  ("Float", [

  ]),
  ("String", [
    "new", "try_convert"
  ]),
  ("Symbol", [
    "all_symbols"
  ]),
  ("Array", [
    "[]", "new", "try_convert"
  ]),
  ("Hash", [
    "[]", "ruby2_keywords_hash", "ruby2_keywords_hash?", "try_convert"
  ]),
  ("Proc", [
    "new"
  ]),
  ("Exception", [
    "exception", "to_tty?"
  ]),
  ("StandardError", [

  ]),
  ("RuntimeError", [

  ]),
  ("ArgumentError", [

  ]),
  ("TypeError", [

  ]),
  ("NameError", [

  ]),
  ("NoMethodError", [

  ]),
  ("ZeroDivisionError", [

  ]),
  ("LocalJumpError", [

  ]),
  ("FrozenError", [

  ]),
  ("IndexError", [

  ]),
  ("KeyError", [

  ]),
  ("RangeError", [

  ]),
  ("StopIteration", [

  ]),
  ("NotImplementedError", [

  ]),
  ("ScriptError", [

  ])
]

/-- Toplevel constants CRuby defines (Object.constants): a constant-lookup
    miss on one of these is "unmodeled", not NameError. -/
def crubyToplevelConstants : List String := [
  "ARGF", "ARGV", "ArgumentError", "Array", "BasicObject", "Binding", "CROSS_COMPILING", "Class",
  "ClosedQueueError", "Comparable", "Complex", "ConditionVariable", "Data", "DidYouMean", "Dir", "ENV",
  "EOFError", "Encoding", "EncodingError", "Enumerable", "Enumerator", "Errno", "ErrorHighlight", "Exception",
  "FalseClass", "Fiber", "FiberError", "File", "FileTest", "Float", "FloatDomainError", "FrozenError",
  "GC", "Gem", "Hash", "IO", "IOError", "IndexError", "Integer", "Interrupt",
  "Kernel", "KeyError", "LoadError", "LocalJumpError", "Marshal", "MatchData", "Math", "Method",
  "Module", "Monitor", "MonitorMixin", "Mutex", "NameError", "NilClass", "NoMatchingPatternError", "NoMatchingPatternKeyError",
  "NoMemoryError", "NoMethodError", "NotImplementedError", "Numeric", "Object", "ObjectSpace", "Pathname", "Proc",
  "Process", "Queue", "RUBYGEMS_ACTIVATION_MONITOR", "RUBY_COPYRIGHT", "RUBY_DESCRIPTION", "RUBY_ENGINE", "RUBY_ENGINE_VERSION", "RUBY_PATCHLEVEL",
  "RUBY_PLATFORM", "RUBY_RELEASE_DATE", "RUBY_REVISION", "RUBY_VERSION", "Ractor", "Random", "Range", "RangeError",
  "Rational", "RbConfig", "Refinement", "Regexp", "RegexpError", "Ruby", "RubyVM", "RuntimeError",
  "STDERR", "STDIN", "STDOUT", "ScriptError", "SecurityError", "Set", "Signal", "SignalException",
  "SizedQueue", "StandardError", "StopIteration", "String", "Struct", "Symbol", "SyntaxError", "SyntaxSuggest",
  "SystemCallError", "SystemExit", "SystemStackError", "TOPLEVEL_BINDING", "Thread", "ThreadError", "ThreadGroup", "Time",
  "TracePoint", "TrueClass", "TypeError", "UnboundMethod", "UncaughtThrowError", "UnicodeNormalize", "Warning", "ZeroDivisionError"
]

def crubyClassDefines (className mname : String) : Bool :=
  match crubyMethodNames.find? (·.1 == className) with
  | some (_, names) => names.contains mname
  | none => false

def crubySingletonDefines (className mname : String) : Bool :=
  match crubySingletonNames.find? (·.1 == className) with
  | some (_, names) => names.contains mname
  | none => false

end RubyCore
