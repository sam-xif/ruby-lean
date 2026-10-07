import RubyCore.Interp
import Books.Metatheory.Builtins.StringFacts

/-! The pure builtin runner and the interpreter have distinct interfaces.
An `.ok` from `Builtins.run` is sufficient for a direct dispatch only when no
interpreter protocol intercepts the builtin id. -/
namespace RubyCore.Proof
open Interp

def directBuiltinB (bid : String) : Bool :=
  !(bid.startsWith "Main#" ||
    ["Object#inspect", "Object#raise", "Object#fail", "Exception.exception",
      "Exception#exception", "Exception#to_s", "UncaughtThrowError#to_s",
      "Object#initialize_dup", "Object#initialize_clone", "String#initialize_copy",
      "Array#initialize_copy", "Hash#initialize_copy", "Class#new", "Module#new",
      "Class#allocate", "Module#const_set", "Class#initialize", "Module#initialize",
      "String#initialize", "Array#initialize", "Hash#initialize", "Exception#initialize",
      "Object#__forwardable_compile", "String#+"].contains bid ||
    nativeDupBid bid || nativeCloneBid bid || requireBid bid || enumBid bid ||
    nativeIteratorBid bid || procCallBid bid || arrayMapBid bid)

end RubyCore.Proof
