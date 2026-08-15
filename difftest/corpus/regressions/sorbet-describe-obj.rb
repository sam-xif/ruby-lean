# L127. The sorbet-runtime shim *does* enforce — a `sig` installs a checking
# wrapper, `T.let`/`cast`/`must` check, `T.unsafe` does not — and this file is
# about the part that was wrong anyway: how a failing check **describes the
# value**. Three rules from the gem's `T::Types::Base#describe_obj`, none of them
# guessable, all three observable, and the shim had none of them.
require "sorbet-runtime"
class Module
  include T::Sig
end

def show(label)
  puts("#{label} => #{yield.inspect}")
rescue StandardError => e
  puts("#{label} => #{e.class}: #{e.message.split("\n").first}")
end

# 1. nil/true/false print NO value clause ("redundant to print class and value").
show("nil")   { T.let(nil, Integer) }
show("true")  { T.let(true, Integer) }
show("false") { T.let(false, Integer) }

# 2. everything else prints `with value <inspect>`, truncated to 27 + "..." + 30
#    once the inspect exceeds 60 characters.
show("symbol")     { T.let(:sym, Integer) }
show("string")     { T.let("s", Integer) }
show("float")      { T.let(1.5, Integer) }
show("array")      { T.let([1, 2], Integer) }
show("hash")       { T.let({ a: 1 }, Integer) }
show("range")      { T.let((1..2), Integer) }
show("class")      { T.let(Integer, String) }
show("len 60")     { T.let("x" * 58, Integer) }
show("len 61")     { T.let("x" * 59, Integer) }
show("long array") { T.let((1..40).to_a, Integer) }

# a user `inspect` is not the default one, so it is printed rather than hashed
class WithInspect
  def inspect = "CUSTOM"
end
show("custom inspect") { T.let(WithInspect.new, Integer) }

# 3. a value whose `inspect` is the *default* prints `with hash <obj.hash>`, and
#    `Object#hash` is per-process seeded — so the model **gates** rather than
#    inventing a number (N38). Not exercised here: a gate anywhere refuses the
#    whole program, and the point of this file is the twelve lines above.

# the same rules through a `sig`, which is the path that matters for W8's
# "no blame fires" validation
class Calc
  extend T::Sig

  sig { params(a: Integer).returns(String) }
  def bad_return(a) = a

  sig { params(a: Integer, b: Integer).returns(Integer) }
  def add(a, b) = a + b

  sig { params(a: Integer).returns(Integer).checked(:never) }
  def unchecked(a) = a
end
c = Calc.new
show("param")       { c.add(1, "two") }
show("param nil")   { c.add(nil, 2) }
show("param long")  { c.add(1, "y" * 100) }
show("return")      { c.bad_return(1) }
show("checked never") { c.unchecked("not an int") }
show("ok")          { c.add(1, 2) }

# `T::Struct`'s prop message is a DIFFERENT rule, checked separately: plain
# `inspect`, no truncation, no hash substitution — and the class named by `to_s`,
# so an anonymous one is `#<Class:0x…>` where `name` would answer nil.
class Pt < T::Struct
  const :x, Integer
end
def norm(s) = s.gsub(/0x[0-9a-f]+/, "0xADDR")
show("struct long")  { Pt.new(x: "z" * 100) }
show("struct nil")   { Pt.new(x: nil) }
# `.split("\n").first` because the gem appends a `Caller:` source-location line to
# this message, which RubyCore cannot produce (no line numbers in the AST) and
# which the difftest engine normalizes away — but this line reads `$!.message`
# as a *value*, where the normalization does not reach.
show("struct anon") do
  k = Class.new
  norm((Pt.new(x: k.new) rescue $!.message).split("\n").first)
end
