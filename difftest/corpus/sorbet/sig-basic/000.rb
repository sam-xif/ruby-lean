# typed: strict
require "sorbet-runtime"

class Greeter
  extend T::Sig

  sig { params(name: String).void }
  def initialize(name)
    @name = T.let(name, String)
  end

  sig { returns(String) }
  def greet
    "hello, #{@name}"
  end
end

puts Greeter.new("world").greet
