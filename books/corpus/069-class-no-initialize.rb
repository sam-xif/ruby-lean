# typed: true
class Greeter
  extend T::Sig
  sig { returns(String) }
  def hi
    "hi"
  end
end

Greeter.new.hi
