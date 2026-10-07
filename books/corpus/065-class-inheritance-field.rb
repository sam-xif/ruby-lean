# typed: true
class Animal
  extend T::Sig
  sig { params(name: String).void }
  def initialize(name)
    @name = name
  end

  sig { returns(String) }
  def speak
    @name
  end
end

class Dog < Animal
end

Dog.new("Rex").speak
