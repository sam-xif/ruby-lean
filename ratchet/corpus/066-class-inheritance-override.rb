# typed: true
class Animal
  extend T::Sig
  sig { returns(String) }
  def speak
    "..."
  end
end

class Dog < Animal
  extend T::Sig
  sig { returns(String) }
  def speak
    "Woof"
  end
end

Dog.new.speak
