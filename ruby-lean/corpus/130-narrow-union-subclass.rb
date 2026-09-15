# typed: true
extend T::Sig
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
  def fetch
    "ball"
  end
end

sig { params(flag: T::Boolean).returns(Animal) }
def make(flag)
  if flag
    Dog.new
  else
    Animal.new
  end
end

v = make(true)
if v.is_a?(Dog)
  v.fetch
else
  v.speak
end
