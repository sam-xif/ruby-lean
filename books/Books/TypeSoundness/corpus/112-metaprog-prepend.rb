# typed: true
module Logger
  extend T::Sig
  sig { returns(String) }
  def speak
    "logged: " + super
  end
end

class Person
  extend T::Sig
  prepend Logger
  sig { returns(String) }
  def speak
    "hi"
  end
end

Person.new.speak
