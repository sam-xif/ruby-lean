# typed: true
module Loud
  extend T::Sig
  sig { returns(String) }
  def shout
    "LOUD"
  end
end

class Person
  extend Loud
end

Person.shout
