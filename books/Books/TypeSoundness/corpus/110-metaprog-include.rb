# typed: true
module Greetable
  extend T::Sig
  sig { returns(String) }
  def greet
    "hi"
  end
end

class Person
  include Greetable
end

Person.new.greet
