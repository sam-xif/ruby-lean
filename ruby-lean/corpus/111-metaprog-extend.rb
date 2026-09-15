# typed: true
module Loud
  def shout
    "LOUD"
  end
end

class Person
  extend Loud
end

Person.shout
