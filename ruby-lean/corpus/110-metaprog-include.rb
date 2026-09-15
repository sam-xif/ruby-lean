# typed: true
module Greetable
  def greet
    "hi"
  end
end

class Person
  include Greetable
end

Person.new.greet
