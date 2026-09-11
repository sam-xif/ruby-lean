# typed: true
module Logger
  def speak
    "logged: " + super
  end
end

class Person
  prepend Logger
  def speak
    "hi"
  end
end

Person.new.speak
