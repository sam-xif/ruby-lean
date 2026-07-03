# class/module/inheritance/instance-methods/ivars/singleton-def.
# Exercises the [:class]/[:module]/[:def]/[:defs] heads and instance dispatch.
module Greeting
  def hello
    "hi from #{self.class.name}"
  end
end

class Animal
  def initialize(name)
    @name = name
  end

  def name
    @name
  end

  def self.kingdom
    "Animalia"
  end
end

class Dog < Animal
  def speak
    "#{name}: woof"
  end
end

d = Dog.new("Rex")
print(d.speak)
print(";")
print(Animal.kingdom)
print(";")
print(Dog.new("Fido").name)
