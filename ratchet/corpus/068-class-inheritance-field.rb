class Animal
  def initialize(name)
    @name = name
  end

  def speak
    @name
  end
end

class Dog < Animal
end

Dog.new("Rex").speak
