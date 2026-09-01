class Animal
  def speak
    "..."
  end
end

class Dog < Animal
  def speak
    "Woof"
  end
end

Dog.new.speak
