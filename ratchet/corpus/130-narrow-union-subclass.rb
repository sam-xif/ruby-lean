class Animal
  def speak
    "..."
  end
end

class Dog < Animal
  def fetch
    "ball"
  end
end

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
