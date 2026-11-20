# typed: true
extend T::Sig
class Animal
  extend T::Sig
  sig { returns(String) }
  def speak
    "..."
  end
end

sig { params(flag: T::Boolean).returns(T.nilable(Animal)) }
def find(flag)
  if flag
    Animal.new
  else
    nil
  end
end

v = find(true)
if v.nil?
  "none"
else
  v.speak
end
