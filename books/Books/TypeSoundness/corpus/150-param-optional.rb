# typed: true
extend T::Sig
sig { params(name: String, greeting: String).returns(String) }
def greet(name, greeting = "hi")
  greeting + " " + name
end

greet("a") + greet("a", "yo")
