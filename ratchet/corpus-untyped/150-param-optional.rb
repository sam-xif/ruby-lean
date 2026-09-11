def greet(name, greeting = "hi")
  greeting + " " + name
end

greet("a") + greet("a", "yo")
