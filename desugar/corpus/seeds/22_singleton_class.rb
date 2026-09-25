# class << obj — reopen an object's singleton (eigen) class and define a method on it.
# The [:sclass] head must render back to the keyword form (not desugared away), since the
# body evaluates with the singleton class as self/cref.
obj = Object.new

class << obj
  def only_me
    "singleton method"
  end
end

print(obj.only_me)
print(";")
print(obj.respond_to?(:only_me))
print(";")
# a fresh Object does NOT have the singleton method.
print(Object.new.respond_to?(:only_me))
