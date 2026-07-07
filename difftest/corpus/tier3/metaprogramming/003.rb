class Base
  def greet; "base"; end
end
b = Base.new
puts b.greet
class Base
  def greet; "reopened"; end
  def extra; "extra"; end
end
puts b.greet
puts b.extra
