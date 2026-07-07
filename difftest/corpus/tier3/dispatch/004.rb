class D
  def val; 1; end
end
d = D.new
puts d.val
m = d.method(:val)
class D
  def val; 2; end
end
puts d.val
puts m.call
