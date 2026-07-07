class F
  def hi; "F"; end
end
f = F.new
def f.hi
  "S->" + super
end
puts f.hi
puts F.new.hi
puts f.method(:hi).super_method.call
