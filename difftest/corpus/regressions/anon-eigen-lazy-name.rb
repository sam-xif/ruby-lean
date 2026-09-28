# L276: singleton-class display names follow their attached object in the live heap.
def norm(s)
  s.gsub(/0x[0-9a-f]+/, "0xADDR")
end

k = Class.new
o = k.new
before = o.singleton_class.to_s     # materializes the eigenclass while anonymous
K = k                              # ...and *now* the class gets a name
after = o.singleton_class.to_s

puts("before => #{norm(before)}")
puts("after  => #{norm(after)}")
puts("recomputed => #{(before != after).to_s}")

# the control: name the class first, and both implementations agree
k2 = Class.new
K2 = k2
o2 = k2.new
puts("named first => #{norm(o2.singleton_class.to_s)}")

# A singleton class has no constant name until one is assigned to it, and that
# name does not replace its display of the attached object.
puts("unnamed eigen name => #{o2.singleton_class.name.inspect}")
Eigen = o2.singleton_class
puts("named eigen name => #{Eigen.name}")
puts("named eigen display => #{norm(Eigen.to_s)}")
k3 = Class.new
e3 = k3.singleton_class
ee3 = e3.singleton_class
K3 = k3
puts("class eigen => #{norm(e3.to_s)}")
puts("nested eigen => #{norm(ee3.to_s)}")
puts("boot eigen name => #{Object.singleton_class.name.inspect}")
