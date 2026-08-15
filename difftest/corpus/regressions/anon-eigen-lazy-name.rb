# L124, OPEN. CRuby computes an eigenclass's name *on demand*; the model fixes it
# when the eigenclass is created. They agree everywhere except here: an anonymous
# class that acquires a name (by constant assignment) *after* one of its
# instances already has an eigenclass.
#
#   CRuby  #<Class:#<K:0xADDR>>          — recomputed from the class's name now
#   model  #<Class:#<#<Class:0xADDR>:0xADDR>>  — the name the class had then
#
# Closing it means storing the attached object on the class payload and making
# `className` recursive (fuel-bounded), i.e. a heap-shape change on the dispatch
# path. Filed instead, so it cannot be forgotten.
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
