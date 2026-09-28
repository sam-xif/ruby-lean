def show(label)
  p [label, yield]
rescue StandardError => e
  p [label, e.class, e.message]
end
class FrozenThing
  def inspect
    puts :object_inspect
    "FROZEN"
  end
  def set
    @x = 1
  end
end
o = FrozenThing.new.freeze
show(:ivar) { o.set }
show(:reflective_ivar) { o.instance_variable_set(:@x, 1) }
a = [1]
def a.inspect
  puts :array_inspect
  "ARRAY"
end
a.freeze
show(:push) { a.push(2) }
show(:array_set) { a[0] = 2 }
h = {a: 1}
def h.inspect = "HASH"
h.freeze
show(:hash_set) { h[:b] = 2 }
s = "a"
def s.inspect = "STRING"
s.freeze
show(:string_append) { s << "b" }
class FrozenSubclass < Array
  def self.to_s
    puts :class_to_s
    "DISPLAY_CLASS"
  end
end
show(:subclass) { FrozenSubclass.new.freeze.push(1) }
[nil, 12, false, Object.new].each do |result|
  o = Object.new
  o.define_singleton_method(:inspect) { puts :inspect_result; result }
  o.freeze
  show(:inspect_result) { o.instance_variable_set(:@x, 1) }
end
repr = Object.new
def repr.to_s
  puts :repr_to_s
  "CONVERTED"
end
o = Object.new
o.define_singleton_method(:inspect) { repr }
o.freeze
show(:repr_to_s) { o.instance_variable_set(:@x, 1) }
def repr.to_s = 12
show(:invalid_to_s) { o.instance_variable_set(:@x, 1) }
o = Object.new
def o.inspect = raise("inspection failed")
o.freeze
show(:inspect_raises) { o.instance_variable_set(:@x, 1) }
o = Object.new
def o.inspect = throw(:inspection, :escaped)
o.freeze
show(:inspect_throw) { catch(:inspection) { o.instance_variable_set(:@x, 1) } }
o = Object.new
def o.inspect = @x = 1
o.freeze
show(:recursive_inspect) { o.instance_variable_set(:@x, 1) }
# The rendering recursion guard is gone after unwinding.
2.times { show(:recursive_again) { o.instance_variable_set(:@x, 1) } }
