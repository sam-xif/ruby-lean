# L124. An anonymous class (`Class.new`) has no name, and CRuby renders it by
# address wherever a name is wanted — so every message built from a class name
# carries the `#<Class:0x…>` form. The model answered the empty string.
#
# The address is what kept this out of the corpus (N38: an observation must be
# process-independent). It does not have to: the program can **normalize the
# address itself** and then assert the whole message, which is stronger than the
# `include?("Class:0x")` predicate the handoff proposed.
def norm(s)
  s.gsub(/0x[0-9a-f]+/, "0xADDR")
end

def show(label)
  puts("#{label} => #{norm(yield.to_s)}")
rescue StandardError => e
  # the class name needs normalizing too: an anonymous exception class *is* an
  # address form
  puts("#{label} => #{norm(e.class.to_s)}: #{norm(e.message)}")
end

# locals, not constants: a constant assignment *names* an anonymous class (L72),
# and a named class does not exercise any of this. The two `Named*` cases at the
# bottom are the deliberate exception.
anon = Class.new
anon_err = Class.new(StandardError)

# `Module#name` is still nil, and `to_s`/`inspect` are still the address form:
# the fallback is `className`'s, and `name` does not go through it
show("name") { Class.new.name.inspect }
show("mod name") { Module.new.name.inspect }
show("to_s") { Class.new.to_s }
show("inspect") { Class.new.inspect }
show("mod to_s") { Module.new.to_s }

# the coercion and comparison families (L123's messages, this session's names)
show("plus") { 0 + anon.new }
show("float plus") { 0.5 + anon.new }
show("modulo") { 0 % anon.new }
show("relop") { 1 < anon.new }
show("str plus") { "abc" + anon.new }

# dispatch, constants, freezing, allocation
show("nomethod") { anon.new.frobnicate }
show("nomethod on the class") { Class.new.frobnicate }
show("const") { anon::Nope }
show("frozen") do
  o = anon.new
  o.freeze
  o.instance_variable_set(:@a, 1)
end
show("superclass") { Class.new(anon.new) }

# an instance of an anonymous class renders as `#<#<Class:0x…>:0x…>` — the
# default repr nests the class's own address form (both twins: `Repr` and
# `__inspect_slow`)
show("instance to_s") { anon.new.to_s }
show("instance inspect") { anon.new.inspect }
show("instance interpolated") { "#{anon.new}" }
show("instance with ivars") do
  o = anon.new
  o.instance_variable_set(:@a, 1)
  o.inspect
end
show("in a container") { [anon.new].join(",") }

# `Exception.new` with no message uses the class name as the message
show("exception message") { anon_err.new.message }
show("raised") { raise anon_err }

# the four prelude messages that used `.class.name`, where nil made a *different*
# error (`no implicit conversion of nil into String`)
show("to_ary conversion") do
  k = Class.new { def to_ary = 1 }
  a, b = k.new
  [a, b].inspect
end
show("to_str conversion") do
  k = Class.new { def to_str = 1 }
  String.try_convert(k.new)
end
# `Array#to_h`'s message carries the element index; `Enumerable#to_h`'s does not [V]
show("to_h element") { [anon.new].to_h }

# an anonymous class named by a constant assignment is named from then on (L72),
# the same two shapes then report the constant, not an address
Named = Class.new
show("named by assignment") { Named.name }
show("named, coerced") { 0 + Named.new }
