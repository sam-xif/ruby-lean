# L133 — every implicit Array conversion is `rb_check_array_type`, which
# *dispatches*. Guards the answering sites; the two that gate instead live in
# `to-ary-gates.rb`.
def show(label)
  r = begin
    yield.inspect
  rescue => e
    "#{e.class}: #{e.message}"
  end
  puts "#{label}: #{r.gsub(/0x[0-9a-f]+/, '0xADDR')}"
end

class Good;  def to_ary = [7, 8]; end
class Bad;   def to_ary = "nope"; end
class NilAry; def to_ary = nil; end
class MM;    def method_missing(n, *a); puts "  mm(#{n})"; "nope"; end; end
class MMA;   def method_missing(n, *a); puts "  mm(#{n})"; [7, 8]; end; end
class MMR
  def method_missing(n, *a); puts "  mm(#{n})"; [7, 8]; end
  def respond_to_missing?(n, p = false) = n == :to_a
end
class Plain; end
class HasToA; def to_a = [9]; end

# Array#+ / #concat: the value is used, the method_missing runs, and a
# non-Array answer names the method ("to", not "into").
show("plus-good")     { [1] + Good.new }
show("plus-bad")      { [1] + Bad.new }
show("plus-mm")       { [1] + MM.new }
show("plus-mma")      { [1] + MMA.new }
show("plus-plain")    { [1] + Plain.new }
show("plus-nil")      { [1] + nil }
# a `to_ary` that answers **nil** is a mismatch naming NilClass, not
# "no implicit conversion": `rb_convert_type_with_id` type-checks whatever
# `rb_check_funcall` returned, and only an *absent* method is undefined.
show("plus-nilary")   { [1] + NilAry.new }
show("concat-good")   { [1].concat(Good.new) }
show("concat-bad")    { [1].concat(Bad.new) }
show("concat-mm")     { [1].concat(MM.new) }

# Kernel#Array: to_ary, then to_a, both through rb_check_funcall — so a
# respond_to_missing? that names only :to_a skips the to_ary probe silently.
show("kArray-good")   { Array(Good.new) }
show("kArray-bad")    { Array(Bad.new) }
show("kArray-mm")     { Array(MM.new) }
show("kArray-mma")    { Array(MMA.new) }
show("kArray-mmr")    { Array(MMR.new) }
show("kArray-nilary") { Array(NilAry.new) }
show("kArray-plain")  { Array(Plain.new) }
show("kArray-toa")    { Array(HasToA.new) }
show("kArray-hash")   { Array({ "a" => 1 }) }
show("kArray-range")  { Array(1..3) }
show("kArray-nil")    { Array(nil) }

# flatten and join ask rb_check_array_type what "nested" means.
show("flatten-elem")  { [[1], Good.new].flatten }
show("flatten-none")  { [NilAry.new, 1].flatten }
show("join-elem")     { [Good.new].join(",") }

# puts flattens through to_ary before rendering — the gate L133 retired.
show("puts-good")     { puts(Good.new) }
show("puts-bad")      { puts(Bad.new) }
show("puts-plain")    { puts(Plain.new) }
show("puts-nested")   { puts([1, [2, [3]]]) }

# massign has dispatched all along (the desugarer lowers it to
# `Array.try_convert(x) || [x]`); kept so a change to try_convert shows here.
show("massign-good")  { a, b = Good.new; [a, b] }
show("massign-mm")    { a, b = MM.new; [a, b] }
show("try_convert-nilary") { Array.try_convert(NilAry.new) }
