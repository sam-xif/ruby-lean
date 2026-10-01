def show(label)
  p [label, yield]
rescue StandardError => e
  p [label, e.class, e.message]
end
class Pair
  def to_ary
    puts :to_ary
    [1, 2]
  end
end
class PrivatePair
  private
  def to_ary = [3, 4]
end
class MissingPair
  def method_missing(name, *args)
    puts name
    name == :to_ary ? [5, 6] : super
  end
end
class NilPair
  def to_ary = nil
end
class WrongPair
  def to_ary = false
end
class RejectPair < Pair
  def respond_to?(name)
    p name
    false
  end
end
show(:proc) { proc { |a,b| [a,b] }.call(Pair.new) }
show(:private) { proc { |a,b| [a,b] }.call(PrivatePair.new) }
show(:missing) { proc { |a,b| [a,b] }.call(MissingPair.new) }
show(:nil_result) { s = NilPair.new; proc { |a,b| [a.equal?(s), b] }.call(s) }
show(:wrong_result) { proc { |a,b| [a,b] }.call(WrongPair.new) }
show(:rejected) { s = RejectPair.new; proc { |a,b| [a.equal?(s), b] }.call(s) }
show(:single) { s = Pair.new; proc { |a| a.equal?(s) }.call(s) }
show(:rest_only) { s = Pair.new; proc { |*a| a.first.equal?(s) }.call(s) }
show(:trailing_comma) { proc { |a,| a }.call(Pair.new) }
show(:rest_and_post) { proc { |a,*b,c| [a,b,c] }.call(Pair.new) }
show(:lambda) { lambda { |a,b| [a,b] }.call(Pair.new) }
show(:lambda_rest) { s = Pair.new; lambda { |a,*b| [a.equal?(s),b] }.call(s) }
show(:map) { [Pair.new, PrivatePair.new].map { |a,b| [a,b] } }
show(:each_break) { [Pair.new].each { |a,b| break a+b } }
show(:no_recursive_conversion) do
  inner = Pair.new
  outer = Object.new
  outer.define_singleton_method(:to_ary) { [inner] }
  proc { |a,b| [a.equal?(inner), b] }.call(outer)
end
show(:throw) do
  s = Object.new
  def s.to_ary = throw(:conversion, :escaped)
  catch(:conversion) { proc { |a,b| [a,b] }.call(s) }
end
show(:redo) do
  n = 0
  proc do |a,b; local|
    local = (local || 0) + 1
    p [a,b,local]
    a = 9
    n += 1
    redo if n < 2
    [a,b,local]
  end.call(Pair.new)
end
a = [1, 2]
def a.to_ary = raise("must bypass to_ary")
def a.respond_to?(*args) = raise("must bypass respond_to?")
show(:array_bypass) { proc { |a,b| [a,b] }.call(a) }
class Integer
  def to_ary = [self, self + 1]
end
show(:immediate) { proc { |a,b| [a,b] }.call(7) }
