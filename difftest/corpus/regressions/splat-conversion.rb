def show(label)
  p [label, yield]
rescue StandardError => e
  p [label, e.class, e.message]
end
class Spread
  def to_a
    puts :to_a
    [2, 3]
  end
end
class PrivateSpread
  private
  def to_a = [4, 5]
end
class MissingSpread
  def method_missing(name, *args)
    puts name
    name == :to_a ? [6, 7] : super
  end
end
class NilSpread
  def to_a = nil
end
class WrongSpread
  def to_a = "wrong"
end
class RejectSpread < Spread
  def respond_to?(name, include_private = false)
    p [name, include_private]
    false
  end
end
class MissingFailure
  def method_missing(name, *args) = super
end
class PromisedFailure < MissingFailure
  def respond_to_missing?(name, include_private = false) = true
end
show(:array) { [1, *Spread.new, 8] }
show(:private) { [*PrivateSpread.new] }
show(:missing) { [*MissingSpread.new] }
show(:nil_result) { s = NilSpread.new; [*s].first.equal?(s) }
show(:wrong_result) { [*WrongSpread.new] }
show(:rejected) { s = RejectSpread.new; [*s].first.equal?(s) }
show(:missing_failure) { s = MissingFailure.new; [*s].first.equal?(s) }
show(:promised_failure) { [*PromisedFailure.new] }
def collect(*args) = args
def effect(n)
  p [:effect, n]
  n
end
show(:call_order) { collect(effect(1), *Spread.new, effect(8)) }
def yielding(s) = yield(1, *s, 8)
show(:yield) { yielding(Spread.new) { |*args| args } }
class Parent
  def args(*xs) = xs
end
class Child < Parent
  def args(s) = super(1, *s, 8)
end
show(:super) { Child.new.args(Spread.new) }
show(:hash) { [*{a: 1, b: 2}] }
h = {a: 1}
def h.each = raise("must not dispatch each")
show(:hash_native) { [*h] }
def h.to_a = [:override]
show(:hash_override) { [*h] }
show(:range) { [*(2..4)] }
class Range
  def to_a = [:range_override]
end
show(:range_override) { [*(2..4)] }
md = /(a)(b)?/.match("a")
show(:match_data) { [*md] }
def md.to_a = [:match_override]
show(:match_override) { [*md] }
a = [1, 2]
def a.to_a = raise("must bypass to_a")
def a.respond_to?(*args) = raise("must bypass respond_to?")
show(:array_bypass) { [*a] }
class NilClass
  def to_a = raise("nil splat must bypass to_a")
end
show(:nil_bypass) { [1, *nil, 2] }
class Integer
  def to_a = [self, self + 1]
end
show(:immediate) { [*3] }
show(:throw) do
  s = Object.new
  def s.to_a = throw(:conversion, :escaped)
  catch(:conversion) { [*s] }
end
