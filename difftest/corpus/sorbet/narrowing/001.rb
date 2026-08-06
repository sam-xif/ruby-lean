# typed: true
require "sorbet-runtime"
extend T::Sig

class Box
  extend T::Sig

  sig { params(v: T.nilable(String)).void }
  def initialize(v)
    @v = v
  end

  sig { returns(T.nilable(String)) }
  def value
    @v
  end
end

sig { params(b: Box).returns(Integer) }
def size(b)
  return 0 if b.value.nil?
  b.value.length
end

puts size(Box.new("abc"))
