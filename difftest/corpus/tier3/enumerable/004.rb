# `slice_before` answers an Enumerator (with a pattern or a block).
class C
  include Enumerable

  def each
    yield 1
    yield 2
  end
end

C.new.slice_before(1)
puts "gated, not NoMethodError"
