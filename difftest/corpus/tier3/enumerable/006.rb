# `slice_when` answers an Enumerator.
class C
  include Enumerable

  def each
    yield 1
    yield 2
  end
end

C.new.slice_when { |a, b| b != a + 1 }
puts "gated, not NoMethodError"
