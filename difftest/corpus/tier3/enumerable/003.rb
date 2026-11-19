# `chunk_while` answers an Enumerator.
class C
  include Enumerable

  def each
    yield 1
    yield 2
  end
end

C.new.chunk_while { |a, b| b == a + 1 }
puts "gated, not NoMethodError"
