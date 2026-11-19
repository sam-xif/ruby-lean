# `chunk` answers an Enumerator.
class C
  include Enumerable

  def each
    yield 1
    yield 2
  end
end

C.new.chunk { |x| x.even? }
puts "gated, not NoMethodError"
