# `lazy` answers an Enumerator::Lazy, which the boot heap does not have.
class C
  include Enumerable

  def each
    yield 1
    yield 2
  end
end

C.new.lazy
puts "gated, not NoMethodError"
