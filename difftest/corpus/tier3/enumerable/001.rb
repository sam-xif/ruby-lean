# `cycle` without a block answers an Enumerator, which the model does not build.
class C
  include Enumerable

  def each
    yield 1
    yield 2
  end
end

C.new.cycle
puts "gated, not NoMethodError"
