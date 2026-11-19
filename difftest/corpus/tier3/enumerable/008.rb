# `each_entry` without a block answers an Enumerator.
class C
  include Enumerable

  def each
    yield 1
  end
end

C.new.each_entry
puts "gated, not NoMethodError"
