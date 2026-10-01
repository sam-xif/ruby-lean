# A trailing comma distinguishes destructuring from a single target.
class ForYield
  def each
    yield
    yield [1, 2]
    yield 3, 4
    :finished
  end
end
p(for x in ForYield.new; p x; end)
p(for y, in ForYield.new; p y; end)
p [x, y]
class ForTarget
  def run
    for @value, in [[7, 8], 9]
      p @value
    end
    @value
  end
end
p ForTarget.new.run
class ForConvert
  def to_ary
    p :convert
    [10, 11]
  end
end
for z, in [ForConvert.new]
  p z
end
nil
