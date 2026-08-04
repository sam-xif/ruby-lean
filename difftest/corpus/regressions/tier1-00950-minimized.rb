class C0
  def initialize(x, y)
    @x = x
    @y = y
  end
  attr_accessor :x
  def self.sm0
    (a = 0)
    0
  end
  def self.sm1
    (a = 0)
    0
  end
  def method_missing(name, *args)
    "mm-#{name}"
  end
end
class C1
end
(a = C0.new(0, 0))
puts(a)
