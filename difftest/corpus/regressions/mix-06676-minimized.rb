def m0
  (a = 0)
  0
end
def m1
  (a = 0)
  0
end
def m2
  (a = 0)
  nil
end
class C0
  def initialize(x, y)
    @x = x
    @y = y
  end
  define_method(:dm0) do
    (a = 0)
    0
  end
  define_method(:dm1) do
    (a = 0)
    nil
  end
  define_singleton_method(:ds0) do
    (a = 0)
    m0()
  end
  def method_missing(name, *args)
    "mm-#{name}"
  end
end
a, b = (0), (0)
(f = (-> {
a, b = (0), (C0.new(0, 0)), (a)
(a = ("v=#{0}" < b))
0
}))
puts(f.call())
