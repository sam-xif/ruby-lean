def m0
  (f = (-> {
(a = nil)
(a = 0)
59
}))
  1.times do |i|
    (a = i)
    return
  end
  0.times do |i|
    (a = i)
  end
  nil
end
def m1(k1: (-2), k2: 3, **o9)
  0.times do |i|
    (a = (0..0))
  end
  19
end
def m2(o1 = 42, o2 = 0, **o9)
  for fi in [0, nil, 31]
    (a = {:k => 2})
  end
  (a = nil)
  (a = ["v=#{nil}v=#{o1}", 11, o1][(-1)])
  []
end
module M0
  def mm0
    i = 0
    begin
      (a = nil)
      i += 1
    end while i < 0
    (a = 100)
    0.times do |i|
      (a = 0)
    end
    0
  end
end
module M1
  def mm0(x, y)
    return
    (a = {:k => nil})
    i = 0
    while i < 0
      (a = 1)
      i += 1
    end
    4
  end
end
class C0
  def initialize(x, y)
    @x = x
    @y = y
  end
  K0 = (-15)
  def im0(x)
    (a = x)
    5
  end
  def method_missing(name, *args)
    "mm-#{name}"
  end
  alias al0 im0
end
class C1
  include M1
  K0 = 62
  define_method(:dm0) do
    (o = C0.new(24, {:k => C0::K0}))
    (f = (->(bx) {
(a = o.im0(o.im0(1)))
(a = 1)
bx
}))
    0
  end
  define_singleton_method(:ds0) do |x|
    for fi in (0..0)
      (a = 2)
    end
    88
  end
  def self.sm0(x)
    (a = x)
    for fi in [0]
      (ix0 = [0])
    end
    12
  end
  def method_missing(name, *args)
    "mm-#{name}"
  end
  def ud0
    nil
  end
  undef ud0
end
class C2 < C0
  include M0
  define_method(:dm0) do |x|
    (q = C1.new())
    for fi in (0...0)
      (a = 0)
    end
    (a = 0)
    2
  end
  define_method(:dm1) do
    (a = 1)
    0
  end
  def self.sm0(x)
    begin
      (a = [0, [x, x, x][(-1)], (0..0)][(-1)])
      (x += 0)
      raise('boom')
    rescue => e
      puts("err:#{e}")
      (a = 0)
    end
    i = 0
    begin
      (a = 0)
      (a = 0)
      i += 1
    end while i < 0
    nil
  end
  def self.sm1(x, y)
    (a = (0..0))
    x
  end
  def im0
    (a = 0)
    0
  end
  alias al0 al0
end
class C0
  def rm0
    (a = 0)
    nil
  end
end
(f = (-> {
(a = 0)
0
}))
begin
  (a = 0)
rescue => e
  puts("err:#{e}")
  (a = 0)
else
  puts("else-ran")
  (a = 0)
end
puts("v=#{[]}v=#{C2.new(0, nil)}")
