def m0
  (f = (-> {
(a = 3)
(a = 0)
nil
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
  74
end
def m2(o1 = 42, o2 = 0, **o9)
  for fi in [0, nil, 31]
    (a = {:k => 15})
  end
  (a = 0)
  (a = nil)
  []
end
module M0
  def mm0
    i = 0
    begin
      (a = 25)
      i += 1
    end while i < 0
    (a = i)
    0.times do |i|
      (a = 0)
    end
    nil
  end
end
module M1
  def mm0(x, y)
    return
    (a = (0..0))
    i = 0
    while i < 0
      (a = 3)
      i += 1
    end
    nil
  end
end
class C0
  def initialize(x, y)
    @x = x
    @y = y
  end
  K0 = (-15)
  def im0(x)
    (a = (-13))
    nil
  end
  def method_missing(name, *args)
    "mm-#{name}"
  end
  alias al0 im0
end
class C1
  include M1
  K0 = 62
  define_method(:dm0) do |x, y|
    (a = 0)
    1
  end
  define_singleton_method(:ds0) do
    rt0 = 0
    begin
      (rt0 += 1)
      if (rt0 <= 3)
        raise('boom')
      end
      nil
    rescue => e
      puts("retry:#{e}")
      retry
    end
    3
  end
  class << self
    def esm0
      0.times do |i|
        (a = (0...0))
        (a = C0::K0)
      end
      0.times do |i|
        next
        next
      end
      (0...0)
    end
  end
  def self.sm0(x)
    (a = x)
    for fi in [0]
      (ix0 = [0])
    end
    12
  end
  def im0
    (a = {:k => 99})
    (a = "v=#{"v=#{a}v=#{6}"}")
    for fi in (0...0)
      (a += 0)
      a, b = (0), (0), (2)
    end
    nil
  end
  def im1(x, y)
    if {:k => 91, :v => [nil, nil, nil]}
      (a = "v=#{nil}v=#{mm0(im0(), 0)}")
      (a = x)
    end
    if 4
      (a = x)
    end
    begin
      (a = 0)
    rescue => e
      puts("err:#{e}")
      (a = 0)
    else
      puts("else-ran")
      (a = x)
    ensure
      puts("ensure-ran")
      (a = 48)
    end
    (!nil)
  end
  def method_missing(name, *args)
    "mm-#{name}"
  end
end
class C2 < C0
  include M0
  K0 = (-19)
  attr_accessor :x, :y
  class << self
    def esm0
      i = 0
      while i < 0
        (a = 1)
        (a = 1)
        i += 1
      end
      (f = (->(bx) {
(a = C0::K0)
(a = nil)
C1.sm0(nil)
}))
      39
    end
  end
  def self.sm0
    (a = 51)
    (0..0)
  end
  def self.sm1(x)
    if 1
      (a = 0)
    end
    [1]
  end
  def im0
    (a = ([3].each() { |bx|
(a = C1.ds0())
(!bx)
}))
    if nil
      (ix1 = {:k => 37})
    else
      (o = C1.new())
    end
    j = 0
    begin
      puts(((@x && @y) && a))
      j += 1
    end while j < 0
    "#{{:k => @x, :v => @x}}"
  end
  def ud0
    nil
  end
  alias al0 y
  undef ud0
end
class C1
  def rm1(x, y)
    (o = C2.new(40, "ok"))
    "ok"
  end
end
class C2
  def rm1
    0.times do |j|
      (a = (nil || true))
      (a -= C1::K0)
    end
    (2..2)
  end
end
a, b = (C2.new(m0(), m2(m1(k3: m1(k1: 75, k3: :k)), m2(m1(k1: m2(47, 49, k2: m0()), k2: m0()), nil), k1: "zap"))), ("ok"), (m1(k3: ""))
puts([" #{b}<#{a}", C1::K0], (C2.new(21, m2(a, k2: m2())) + {:k => b}))
a, b, c = ((m1() || m0())), (a), (["", b, 58][(-1)])
puts(C2.sm1(m1()))
