def m0(x, y)
  (a = 0)
  0
end
module M0
  def mm0
    (a = 0)
    0
  end
end
class C0
  include M0
  def initialize(x, y)
    @x = x
    @y = y
  end
  define_method(:dm0) do |x|
    (a = 0)
    x
  end
  class << self
    def esm0
      (a = 0)
      0
    end
  end
  def self.sm0
    (a = 0)
    0
  end
  def im0
    (a = 0)
    0
  end
  def im1
    (a = 0)
    0
  end
  def method_missing(name, *args)
    "mm-#{name}"
  end
end
class C1
end
class C2
end
class C0
  def rm0
    (a = 0)
    0
  end
end
class C1
  def rm0
    (a = 0)
    0
  end
end
rt0 = 0
begin
  (rt0 += 1)
  if (rt0 <= 1)
    raise('boom')
  end
  nil
rescue => e
  puts("retry:#{e}")
  retry
end
(a = ("hi" + C0.new(0, 0)))
puts(0)
