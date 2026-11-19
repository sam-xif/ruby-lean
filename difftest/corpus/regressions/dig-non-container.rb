h = {a: 1}
begin
  h.dig(:a, :b)
rescue TypeError => e
  p [e.class, e.message]
end
p([[1]].dig(0, 0, 5))

def show
  p(yield)
rescue Exception => e
  p [e.class, e.message]
end
show { {a: false}.dig(:a, 1) }
show { {a: "s"}.dig(:a, 1) }
show { {a: nil}.dig(:a, :b) }
show { {a: {b: [1, {c: 3}]}}.dig(:a, :b, 1, :c) }

class D
  def dig(*a) = "D dug #{a.inspect}"
end
show { {a: D.new}.dig(:a, 1, 2) }

class RT
  def dig(_k) = 5
  def respond_to?(_m, _p = false) = false
end
show { {a: RT.new}.dig(:a, 1) }

class MM
  def method_missing(n, *a) = n == :dig ? "served #{a.inspect}" : super
  def respond_to_missing?(n, _p = false) = n == :dig
end
show { [MM.new].dig(0, 1) }
