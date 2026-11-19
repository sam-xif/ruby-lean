def show
  p(yield)
rescue Exception => e
  p [e.class, e.message]
end

s = Struct.new(:a, :b)
show { s.new(1, 2).dig(:a) }
show { s.new(1, 2).dig(1) }
show { s.new(1, 2).dig(-1) }
show { s.new(1, 2).dig("b") }
show { s.new(1).dig(:zz) }
show { s.new(1).dig(5) }
show { s.new(1).dig(-3) }
show { s.new(1).dig }
show { {x: s.new(1, 2)}.dig(:x, :b) }
show { s.new({k: 5}).dig(0, :k) }
show { s.new([1, 2]).dig(:a, 1) }
show { s.new(1, 2).dig(:a, :x) }
