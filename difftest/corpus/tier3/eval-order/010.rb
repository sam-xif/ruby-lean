def tag(s, v); print("#{s};"); v; end

class Store
  def initialize; @h = {}; end
  def []=(k, v); @h[k] = v; return :setter_ret; end
  def get(k); @h[k]; end
  def attr=(v); @a = v; return 999; end
  def attr; @a; end
end

s = Store.new
r1 = (tag("recv1", s)[tag("idx", :k)] = tag("rhs1", 42))
print("r1=#{r1};stored=#{s.get(:k)};")
r2 = (tag("recv2", s).attr = tag("rhs2", 7))
print("r2=#{r2};attr=#{s.attr};")
puts
