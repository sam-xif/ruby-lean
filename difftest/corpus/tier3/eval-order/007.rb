$o = []
class Store
  def initialize(n); @n = n; end
  def x=(v); $o << "set#{@n}=#{v}"; end
end
def lhs(n); $o << "L#{n}"; Store.new(n); end
def r(n); $o << "R#{n}"; n; end
lhs(1).x, lhs(2).x = r(10), r(20)
p $o
