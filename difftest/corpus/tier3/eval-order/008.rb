$o = []
def v(x); $o << x; x; end
class C
  def foo(a, b, c); $o << "foo"; [a, b, c]; end
end
def obj; $o << "recv"; C.new; end
result = obj.foo(v(1), v(2), v(3))
p result
p $o
