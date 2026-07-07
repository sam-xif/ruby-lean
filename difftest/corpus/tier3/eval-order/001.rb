$log = []
def f(n); $log << n; n; end
def g(a,b,c); print "call "; a+b+c; end
x = g(f(1), f(2), f(3))
puts $log.join(",")
puts x
h = { f(4) => f(5), f(6) => f(7) }
puts $log.join(",")
puts h.values_at(4,6).join(",")
