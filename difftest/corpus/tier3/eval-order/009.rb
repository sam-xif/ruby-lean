$o = []
def n(x); $o << x; x; end
h = Hash.new(0)
result = "#{h[n(:k)] += n(5)}|#{h[n(:k)] += n(3)}"
puts result
p h
p $o
