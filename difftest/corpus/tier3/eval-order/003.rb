def v(tag); print "#{tag} "; tag; end
a, b, (c, d), *e = v(1), v(2), [v(3), v(4)], v(5), v(6)
puts
puts [a,b,c,d,e.inspect].join(",")
def pair; print "pairing "; return v(:x), v(:y); end
p, q = pair
puts
puts "#{p},#{q}"
print "swap: "
m, n = 10, 20
m, n = n, m
puts "#{m},#{n}"
