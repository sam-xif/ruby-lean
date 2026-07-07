def t(x); print "[#{x}]"; x; end
class A
  def [](i); print "get(#{i})"; @h ||= {}; @h[i] || 0; end
  def []=(i,v); print "set(#{i},#{v})"; (@h ||= {})[i] = v; end
end
a = A.new
puts
r = (t(a)[t(1)] += t(10))
puts
puts r
