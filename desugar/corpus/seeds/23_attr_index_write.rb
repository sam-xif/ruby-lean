# ADVERSARIAL: an assignment-call (`obj[i] = v`, `obj.attr = v`) has TWO obligations a
# naive `obj.[]=(i, v)` send gets wrong:
#   (a) the VALUE of the expression is the RHS `v`, NOT the writer method's return;
#   (b) receiver, then index args, then RHS are evaluated left-to-right, each exactly once.
class Box
  def initialize; @h = {}; end
  def [](k); @h[k]; end
  def []=(k, v); @h[k] = v; return :ignored_return; end   # writer returns non-v on purpose
  def val=(v); @b = v; return 999; end
  def val; @b; end
end

def side(tag, v)
  print("#{tag};")
  v
end

b = Box.new
# value of `b[k] = v` must be 7 (the RHS), not :ignored_return.
r = (b[side("recv-k", :a)] = side("rhs", 7))
print("val=#{r.inspect};")           # eval order: recv-k; rhs; then val=7
print("stored=#{b[:a]};")

# attribute writer: value is the RHS (10), not 999.
r2 = (b.val = 10)
print("attr=#{r2};")
