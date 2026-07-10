# ADVERSARIAL (eval order): a writer-call `recv[idx] = rhs` / `recv.attr = rhs`
# evaluates receiver, then index args, then RHS — each exactly once, RHS LAST — and
# the expression's value is the RHS, not the setter's return. The temp-based
# desugaring must keep `(t = rhs)` in the LAST argument slot; a leading-temp form
# (`t = rhs; recv[...] = t`) would hoist RHS ahead of a side-effecting receiver/index
# and reorder the trace. Seed 23 uses a plain-local receiver; this one makes the
# receiver side-effecting too, pinning receiver-before-index.
def tag(s, v); print("#{s};"); v; end

class Store
  def initialize; @h = {}; end
  def []=(k, v); @h[k] = v; return :setter_ret; end   # writer returns non-v on purpose
  def get(k); @h[k]; end
  def attr=(v); @a = v; return 999; end
  def attr; @a; end
end

s = Store.new
r1 = (tag("recv1", s)[tag("idx", :k)] = tag("rhs1", 42))
print("r1=#{r1};stored=#{s.get(:k)};")     # order: recv1; idx; rhs1;  r1 = 42 (RHS)
r2 = (tag("recv2", s).attr = tag("rhs2", 7))
print("r2=#{r2};attr=#{s.attr};")          # order: recv2; rhs2;  r2 = 7 (RHS)
