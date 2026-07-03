# ADVERSARIAL: || must evaluate its left operand exactly once, even when truthy.
# A naive `a || b => if a then a else b` re-evaluates `a` in the then branch.
# Correct stdout: "a=5"   Buggy (double-eval) stdout: "aa=5"
def m(tag, val)
  print(tag)
  val
end

r = m("a", 5) || m("b", 9)
print("=")
print(r.inspect)
