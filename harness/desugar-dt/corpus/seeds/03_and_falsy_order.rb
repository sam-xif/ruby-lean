# ADVERSARIAL: && must evaluate its left operand exactly once, even when falsy.
# A naive `a && b => if a then b else a` re-evaluates `a` in the else branch.
# Correct stdout: "a=nil"   Buggy (double-eval) stdout: "aa=nil"
def m(tag, val)
  print(tag)
  val
end

r = m("a", nil) && m("b", 2)
print("=")
print(r.inspect)
