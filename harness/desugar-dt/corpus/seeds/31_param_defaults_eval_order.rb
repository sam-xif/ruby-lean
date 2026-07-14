# Eval-order adversarial (C25): optional defaults are evaluated LAZILY, left-to-right, in
# the callee scope, at call time, ONLY for the arguments actually omitted. A naive
# desugaring that evaluates all defaults, evaluates them once at def time, or in the wrong
# order would perturb this print-trace even though the returned value could look right.
def f(a, b = (print("b;"); a + 1), c = (print("c;"); b + 1))
  [a, b, c]
end

print("call1;")
r1 = f(1, 9)          # b supplied, c omitted -> prints only "c;"
print("=#{r1.inspect};")

print("call2;")
r2 = f(1)             # b and c omitted -> prints "b;c;" (left-to-right; c sees defaulted b)
print("=#{r2.inspect};")

print("call3;")
r3 = f(1, 2, 3)       # nothing omitted -> no default runs
print("=#{r3.inspect}")
r3
