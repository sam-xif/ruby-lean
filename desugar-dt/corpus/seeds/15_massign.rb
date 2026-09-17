# multiple assignment (explicit value list; swap; arity mismatch; ivar targets)
a, b = 1, 2
a, b = b, a          # swap -> a=2, b=1
x, y, z = 10, 20     # z -> nil
@p, @q = 3, 4
print([a, b, x, y, z, @p, @q].inspect)
