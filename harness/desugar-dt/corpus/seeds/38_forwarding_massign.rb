# M6c (C28): `...` argument forwarding, and single-RHS massign (to_ary coercion).
def target(a, b, c, key:)
  [a, b, c, key]
end
def fwd(...)
  target(...)               # forward all positional + keyword (+ block) args
end
print("fwd=#{fwd(1, 2, 3, key: 9).inspect};")

def fwd_lead(first, ...)     # `...` after a leading required param
  [first, target(...)]
end
print("fwdlead=#{fwd_lead(0, 1, 2, 3, key: 8).inspect};")

# Single-RHS multiple assignment coerces the RHS via to_ary (else wraps).
a, b = [10, 20]              # array RHS
print("arr=#{[a, b].inspect};")
c, d = 99                    # non-array -> wrapped: c=99, d=nil
print("wrap=#{[c, d].inspect};")
class Pair
  def to_ary; [:p, :q]; end
end
e, f = Pair.new              # to_ary honored
print("toary=#{[e, f].inspect};")
g, *h = [1, 2, 3, 4]         # single-RHS with a rest target
print("rest=#{[g, h].inspect};")

# The VALUE of a massign is the RHS *as written*, not the distributed/coerced array:
# a single-RHS massign yields the raw RHS (`(* = 1)` is 1, not [1]).
print("val_single=#{(* = 1).inspect};")     # 1  (anonymous splat target, raw RHS value)
print("val_rest=#{(*z = 7).inspect};")       # 7  (z becomes [7], but the value is 7)
print("val_list=#{(p, q = 1, 2).inspect}")   # [1, 2]  (value list -> the array)
[a, b]
