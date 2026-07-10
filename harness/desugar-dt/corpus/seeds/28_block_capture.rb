# Block-capture param `&blk` (C22): a literal block attached to the call is reified into
# a Proc bound to the param. It must be indistinguishable from yield/block_given? — the
# same block is seen whether the callee names it (`&blk`) or yields to it implicitly.
def cap(&blk)
  return "none" if blk.nil?          # no block passed -> nil
  print("given=#{block_given?};")    # block_given? true when a block was passed
  a = blk.call(10)                   # calling the reified Proc
  b = yield 20                       # ...sees the SAME block as yield
  a + b
end

r1 = cap { |x| print("body#{x};"); x + 1 }
r2 = cap                             # no block -> "none", blk is nil
print("r1=#{r1};r2=#{r2}")

# block-capture alongside positional params, and an anonymous `&` capture param
def mixed(a, b, &blk)
  blk.call(a + b)
end
print(";mixed=#{mixed(3, 4) { |s| s * 2 }}")

def anon(&)                          # anonymous block param binds but is unnamed
  block_given? ? "has" : "no"
end
print(";anon=#{anon { 1 }}")
r1
