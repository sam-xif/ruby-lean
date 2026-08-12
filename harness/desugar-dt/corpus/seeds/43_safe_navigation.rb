# C34 safe navigation `recv&.m`. This was silently dropped — `x&.to_h` desugared to a
# plain `x.to_h` — which is invisible for a method nil does not answer (both sides raise
# NoMethodError) and wrong for one it does. `nil&.to_h` is nil; `nil.to_h` is `{}`.
x = nil
print("nil=#{x&.to_h.inspect},#{x&.to_s.inspect},#{x&.to_a.inspect};")
y = [1, 2]
print("arr=#{y&.length};")

# The guard is `nil?`, not truthiness: `false&.to_s` really does call `to_s`.
f = false
print("false=#{f&.to_s.inspect};")

# The receiver is evaluated exactly once, and when it is nil the *arguments are
# not evaluated at all* — which is why this cannot be `t && t.m(args)` with `t`
# re-evaluated, nor a plain send.
def recv(v)
  print("recv;")
  v
end

def arg(n)
  print("arg#{n};")
  n
end

print("nil-args=#{recv(nil)&.fetch(arg(1)).inspect};")
print("live-args=#{recv([9, 8])&.fetch(arg(1)).inspect};")

# Chained, and mixed with an ordinary send.
h = { a: { b: 1 } }
print("chain=#{h[:a]&.fetch(:b)},#{h[:zz]&.fetch(:b).inspect};")

# With a block, and as a statement whose value is discarded.
print("blk=#{y&.map { |e| e * 2 }.inspect};")
nil&.each { |e| print("never;") }
print("done")
[x&.to_h, y&.length]
