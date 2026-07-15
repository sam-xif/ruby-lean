# M7 (C29): indexed/attr op-assign (once-only receiver/index), numbered block params,
# single-target implicit-rest massign, do-while.

# Indexed op-assign: receiver + index evaluated ONCE (side effects fire once).
def tr(x); print("#{x};"); x; end
h = Hash.new(0)
arr = [10, 20, 30]
h[tr(:k)] += 5                    # recv h, index :k once; h[:k] = 0 + 5
print("idxop=#{h.inspect};")
arr[tr(1)] *= 2                   # arr[1] = 20 * 2
print("idxmul=#{arr.inspect};")
# A splat index (`a[*idx] += v`): the splatted array is cached once and re-splatted.
grid = { [0, 0] => 5 }
key = [0, 0]
grid[*[key]] += 10               # index is *[key] -> the single key [0,0]
print("splatidx=#{grid[[0, 0]]};")

cfg = {}
cfg[:a] ||= "default"            # or-write: writes since absent
cfg[:a] ||= "ignored"            # already set: no write
print("idxor=#{cfg.inspect};")

# Attribute op-assign.
Box = Struct.new(:v)
b = Box.new(1)
b.v += 41
print("attrop=#{b.v};")
b.v &&= 100                       # and-write: v truthy -> assigns
print("attrand=#{b.v};")

# Numbered block params.
print("num=#{[1, 2, 3].map { _1 * _1 }.inspect};")
print("num2=#{[[1, 2], [3, 4]].map { _1 + _2 }.inspect};")

# Single-target / implicit-rest massign.
a, = [7, 8, 9]                    # implicit rest discards the tail
print("implrest=#{a};")

# do-while: body runs once even though the condition is false.
n = 0
begin
  n += 1
end while n < 0
print("dowhile=#{n}")
n
