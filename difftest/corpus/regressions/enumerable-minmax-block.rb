# #128. `Enumerable#minmax` accepted a comparison block and never called it,
# answering the pair under the default `<=>` instead. The block is a
# comparison over consecutive elements, not a key function, so the program
# pins both the answer and the sequence of comparisons CRuby makes.
$log = []
def cmp(a, b)
  $log << [a, b]
  a <=> b
end
def with_log(xs)
  $log = []
  r = xs.minmax { |a, b| cmp(a, b) }
  [r, $log]
end
p with_log([3, 1, 4, 1, 5])
p with_log([5])
p with_log([])
p with_log([2, 1])
p with_log([1, 2])
p with_log([1, 1])
p with_log([5, 1, 4, 2, 3])

# the block chooses the order
p [1, 2, 3].minmax { |a, b| b <=> a }
p %w[xxx x xxxx xx].minmax { |a, b| a.size <=> b.size }
h = { foo: 0, bar: 1, baz: 2 }
p h.minmax { |a, b| a[1] <=> b[1] }
p 5.times.minmax { |a, b| b <=> a }
p [7, 7, 7].minmax { |a, b| a <=> b }

# a comparison whose result depends on how often it has run: only the
# loop that calls it in CRuby's order answers this the same way
$calls = 0
p([4, 3, 2, 1].minmax { |a, b|
  $calls = $calls + 1
  ($calls % 2 == 1) ? (a <=> b) : (b <=> a)
})
p $calls

# without a block the answer is unchanged
p [[3, 1, 4, 1, 5].minmax, [].minmax, [2, 2].minmax]
