def counter
  n = 0
  inc = -> { n += 1 }
  get = -> { n }
  [inc, get]
end
inc, get = counter
inc.call
inc.call
inc.call
puts get.call

adders = []
(1..3).each { |i| adders << lambda { |x| x + i } }
puts adders.map { |f| f.call(10) }.inspect

shared = 0
blk = proc { shared += 5 }
blk.call; blk.call
puts shared
