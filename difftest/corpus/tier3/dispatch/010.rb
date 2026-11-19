# CRuby's `range_min`/`range_max` answer without iterating: a Float range has
# both a minimum and a maximum, and an exclusive range whose end is not an
# Integer has no maximum at all. `Enumerable#max` steps with `succ` instead —
# which Float does not have — and `(1...2.5).max` would answer 2.
[(1..5), (1...5), (1.5..2.5), (1.5...2.5), (1...2.5), (1.5...3), (2..1), (1...1),
 ("a".."c")].each do |r|
  %i[min max minmax].each do |m|
    begin
      puts "#{r.inspect}.#{m} = #{r.public_send(m).inspect}"
    rescue TypeError => e
      puts "#{r.inspect}.#{m} !! #{e.class}: #{e.message}"
    end
  end
end

# With a block, `min`/`max` are `Enumerable`'s, which the receiver still owns.
puts (1..5).max { |a, b| -(a <=> b) }.inspect
puts (1..5).min { |a, b| -(a <=> b) }.inspect
puts (1.5..2.5).minmax.inspect
