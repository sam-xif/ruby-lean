# `Range#cover?` orders with `<=>` (CRuby's `r_cover_p` over `r_less`), so an
# argument from a class the endpoint cannot be ordered against is *outside* the
# range: an answer, not a raised `NoMethodError`/`ArgumentError`.
[(1..2), (1...2), ("a".."c"), (:a..:c)].each do |r|
  [nil, :a, "x", 1, 3, 1.5, [3, :a], [1]].each do |arg|
    puts "#{r.inspect}.cover?(#{arg.inspect}) = #{r.cover?(arg).inspect}"
    puts "#{r.inspect} === #{arg.inspect} = #{(r === arg).inspect}"
  end
end

# A Range argument asks a different question — is the whole subrange covered? —
# and `===` does not: CRuby's `range_eqq` is `r_cover_p`, the scalar half, so
# `(1..10) === (2..3)` is false while `cover?` is true. Both endpoints of the
# argument must be covered, an empty argument range covers nothing, and an
# exclusive argument end past this range's end still counts when the argument's
# `max` is covered.
[[1..10, 2..3], [1..10, 1...10], [1..10, 1..10], [1..10, 2..30], [1..10, 0..10],
 [1..2, 2..1], [1..2, 1...1], [1..10, 1...11], [1..10, 10...11],
 [1..10, 10..10], [1...10, 9..10], [1...10, 9...10], [1...10, 10...10],
 [1..10, "a".."b"], [1..10, :a..:c], [1..2, 1.5...2.5], [1..2, 1...2.5],
 [1..2, 0.5...1.5], [1.0..2.0, 1...2]].each do |r, arg|
  puts "#{r.inspect}.cover?(#{arg.inspect}) = #{r.cover?(arg).inspect}"
  puts "#{r.inspect} === #{arg.inspect} = #{(r === arg).inspect}"
end

# `===` is the question `case`/`when` asks, so a `when` arm whose range cannot
# order one of the values is skipped rather than aborting the program.
[1, :a, 3, 2].each do |x|
  case x
  when (1..2) then puts "#{x.inspect} is low"
  else puts "#{x.inspect} is not low"
  end
end
puts [1, :a, 3, 2].select { |x| (1..2) === x }.inspect
