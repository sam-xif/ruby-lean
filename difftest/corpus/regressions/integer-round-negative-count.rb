# `Integer#round`/`#ceil`/`#floor`/`#truncate` with a negative count take the
# receiver's magnitude first (CRuby's `rb_int_round`, `_floor`, `_ceil`,
# `_truncate`), so all four rules are one-sided in `|n|`: `round` is half away
# from zero on both sides, `truncate` moves toward zero, and the sign only
# selects which multiple of the granularity is wanted. Reading the remainder of
# a floor division as if it were signed stepped a negative receiver the wrong
# way: `-195.round(-1)` answered -210, `-195.truncate(-1)` answered -200.

# The whole surface, both signs, at every granularity up to 10^4.
(-40..40).each do |n|
  (-1..-4).each do |d|
    %i[round ceil floor truncate].each do |m|
      puts "#{n}.#{m}(#{d}) = #{n.public_send(m, d)}"
    end
  end
end

# The rounding boundary itself: a bare value below the half goes to zero, the
# half goes away from zero, and one above it goes to the next multiple.
[-195, -155, -150, -145, -105, -100, -95, -55, -50, -45, -15, -10, -5, -1, 0,
 1, 5, 10, 15, 45, 50, 55, 95, 100, 105, 145, 150, 155, 195].each do |n|
  %i[round ceil floor truncate].each do |m|
    puts "#{n}.#{m}(-1) = #{n.public_send(m, -1)}, -2 = #{n.public_send(m, -2)}"
  end
end

# A count past the value: `round` and `truncate` answer zero rather than
# materializing the granularity, while `floor`/`ceil` still answer a multiple of
# it. Also every receiver that is already a multiple, in both directions.
[0, 1, -1, 5, -5, 500, -500, 1234, -1234].each do |n|
  [-5, -6, -10, -19, -20, -21, -100].each do |d|
    %i[round ceil floor truncate].each do |m|
      puts "#{n}.#{m}(#{d}) = #{n.public_send(m, d)}"
    end
  end
end

# A non-negative count is the receiver, and the bare forms are all the receiver.
puts [555.round, 555.ceil, 555.floor, 555.truncate, (-555).round, (-555).truncate].inspect
puts [555.round(0), 555.round(1), 555.round(100), (-555).floor(0), (-555).truncate(50)].inspect
