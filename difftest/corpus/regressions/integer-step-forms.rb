# `Integer#step` is CRuby's `num_step`: `step(to = nil, by = 1)`, which the
# keywords `to:` and `by:` also set, a missing step of 1, and the whole
# sequence promoted to Float when any of the three numbers is a Float.
# The block form returns the receiver.

seen = []
p 1.step(5) { |i| seen << i }
p seen
seen = []
p 2.step(1) { |i| seen << i }
p seen
seen = []
p 1.step(to: 5) { |i| seen << i }
p seen
seen = []
p 1.step(by: 2, to: 5) { |i| seen << i }
p seen
seen = []
p 1.step(5, by: 2) { |i| seen << i }
p seen
seen = []
p 1.step(5, by: nil) { |i| seen << i }
p seen

# A Float anywhere promotes the sequence, receiver included.
seen = []
p 1.step(5.5) { |x| seen << x }
p seen
seen = []
p 1.step(5, 1.5) { |x| seen << x }
p seen
seen = []
p 3.step(by: -1.5, to: -3) { |x| seen << x }
p seen

# ruby_float_step_size: the count comes from the quotient and its rounding
# error, and the last value is clamped to the limit.
seen = []
p 0.step(0.3, 0.1) { |x| seen << x }
p seen
seen = []
p 0.step(1.0, 0.1) { |x| seen << x }
p seen
seen = []
p 1.step(1.0) { |x| seen << x }
p seen

# The argument errors, with CRuby's messages.
begin
  1.step(5, 0) { |x| nil }
rescue ArgumentError => e
  p [e.class, e.message]
end
begin
  1.step(5, nil) { |x| nil }
rescue TypeError => e
  p [e.class, e.message]
end
begin
  1.step(5, to: 6) { |x| nil }
rescue ArgumentError => e
  p [e.class, e.message]
end
begin
  1.step(5, 2, by: 3) { |x| nil }
rescue ArgumentError => e
  p [e.class, e.message]
end
begin
  1.step(5, foo: 1) { |x| nil }
rescue ArgumentError => e
  p [e.class, e.message]
end
begin
  1.step(1, 2, 3) { |x| nil }
rescue ArgumentError => e
  p [e.class, e.message]
end

# A Rational step stays exact on the generic path.
seen = []
p 1.step(by: Rational(1, 2), to: 3) { |x| seen << x }
p seen
