# Every argument form CRuby's `num_step` accepts for `Integer#step`, and the
# errors it raises. The model used to take two required positional arguments and
# keep an Integer receiver when an argument was a Float.
def show(label)
  print label, ": "
  begin
    print yield.inspect
  rescue => e
    print "#{e.class}: #{e.message}"
  end
  puts
end

show("default step") { 1.step(5) { |i| print i } }
show("positional step") { 1.step(5, 2) { |i| print i } }
show("keyword to") { 1.step(to: 5) { |i| print i } }
show("keyword by and to") { 1.step(by: 2, to: 5) { |i| print i } }
show("returns the receiver") { 1.step(5) { |i| } }
show("descending") { 5.step(1, -2) { |i| print i } }
show("float limit promotes") { 1.step(5.5) { |x| print x, "," } }
show("float step promotes") { 1.step(5, 1.5) { |x| print x, "," } }
show("float rounding tolerance") { 1.step(1.9, 0.3) { |x| print x, "," } }
show("float last value is clamped") { (-1).step(-0.3, 0.1) { |x| print x, "," } }
show("descending float") { 1.step(-3, -1.5) { |x| print x, "," } }
show("rational limit and step") { 1.step(Rational(3, 2), Rational(1, 2)) { |x| print x, "," } }
show("nil positional step") { 1.step(5, nil) { |i| print i } }
show("too many arguments") { 1.step(5, 1, 2) { |i| print i } }
show("to given twice") { 1.step(5, to: 3) { |i| print i } }
show("step given twice") { 1.step(5, 1, by: 3) { |i| print i } }
show("unknown keyword") { 1.step(5, zzz: 3) { |i| print i } }
show("break out of the block") { 1.step(10, 2) { |i| break :done if i > 4 } }
