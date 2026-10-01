# L280: internal iteration calls the saved method anew, independently of next.
e = 4.times
p [e.class, e.is_a?(Enumerable), e.size, e.inspect, e.each.equal?(e)]
p [e.map { |x| x * 3 }, e.take(2), e.to_a, (-2).times.to_a, (-2).times.size]
p e.next
p e.map { |x| x + 10 }
p e.next
obj = Object.new
def obj.walk(n)
  yield n
  yield n + 1
  :finished
end
e = obj.enum_for(:walk, 3) { |n| n + 2 }
p [e.size, e.to_a, e.each { |x| p x }]
def obj.walk(n)
  yield n * 10
  :changed
end
p e.to_a
p e.each { |x| break [:break, x] }
ary = [1, 2]
e = ary.each
ary << 3
p [e.size, e.map { |x| x + 1 }]
class Array
  def each
    yield :overridden
    :return_value
  end
end
p [e.next, e.each { |x| p x }]
