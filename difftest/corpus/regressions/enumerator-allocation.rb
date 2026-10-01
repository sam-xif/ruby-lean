# L280: native Generator/Yielder, uninitialized descriptors, sizes and freezing.
e = Enumerator.allocate
p e.inspect
begin
  e.next
rescue => err
  p [err.class, err.message]
end
e.send(:initialize, 2) { |y| y << 1; y << 2; :result }
p [e.size, e.to_a]
y = Enumerator::Yielder.new { |*args| p args; :block_value }
p y.yield(1, 2)
p (y << 3).equal?(y)
g = Enumerator::Generator.new { |yield_to| yield_to << 7; :result }
p [g.each { |x| p x }, g.to_a]
chain = Enumerator::Chain.allocate
p chain.inspect
[:size, :each, :rewind].each do |method|
  begin
    chain.send(method) { |x| x }
  rescue => err
    p [method, err.class, err.message]
  end
end
[-1, 1.5, Float::INFINITY].each { |n| p Enumerator.new(n) {}.size }
count = 1
e = Enumerator.new(-> { count }) { |yield_to| yield_to << count }
p e.size
count = 3
p [e.size, e.next]
e = 2.times.freeze
p [e.size, e.to_a]
begin
  e.next
rescue => err
  p [err.class, err.message]
end
