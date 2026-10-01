# L280: suspension preserves effects, yield arity, feed and completion result.
events = []
e = Enumerator.new(3) do |y|
  events << :started
  a = y.yield
  events << [:first, a]
  b = y.yield(1, 2)
  events << [:second, b]
  y << [3, 4]
  :finished
ensure
  events << :ensure
end
e.feed(:early)
p [e.size, events, e.peek, events, e.peek_values, e.next_values]
p [e.peek, events, e.peek.equal?(e.peek), e.peek_values.equal?(e.peek_values)]
p e.next
e.feed(:fed)
p [e.next_values, events]
begin
  e.next
rescue StopIteration => err
  p [err.class, err.message, err.result, events, err.instance_variables]
  begin
    e.next
  rescue StopIteration => other
    p [other.result, other.equal?(err)]
  end
end
p [e.dup.next, events]
