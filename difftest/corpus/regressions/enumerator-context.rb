# L280: nested external iteration shares heap/captures and isolates exceptions.
state = []
inner = Enumerator.new { |y| state << :inner; y << 10; y << 20; :inner_done }
outer = Enumerator.new do |y|
  state << :outer
  y << inner.next
  state << :resumed
  y << inner.next
  :outer_done
end
p [outer.next, state]
state << :caller
p [outer.next, state]
p(loop { outer.next })
e = Enumerator.new do |y|
  p [:producer_before, $!]
  begin
    raise "inside"
  rescue => err
    y << err.message
    p [:producer_after, $!.message]
  end
end
begin
  raise "outside"
rescue
  p [e.next, $!.message]
  p(loop { e.next })
  p $!.message
end
ary = [1, 2]
e = ary.each
p e.next
ary[1] = 9
ary << 3
p [e.next, e.next]
