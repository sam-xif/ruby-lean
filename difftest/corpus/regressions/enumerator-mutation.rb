# L280: native cursors observe mutations while external iteration is suspended.
a = [1, 2]
e = a.each_index
p e.next
a << 3
p [e.next, e.next]
e.rewind
a.pop
p e.to_a
h = {a: 1, b: 2, c: 3}
e = h.each
p e.next
h[:b] = 7
h.delete(:c)
p e.next
begin
  h[:d] = 4
rescue => err
  p [err.class, err.message]
end
p(loop { e.next })
h[:d] = 4
p h
e = h.each_value
p e.next
e.rewind
begin
  h[:e] = 5
rescue => err
  p err.message
end
p h
# Rewind abandons native cleanup too: even the old Hash remains locked.
h = h.dup
# A second iterator holds its lock, then abandoning it leaves another lock.
left = h.each
right = h.each_key
p [left.next, right.next]
left.rewind
begin
  h[:f] = 6
rescue => err
  p err.message
end
right.rewind
begin
  h[:f] = 6
rescue => err
  p err.message
end
p h.size
h = h.dup
h.each { |k, v| break }
h[:g] = 7
begin
  h.each { raise 'stop' }
rescue
  h[:i] = 8
end
p h.size
