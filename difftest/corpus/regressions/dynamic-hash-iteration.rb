def show(label)
  p [label, yield]
rescue StandardError => e
  p [label, e.class, e.message]
end
def add_key(hash)
  hash[:new] = 3
end
h = {a: 1, b: 2}
h.each do
  h.each { break :inner_done }
  show(:nested_lock_survives_inner_break) { add_key(h) }
  h[:b] = 20
  h.delete(:a)
  break :outer_done
end
show(:after_nested_break) { add_key(h) }
p h
h = {a: 1}
begin
  h.each { raise "iteration escaped" }
rescue RuntimeError
  show(:raise_releases_lock) { add_key(h) }
end
h = {a: 1}
p catch(:iteration) { h.each { throw :iteration, :escaped } }
show(:throw_releases_lock) { add_key(h) }
h = {a: 1}
count = 0
h.each do
  count += 1
  redo if count == 1
  show(:redo_keeps_lock) { add_key(h) }
  next
end
show(:next_releases_lock) { add_key(h) }
h = {a: 1, b: 2}
enum = h.each
p [:suspended, enum.next]
show(:suspended_insertion) { add_key(h) }
show(:suspended_copy) { h.send(:initialize_copy, {z: 9}) }
show(:suspended_update) { h[:b] = 22 }
p [:live_update, enum.next]
begin
  enum.next
rescue StopIteration
  show(:completed_releases_lock) { add_key(h) }
end
h = {a: 1}
first = h.each
second = h.each
p [:first, first.next]
p [:second, second.next]
begin
  first.next
rescue StopIteration
  show(:second_still_holds_lock) { add_key(h) }
end
begin
  second.next
rescue StopIteration
  show(:both_completed) { add_key(h) }
end
h = {a: 1}
enum = Enumerator.new do |y|
  show(:caller_lock_in_producer) { add_key(h) }
  y << :producer_value
end
h.each { p enum.next; break }
show(:caller_lock_released) { add_key(h) }
h = {a: 1}
enum = h.each
p [:abandon_start, enum.next]
enum.rewind
show(:abandoned_lock) { add_key(h) }
p [:new_start, enum.next]
begin
  enum.next
rescue StopIteration
  show(:abandoned_lock_survives_new_completion) { add_key(h) }
end
empty = {}
empty.each { :unreachable }
show(:empty_unlocked) { add_key(empty) }
nil
