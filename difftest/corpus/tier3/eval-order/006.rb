$log = []
def note(tag, v)
  $log << tag
  v
end
h = { a: 1 }
h[:a] ||= note(:skipA, 99)
h[:b] ||= note(:runB, 2)
h[:a] &&= note(:runA, 3)
h[:c] &&= note(:skipC, 4)
p h
p $log
