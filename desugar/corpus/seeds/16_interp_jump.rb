# control-flow jump inside string interpolation -> linearization hoists it.
# The interpolation's earlier effects run, then the jump fires; the rest is abandoned.
out = []
i = 0
while i < 3
  i += 1
  out << "before"
  "x#{ out << "in"; next }"    # unconditional `next` inside #{}: fires here
  out << "after"               # unreachable
end

# conditional jump inside #{} stays inline (still yields a value when not jumping)
j = 0
tally = []
while j < 3
  j += 1
  s = "v#{ tally << j; break if j == 2 }"
  tally << s
end
p [out, tally]
