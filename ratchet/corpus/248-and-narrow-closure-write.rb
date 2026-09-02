x = 1
f = lambda { x = nil; true }
if x && f.call
  x + 1
else
  2
end
