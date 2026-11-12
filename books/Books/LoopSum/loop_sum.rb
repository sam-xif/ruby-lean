# Sums the integers below 100 with a while loop. The proof in Proof.lean is
# that, every time control reaches HERE, y is the sum of the integers in 0...x.
x = 0
y = 0
while x < 100
  # HERE
  y += x
  x += 1
end
puts y
y
