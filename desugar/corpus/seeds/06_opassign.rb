# x ||= e and x &&= e (local)
y = nil
y ||= 7          # y was falsy -> assigned
z = 3
z ||= 99         # z truthy -> unchanged
w = 5
w &&= w + 1      # w truthy -> assigned w+1
print([y, z, w].inspect)
