# float literal; range/rational/imaginary -> constructor sends; op-assign across namespaces
x = 10
x += 5          # local op-assign  -> 15
x *= 2          # -> 30
@t = 0
@t += x         # ivar op-assign   -> 30
$g = 5
$g -= 2         # gvar op-assign   -> 3
r = (1..5)
f = 2.5
print([x, @t, $g, r.to_a, (f + 0.5), 2r, 3i].inspect)
