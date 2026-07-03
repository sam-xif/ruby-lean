# ||= / &&= across local/ivar/gvar (unset read is nil, no error)
@x ||= 5        # unset ivar -> assign 5
@x ||= 9        # truthy -> stays 5
$y ||= 7        # unset gvar -> assign 7
a = 1
a &&= a + 10    # truthy -> assign 11
b = nil
b &&= 99        # falsy -> stays nil
print([@x, $y, a, b].inspect)
