# M7 destructuring (C29): nested massign targets `(a,b),c = …` and destructuring block
# params `|(a,b)|`. A nested group coerces its value to an array (to_ary-or-wrap), just like
# a single-RHS massign.
(a, b), c = [[1, 2], 3]
print("nest=#{[a, b, c].inspect};")
(x, y), z = [5, 3]              # 5 is not array-convertible -> [5] -> x=5, y=nil
print("nestwrap=#{[x, y, z].inspect};")

# Deeper nesting + a rest inside a nested group.
(p1, (q, r)), s = [[1, [2, 3]], 4]
print("deep=#{[p1, q, r, s].inspect};")

# Destructuring block params.
sums = [[1, 2], [3, 4]].map { |(m, n)| m + n }
print("blk=#{sums.inspect};")
nested_blk = [[1, [2, 3]]].map { |(m, (n2, o))| [m, n2, o] }
print("blknest=#{nested_blk.inspect};")

# Mixed positional + destructure block param, and a rest inside a destructure.
mixed = [[9, [1, 2, 3]]].map { |first, (head, *tail)| [first, head, tail] }
print("mixed=#{mixed.inspect}")
[a, b, c]
