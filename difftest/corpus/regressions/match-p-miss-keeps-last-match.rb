# `match?` never updates `$~`: a miss leaves the previous match in place [V].
"x" =~ /x/
p "a".match?(/b/)
p $~
p $~ && $~[0]
