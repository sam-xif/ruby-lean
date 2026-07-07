def side(tag, val); print "#{tag} "; val; end
@a = nil
puts "---||=---"
r1 = (@a ||= side("rhs1", 5))
r2 = (@a ||= side("rhs2", 99))
puts
puts "a=#{@a} r1=#{r1} r2=#{r2}"
@b = 1
puts "---&&=---"
r3 = (@b &&= side("rhs3", 7))
@b = nil
r4 = (@b &&= side("rhs4", 8))
puts
puts "b=#{@b.inspect} r3=#{r3} r4=#{r4}"
