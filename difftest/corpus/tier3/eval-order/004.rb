def note(s); print "<#{s}>"; s; end
def risky; print "try "; raise "boom"; end
begin
  puts "str: #{note('a')}-#{note('b')}-#{note('c')}"
  x = 0
  begin
    x = risky
  ensure
    print "ensure "
    x ||= note('fallback')
  end
rescue => ex
  puts
  puts "#{ex.class}: #{ex.message} x=#{x}"
end
puts [1,2].map { |i| note("m#{i}") }.join(",")
