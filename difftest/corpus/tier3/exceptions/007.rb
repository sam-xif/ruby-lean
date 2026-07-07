begin
  x = 5
  puts "body"
rescue
  puts "rescue"
else
  puts "else #{x}"
  raise "in else"
ensure
  puts "ensure"
end rescue puts "outer caught"
