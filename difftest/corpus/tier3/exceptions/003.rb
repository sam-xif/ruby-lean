attempts = 0
begin
  attempts += 1
  raise "boom" if attempts < 3
  puts "succeeded after #{attempts}"
rescue
  retry if attempts < 3
end
puts attempts
