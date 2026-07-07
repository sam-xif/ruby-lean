class MyErr < StandardError; end
begin
  raise MyErr, "x"
rescue ArgumentError
  puts "arg"
rescue MyErr
  puts "my"
rescue StandardError
  puts "std"
end
