obj = "hello"
def obj.shout
  upcase + "!"
end
puts obj.shout
puts obj.singleton_methods.inspect
other = "hello"
begin
  other.shout
rescue NoMethodError
  puts "no shout on other"
end
