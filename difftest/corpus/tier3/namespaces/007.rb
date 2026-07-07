COUNT = 0
result = []
begin
  raise "boom"
rescue => e
  local_in_rescue = 99
  result << defined?(local_in_rescue)
ensure
  result << defined?(COUNT)
  result << defined?(local_in_rescue)
end
puts result.map { |x| x.inspect }.join(",")
puts local_in_rescue
result
