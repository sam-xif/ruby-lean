result = []
[10,20,30].each do |x|
  begin
    break if x == 20
    result << x
  ensure
    result << -x
  end
end
puts result.inspect
