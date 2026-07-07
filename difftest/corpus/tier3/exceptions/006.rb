def m
  begin
    raise "original"
  ensure
    raise "from ensure"
  end
rescue => e
  puts e.message
end
puts m
