def m
  begin
    return 1
  ensure
    return 2
  end
end
puts m
