def m
  begin
    return 1
  ensure
    puts "ensure ran"
  end
end
puts m
