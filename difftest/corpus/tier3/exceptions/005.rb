begin
  begin
    raise "inner"
  rescue => e
    puts "caught #{e.message}"
    raise
  end
rescue => e2
  puts "reraised #{e2.message}"
end
