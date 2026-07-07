def risky(a:, b:)
  raise "boom"
ensure
  puts "ensure a=#{a} b=#{b}"
end
begin
  risky(a: 1, b: 2)
rescue RuntimeError => e
  puts e.message
end
