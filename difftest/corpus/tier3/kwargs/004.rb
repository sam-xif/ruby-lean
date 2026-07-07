def m(a, b, c:)
  [a, b, c]
end
begin
  m(1, c: 3)
rescue ArgumentError => e
  puts "#{e.class}: #{e.message}"
end
p m(1, 2, c: 3)
