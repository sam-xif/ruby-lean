def n(a, **nil)
  a
end
p n(1)
begin
  n(1, x: 2)
rescue ArgumentError => e
  puts "#{e.class}: #{e.message}"
end
p n(1, {x: 2})
