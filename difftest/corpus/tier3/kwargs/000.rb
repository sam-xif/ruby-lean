def foo(a:, b:)
  [a, b]
end
h = {a: 1, b: 2}
begin
  p foo(h)
rescue ArgumentError => e
  puts "#{e.class}: #{e.message}"
end
p foo(**h)
