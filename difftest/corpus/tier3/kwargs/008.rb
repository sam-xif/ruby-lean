def target(x, y:, z: 9)
  [x, y, z]
end
def forward(*a, **k)
  target(*a, **k)
end
p forward(1, y: 2)
p forward(1, y: 2, z: 3)
begin
  h = {y: 5}
  p forward(1, h)
rescue ArgumentError => e
  puts "#{e.class}: #{e.message}"
end
