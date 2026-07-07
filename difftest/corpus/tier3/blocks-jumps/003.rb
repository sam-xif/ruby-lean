def takes_block
  yield 1, 2, 3
end
takes_block { |a, b| puts "two params: #{a} #{b}" }
takes_block { |a, b, c, d| puts "four params: #{a.inspect} #{b.inspect} #{c.inspect} #{d.inspect}" }
takes_block { |a| puts "one param: #{a}" }

def takes_few
  yield 5
end
takes_few { |a, b, c| puts "few: #{a.inspect} #{b.inspect} #{c.inspect}" }

l = lambda { |a, b| "#{a}-#{b}" }
begin
  l.call(1)
rescue ArgumentError => e
  puts "ArgumentError: #{e.message}"
end
