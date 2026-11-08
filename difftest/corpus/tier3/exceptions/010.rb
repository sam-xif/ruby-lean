begin
  raise EOFError, "end of input"
rescue IOError => e
  puts e.message
  puts e.class
  puts(e.is_a?(StandardError))
end
puts IOError.new("io failure").message
