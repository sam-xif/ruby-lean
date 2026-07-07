def yield_from_ensure
  yield :try
ensure
  puts "in ensure"
end

def outer
  yield_from_ensure do |t|
    puts "block got #{t}"
    return :returned_through_ensure
  end
  puts "unreachable"
end
p outer
