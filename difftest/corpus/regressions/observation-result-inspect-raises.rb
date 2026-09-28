o = Object.new
def o.inspect
  puts :inspection_started
  raise "inspection failed"
ensure
  puts :inspection_ensured
end
o
