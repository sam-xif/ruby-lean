begin
  File.read("/tmp/missing.txt")
rescue SystemCallError => e
  puts e.class
end
