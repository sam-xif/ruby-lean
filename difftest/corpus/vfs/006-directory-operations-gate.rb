[
  -> { File.read("/tmp/vfsdata") },
  -> { File.size("/tmp/vfsdata") },
  -> { File.write("/tmp/vfsdata", "x") },
].each do |operation|
  begin
    operation.call
  rescue SystemCallError => e
    puts e.class
  end
end
