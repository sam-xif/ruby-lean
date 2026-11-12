# The fixture's bytes, through both paths, with the predicates and sizes that
# share the same lookup: /tmp/readme.txt is "hello\n" and /tmp/vfsdata/nums.txt
# is "1\n2\n3\n".
print File.read("/tmp/readme.txt")
print File.read("/tmp/vfsdata/nums.txt")
p File.size("/tmp/readme.txt")
p File.size("/tmp/vfsdata/nums.txt")
p File.file?("/tmp/readme.txt")
p File.directory?("/tmp/vfsdata")
p File.exist?("/tmp/nope")
