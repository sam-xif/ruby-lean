# The empty write, in the nested directory: 0 bytes written, then an empty read
# and a zero size. A truncation bug and an empty file look the same to `size`,
# so the read is what pins it.
p File.write("/tmp/vfsdata/nums.txt", "")
p File.read("/tmp/vfsdata/nums.txt")
p File.size("/tmp/vfsdata/nums.txt")
