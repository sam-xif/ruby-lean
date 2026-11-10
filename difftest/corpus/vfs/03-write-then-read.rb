# A write replaces the inode's bytes (step 1's documented simplification) and
# answers the number of bytes written; a read afterwards sees them. The next
# run starts from the fixture again, which is what makes this case repeatable.
n = File.write("/tmp/readme.txt", "bye")
p n
p File.read("/tmp/readme.txt")
p File.size("/tmp/readme.txt")
