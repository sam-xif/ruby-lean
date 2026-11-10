# `Dir.exist?` asks for a directory, not for existence: a regular file answers
# false, and so does a missing path. `File.exist?` is the existence question, on
# the same paths.
p Dir.exist?("/tmp/readme.txt")
p Dir.exist?("/tmp/vfsdata/nums.txt")
p Dir.exist?("/tmp/vfsdata")
p Dir.exist?("/tmp")
p Dir.exist?("/tmp/nope")
p File.exist?("/tmp/readme.txt")
p File.exist?("/tmp/nope")
