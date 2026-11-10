# Path resolution: `.`, `..`, an interior `//`, and a trailing slash. The
# trailing slash names a directory only, so `/tmp/readme.txt/` and
# `/tmp/readme.txt/.` are not the file (CRuby's ENOTDIR; there is no Errno to
# answer with yet, so the predicates answer false).
p File.exist?("/")
p File.directory?("/tmp")
p File.directory?("/tmp/")
p File.exist?("/tmp//readme.txt")
p File.exist?("/tmp/./readme.txt")
p File.exist?("/tmp/../tmp/readme.txt")
p File.exist?("/tmp/readme.txt/")
p File.directory?("/tmp/readme.txt/")
p File.exist?("/tmp/readme.txt/.")
p File.file?("/tmp/vfsdata")
p File.exist?("/tmp/vfsdata/nums.txt")
