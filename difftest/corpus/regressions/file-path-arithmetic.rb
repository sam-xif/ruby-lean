# issue #166: File.dirname/basename/extname's pure path arithmetic.
#
# Each table row comes from the issue, which compared the model with CRuby
# 4.0.5. `dirname` chomps the trailing run of separators before it looks for a
# parent (so `"a/b/"` has the parent `"a"`), `extname` skips a component's
# leading dots (so `".."` has no extension), and `basename`'s `".*"` selector
# chops what `extname` finds rather than the last dot of the string (so `".."`
# is left alone).

# dirname: trailing and repeated separators
p File.dirname("a/")
p File.dirname("a//")
p File.dirname("/a/")
p File.dirname("a/b/")
p File.dirname("a/b//")
p File.dirname("a//b")
p File.dirname("///")
p File.dirname("//a")
p File.dirname("/a/b")
p File.dirname("/a//b//c///")

# dirname: the level argument (Ruby 3.4's `rb_file_dirname_n`)
p File.dirname("/a/b/c", 2)
p File.dirname("/a/b/c", 3)
p File.dirname("/a/b/c", 0)
p File.dirname("a/b/c", 2)
p File.dirname("/a/b", 2.0)
begin
  File.dirname("/a/b", -1)
rescue ArgumentError => e
  p e.message
end

# extname: a component made only of dots has no extension
p File.extname("..")
p File.extname("...")
p File.extname("a/..")
p File.extname(".a")
p File.extname("a.")
p File.extname("a..b")
p File.extname("/a/b.c/")

# basename: the ".*" selector leaves a dot-only component alone
p File.basename("..", ".*")
p File.basename("...", ".*")
p File.basename("a.rb", ".*")
p File.basename("/a/b.c/", ".*")

# basename: the ordinary suffix forms still chop, and a suffix that is the whole
# component is not removed
p File.basename("a/b")
p File.basename("a/b/")
p File.basename("///")
p File.basename("a.rb", "rb")
p File.basename("a.rb", ".rb")
p File.basename("a", "a")
p File.basename("a/b", "b")
