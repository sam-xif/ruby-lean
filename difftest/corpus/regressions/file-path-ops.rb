# File.dirname / File.extname / File.join match CRuby on the separator and
# dotfile edge cases. Each `p` below was a genuine disagreement before the fix:
# the prelude returned the text before the last `/` verbatim (keeping trailing
# slashes), scanned `extname` to index 0 without skipping a leading dot run, and
# joined parts with a bare `"/"` (producing `"a///b"`).

# dirname: trailing and repeated separators do not name a component.
p File.dirname("/foo/")          # => "/"
p File.dirname("foo//bar")       # => "foo"
p File.dirname("foo/")           # => "."
p File.dirname("/foo//")         # => "/"
p File.dirname("foo//bar//baz")  # => "foo//bar"
p File.dirname("a/./b/")         # => "a/."
p File.dirname("/")              # => "/"
p File.dirname("///")            # => "/"

# extname: a leading run of dots is not an extension.
p File.extname("..")             # => ""
p File.extname(".")              # => ""
p File.extname(".bashrc")        # => ""
p File.extname(".a.b")           # => ".b"
p File.extname("a...")           # => "."

# join: collapse the inserted separator with a leading `/`, keep interior ones.
p File.join("a/", "/b")          # => "a/b"
p File.join("a", "/b")           # => "a/b"
p File.join("a//", "a")          # => "a//a"
p File.join("a//", "/a")         # => "a/a"
p File.join("a/", "/b/", "/c")   # => "a/b/c"
p File.join("", "a")             # => "/a"
p File.join("a", "")             # => "a/"
