# File.basename(path, ".*") must not strip a leading run of dots: those name
# the file, not an extension. The prelude scanned back to the last dot anywhere
# and answered "." for "..", "..." and "..foo"; CRuby keeps the dots. It also
# still strips a real extension after the leading run.

p File.basename("..", ".*")        # => ".."
p File.basename("...", ".*")       # => "..."
p File.basename("..foo", ".*")     # => "..foo"
p File.basename("/a/..", ".*")     # => ".."
p File.basename(".bashrc", ".*")   # => ".bashrc"
p File.basename(".a.b", ".*")      # => ".a"
p File.basename("foo.ext", ".*")   # => "foo"
p File.basename("foo.", ".*")      # => "foo"
p File.basename("a...", ".*")      # => "a.."
