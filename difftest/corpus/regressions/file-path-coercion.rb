# FIXED — File's path helpers coerce with `FilePathStringValue`, not `to_s`.
#
# `File.basename`/`dirname`/`extname`/`join` each began with `path.to_s`, so the
# model answered *every* argument while CRuby raises `TypeError` for anything
# that is neither a String nor an object answering `to_path`/`to_str`. That is a
# wrong answer, not a refusal (AGENTS.md rule 3), and it was found while fixing
# the CRuby-fidelity defects in the same three string helpers.
#
# The coercion is CRuby's `rb_get_path`: a String verbatim; otherwise `to_path`
# (through `method_missing`, like `rb_check_funcall`), whose answer is then
# `StringValue`-ed — which is why a `to_path` answering an Integer is reported as
# `no implicit conversion of Integer into String` and not as an error naming the
# outer object; otherwise `to_str`; otherwise `no implicit conversion`.
#
# Every observation is rescued, so each line pins one accept/reject decision
# rather than taking the program down at the first one.
def show(label)
  puts("#{label} => #{yield.inspect}")
rescue StandardError => e
  puts("#{label} => #{e.class}: #{e.message}")
end

# the four rows from the issue
show("dirname integer")  { File.dirname(123) }
show("basename integer") { File.basename(123) }
show("join integers")    { File.join(1, 2) }
show("extname symbol")   { File.extname(:sym) }

# nil/true/false are named literally in the message
show("dirname nil")  { File.dirname(nil) }
show("basename nil") { File.basename(nil) }
show("extname nil")  { File.extname(nil) }
show("join nil")     { File.join("a", nil) }
show("join true")    { File.join(true) }

# the suffix goes through `StringValue` too, before the path, and an explicit
# nil suffix is an error rather than "no suffix"
show("basename suffix integer") { File.basename("a/b.rb", 5) }
show("basename suffix nil")     { File.basename("a/b.rb", nil) }
show("basename both bad")       { File.basename(123, 456) }

# `to_path` is the conversion, and its answer is converted again
class Path
  def initialize(p) = @p = p
  def to_path = @p
end
show("dirname to_path")  { File.dirname(Path.new("/a/b.rb")) }
show("basename to_path") { File.basename(Path.new("/a/b.rb"), ".rb") }
show("extname to_path")  { File.extname(Path.new("/a/b.rb")) }
show("join to_path")     { File.join("x", Path.new("y/z")) }

class BadPath
  def to_path = 7
end
show("dirname bad to_path") { File.dirname(BadPath.new) }
show("join bad to_path")    { File.join("a", BadPath.new) }

class NilPath
  def to_path = nil
end
show("basename nil to_path") { File.basename(NilPath.new) }

# `rb_get_path` still accepts a bare `to_str`, and a non-String answer names the
# method (`to`, not `into`)
class Str
  def to_str = "s/t.rb"
end
show("dirname to_str") { File.dirname(Str.new) }
show("join to_str")    { File.join("a", Str.new) }

class BadStr
  def to_str = 5
end
show("dirname bad to_str") { File.dirname(BadStr.new) }

# `to_path` served through `method_missing`/`respond_to_missing?`
class MM
  def respond_to_missing?(name, _priv = false) = name == :to_path
  def method_missing(name, *_args) = name == :to_path ? "/mm/f.rb" : super
end
show("dirname method_missing") { File.dirname(MM.new) }

# arity is CRuby's 1..2 for both
show("basename no args")    { File.basename }
show("basename three args") { File.basename("a", "b", "c") }
show("dirname no args")     { File.dirname }
show("dirname three args")  { File.dirname("a", "b", "c") }

# controls: Strings are still used verbatim, suffix included
show("dirname string")  { File.dirname("/a/b.rb") }
show("basename string") { File.basename("/a/b.rb", ".rb") }
show("extname string")  { File.extname("/a/b.rb") }
show("join strings")    { File.join("/a", "b.rb") }
show("basename empty suffix") { File.basename("a/b.rb", "") }

# The conversion ends at `rb_str_to_cstr` (`rb_get_path_check_convert`), so an
# interior NUL is an `ArgumentError` — and the message names the caller's own
# conversion: a path says "path name", while `File.join`'s `StringValueCStr` on
# an element, and `File.basename`'s on a suffix, say "string" [V]
nul = 0.chr
show("dirname nul")  { File.dirname("a#{nul}b") }
show("basename nul") { File.basename("a#{nul}b") }
show("extname nul")  { File.extname("a#{nul}b.rb") }
show("join nul")     { File.join("x", "a#{nul}b") }
show("join nested nul") { File.join(["a", ["b#{nul}c"]]) }
class NulPath
  def to_path = "/a" + 0.chr + "b"
end
show("dirname nul to_path") { File.dirname(NulPath.new) }
show("join nul to_path")    { File.join("x", NulPath.new) }

# a suffix is only examined when the path has a component, and an all-separator
# path never looks at it at all
show("basename nul suffix") { File.basename("a/b", nul) }
show("basename nul suffix, empty path") { File.basename("", nul) }
show("basename nul suffix, root") { File.basename("/", nul) }
show("basename nul suffix, unmatched") { File.basename("a/b", nul + "x") }
