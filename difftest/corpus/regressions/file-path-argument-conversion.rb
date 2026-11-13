# `File`'s path helpers coerced every argument with `to_s`, so a program whose
# argument was not a String ran to a value where CRuby raises: `File.dirname(123)`
# answered "." and `File.basename(123)` answered "123" where CRuby raises
# `TypeError: no implicit conversion of Integer into String`. That is a wrong
# answer, not a gate (`AGENTS.md` rule 3), on methods that are modeled.
#
# CRuby resolves a path through `FilePathValue` (`rb_get_path`): a String
# stands; otherwise `to_path` and, failing that, `to_str` must answer a String;
# anything else is a TypeError. The suffix of `File.basename` uses the narrower
# `StringValue` (a String or `to_str`, never `to_path`), and an omitted suffix
# differs from an explicit `nil` (which raises).
#
# `File.join` additionally joins each nested array to a String before joining
# the results, drops every trailing separator of the accumulated result when the
# next name starts with one, and raises `ArgumentError: recursive array` on a
# cycle. The separator rows are not part of the coercion defect: they pin the
# rule the rewritten `join` has to keep.
require "pathname"

def show(label)
  puts("#{label} => #{yield.inspect}")
rescue StandardError => e
  puts("#{label} => #{e.class}: #{e.message}")
end

class ToPath
  def to_path = "/tp/x"
end

class ToPathBad
  def to_path = 123
end

class ToStr
  def to_str = "/ts/x"
end

class Both
  def to_path = "/b/x"
  def to_str = "/b/y"
end

class OnlyToS
  def to_s = "/ots/x"
end

# The four rows of the defect: an Integer/Symbol where a path belongs.
show("dirname(123)")  { File.dirname(123) }
show("basename(123)") { File.basename(123) }
show("extname(:sym)") { File.extname(:sym) }
show("join(1, 2)")    { File.join(1, 2) }

# The message names the argument's class, and immediates by their own name.
show("dirname(nil)")      { File.dirname(nil) }
show("dirname(true)")     { File.dirname(true) }
show("dirname(false)")    { File.dirname(false) }
show("dirname(1.5)")      { File.dirname(1.5) }
show("dirname(/re/)")     { File.dirname(/re/) }
show("dirname(Object)")   { File.dirname(Object.new) }

# `to_path` wins over `to_str`; `to_str` is the fallback; `to_s` alone is not a
# conversion, and a bad `to_path` result is named by its own class.
show("dirname(ToPath)")     { File.dirname(ToPath.new) }
show("dirname(ToPathBad)")  { File.dirname(ToPathBad.new) }
show("dirname(ToStr)")      { File.dirname(ToStr.new) }
show("dirname(Both)")       { File.dirname(Both.new) }
show("dirname(OnlyToS)")    { File.dirname(OnlyToS.new) }
show("extname(ToPath)")     { File.extname(ToPath.new) }
show("basename(Pathname)")  { File.basename(Pathname.new("/a/b")) }

# `basename`'s suffix is a `StringValue`: an omitted suffix, an explicit nil,
# `to_str` (accepted) and `to_path` (refused) all differ.
show("basename('a.rb')")           { File.basename("a.rb") }
show("basename('a.rb', nil)")      { File.basename("a.rb", nil) }
show("basename('a.rb', 1)")        { File.basename("a.rb", 1) }
show("basename('a.rb', ToStr)")    { File.basename("a.rb", ToStr.new) }
show("basename('a.rb', ToPath)")   { File.basename("a.rb", ToPath.new) }
show("basename('a.rb', '.rb')")    { File.basename("a.rb", ".rb") }
show("basename('/a/b.rb', '.*')")  { File.basename("/a/b.rb", ".*") }

# The modeled String cases still answer.
show("dirname('')")        { File.dirname("") }
show("dirname('/')")       { File.dirname("/") }
show("dirname('/a/b/c')")  { File.dirname("/a/b/c") }
show("basename('/a/b.rb')"){ File.basename("/a/b.rb") }
show("extname('a.tar.gz')"){ File.extname("a.tar.gz") }
show("join()")             { File.join() }
show("join('usr','mail','gumby')") { File.join("usr", "mail", "gumby") }

# Nested arrays are joined to Strings first, so an empty array is an empty
# string, not nothing: `join([[], []])` is "/".
show("join(['a', ['b', 'c']], 'd')") { File.join(["a", ["b", "c"]], "d") }
show("join([[], []])")               { File.join([[], []]) }
show("join([[], 'a'])")              { File.join([[], "a"]) }
show("join(['a', []])")              { File.join(["a", []]) }
show("join([Pathname, 'c'])")        { File.join([Pathname.new("/a/b"), "c"]) }
show("join([1])")                    { File.join([1]) }
show("join([nil])")                  { File.join([nil]) }

# The separator rule: the next name's leading separators replace the
# accumulated result's trailing ones, and are kept as written.
show("join('a/', '/b')")   { File.join("a/", "/b") }
show("join('a//', '//b')") { File.join("a//", "//b") }
show("join('a//', '/a')")  { File.join("a//", "/a") }
show("join('/a/', '//')")  { File.join("/a/", "//") }
show("join('a', '')")      { File.join("a", "") }
show("join('', '')")       { File.join("", "") }
show("join('a', '/')")     { File.join("a", "/") }
show("join('a/', 'b')")    { File.join("a/", "b") }

# A cycle is an ArgumentError, not an endless recursion.
cycle = []
cycle << cycle
show("join(recursive)")        { File.join(cycle) }
show("join(['a', recursive])") { File.join(["a", cycle]) }
deep = ["q"]
deep << [deep]
show("join(deep recursive)")   { File.join(deep) }
