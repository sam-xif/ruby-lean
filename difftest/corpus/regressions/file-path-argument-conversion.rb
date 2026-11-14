# File's path helpers run each path argument through `rb_get_path`
# (`FilePathStringValue`), never `to_s`: a String is itself, `to_path` is
# dispatched, and the answer goes through `StringValue` (`to_str`). A value with
# neither is a TypeError naming its class, not a stringified path (issue #57).
class FilePathArg
  def to_path = "/a/b"
end

class FilePathNonString
  def to_path = 42
end

class FileStrArg
  def to_str = "x/y"
end

class FileStrNonString
  def to_str = 42
end

class FileBothArg
  def to_path = "p"
  def to_str = "s"
end

class FileMissingArg
  def method_missing(name, *args)
    name == :to_path ? "/mm/x" : super
  end

  def respond_to_missing?(name, priv = false) = name == :to_path
end

class FileNoRespondArg
  def to_path = "x"
  def respond_to?(*args) = false
end

def file_case(label)
  puts label + ": " + yield.inspect
rescue StandardError => e
  puts label + ": " + [e.class, e.message].inspect
end

file_case("dirname(Integer)") { File.dirname(123) }
file_case("basename(Integer)") { File.basename(123) }
file_case("extname(Symbol)") { File.extname(:sym) }
file_case("join(Integer, Integer)") { File.join(1, 2) }
file_case("dirname(nil)") { File.dirname(nil) }
file_case("dirname(true)") { File.dirname(true) }
file_case("basename(String, Symbol)") { File.basename("a/b", :x) }

# to_path wins over to_str, and its answer is a path in its own right.
file_case("dirname(to_path)") { File.dirname(FilePathArg.new) }
file_case("dirname(to_path, to_str)") { File.dirname(FileBothArg.new) }
file_case("basename(String, to_path)") { File.basename("a/b", FileBothArg.new) }
file_case("dirname(to_str)") { File.dirname(FileStrArg.new) }

# A non-String answer is converted again by StringValue, so the message names
# what that value is, not the receiver.
file_case("dirname(to_path -> Integer)") { File.dirname(FilePathNonString.new) }
file_case("dirname(to_str -> Integer)") { File.dirname(FileStrNonString.new) }

# The conversion dispatches, so a method_missing-served to_path converts, and a
# respond_to? that denies it does not.
file_case("dirname(method_missing to_path)") { File.dirname(FileMissingArg.new) }
file_case("dirname(respond_to? false)") { File.dirname(FileNoRespondArg.new) }

# Pathname is a path, through its own to_path.
file_case("dirname(Pathname)") { File.dirname(Pathname.new("a/b")) }
