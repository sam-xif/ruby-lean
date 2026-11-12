# Issue #57: the pure File path helpers resolved every argument with `to_s`, so
# they answered where CRuby raises `TypeError`, and never consulted the
# `to_path`/`to_str` conversions CRuby accepts. Each row prints the answer or
# CRuby's exception and message, so both sides are compared on every line.
def show(label)
  r = begin
    yield.inspect
  rescue => e
    "#{e.class}: #{e.message}"
  end
  puts "#{label}: #{r}"
end

class OnlyPath;  def to_path = "/x/y"; end
class OnlyStr;   def to_str = "/s/t"; end
class Both;      def to_path = "/p/q"; def to_str = "/s/t"; end
class BadPath;   def to_path = 42; end
class BadStr;    def to_str = 42; end
class NilStr;    def to_str = nil; end
class Neither;   def to_s = "/n/m"; end
class NulPath;   def to_path = "/n\0p"; end
class ViaMM
  def method_missing(name, *args)
    name == :to_path ? "/mm/p" : super
  end
end
class DeniesPath
  def to_path = "/denied"
  def to_str = "/str"
  def respond_to?(name, include_private = false)
    name == :to_path ? false : true
  end
end

# The accept/reject boundary: a String is the path, `to_path` then `to_str` are
# consulted for anything else (`to_path` wins when both answer), and the rest is
# CRuby's TypeError, spelled with nil/true/false literally.
show("dirname(OnlyPath)") { File.dirname(OnlyPath.new) }
show("dirname(OnlyStr)") { File.dirname(OnlyStr.new) }
show("dirname(Both)") { File.dirname(Both.new) }
show("dirname(ViaMM)") { File.dirname(ViaMM.new) }
show("dirname(Pathname)") { File.dirname(Pathname.new("/p/q")) }
show("dirname(BadPath)") { File.dirname(BadPath.new) }
show("dirname(BadStr)") { File.dirname(BadStr.new) }
show("dirname(NilStr)") { File.dirname(NilStr.new) }
show("dirname(Neither)") { File.dirname(Neither.new) }
show("dirname(DeniesPath)") { File.dirname(DeniesPath.new) }
show("dirname(123)") { File.dirname(123) }
show("dirname(nil)") { File.dirname(nil) }
show("dirname(true)") { File.dirname(true) }
show("dirname(false)") { File.dirname(false) }
show("dirname(:sym)") { File.dirname(:sym) }
show("dirname([])") { File.dirname([]) }
show("basename(123)") { File.basename(123) }
show("basename(OnlyPath)") { File.basename(OnlyPath.new) }
show("extname(:sym)") { File.extname(:sym) }
show("extname(OnlyStr)") { File.extname(OnlyStr.new) }
show("join(1, 2)") { File.join(1, 2) }
show("join(true, 'x')") { File.join(true, "x") }
show("join(OnlyPath, 'b')") { File.join(OnlyPath.new, "b") }
show("join(Pathname, 'b')") { File.join(Pathname.new("/p"), "b") }

# The suffix is converted before the path, with `StringValue` — so an explicit
# nil is a TypeError, and a bad suffix is reported before a bad path.
show("basename(str, nil)") { File.basename("/a/b.rb", nil) }
show("basename(str, :rb)") { File.basename("/a/b.rb", :rb) }
show("basename(str, OnlyStr)") { File.basename("/a/b.rb", OnlyStr.new) }
show("basename(str, OnlyPath)") { File.basename("/a/b.rb", OnlyPath.new) }
show("basename(:sym, 123)") { File.basename(:sym, 123) }
show("basename(123, :sym)") { File.basename(123, :sym) }
show("basename()") { File.basename }
show("basename(a, b, c)") { File.basename("a", "b", "c") }

# A NUL byte is not a path: `rb_get_path`'s message for a path, and
# `StringValueCStr`'s for a suffix or a String part of `join`.
show("dirname(nul)") { File.dirname("a\0b") }
show("basename(nul)") { File.basename("a\0b") }
show("extname(nul)") { File.extname("a\0b") }
show("dirname(nul via to_path)") { File.dirname(NulPath.new) }
show("join(nul string)") { File.join("a", "x\0y") }
show("basename(nul suffix)") { File.basename("a", "x\0y") }
show("basename(nul suffix, root)") { File.basename("/", "x\0y") }
