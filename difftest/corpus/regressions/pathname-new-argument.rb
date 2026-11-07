# Issue #93: `Pathname.new` converts its argument the way `File.path` does — a
# String, or an object with `to_path` (then `to_str`) — and raises TypeError for
# anything else. It used to coerce every argument with `to_s`, which answered
# where CRuby raises and read a different path when `to_path` and `to_s` differ.
require "pathname"

def show
  yield
rescue Exception => e
  puts "#{e.class}: #{e.message}"
end

show { p Pathname.new(123) }
show { p Pathname.new(nil) }
show { p Pathname.new(:sym) }
show { p Pathname.new([1]) }

class PathLike
  def to_path = "/from-to_path"
  def to_s = "/from-to_s"
end

show { puts Pathname.new(PathLike.new).to_s }

class StringLike
  def to_str = "/from-to_str"
end

show { puts Pathname.new(StringLike.new).to_s }

show { p Pathname.new("/a\0b") }
