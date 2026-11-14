# Issue #93: `Pathname.new` converts its argument the way `File.path` does —
# `rb_get_path`: a String, or `to_path` (then `to_str`) of it or of the argument
# — and raises TypeError for anything else. It used to coerce every argument
# with `to_s`, which answered where CRuby raises and read a different path when
# `to_path` and `to_s` differ.
#
# Each block pins one clause of `rb_get_path_check_to_string`:
#
#   * a non-String, non-convertible argument raises the rewritten TypeError;
#   * `to_path` wins over `to_str`, and `to_str` converts an argument without it;
#   * a non-String `to_path` answer goes through `StringValue`'s `to_str` step;
#   * `rb_check_funcall_default`'s default is the argument, so `to_path` that is
#     only served by `method_missing` (and delegates to `super`) falls through to
#     the argument's `to_str` rather than raising;
#   * any TypeError raised inside the conversion is rewritten, and a
#     `NoMethodError` from a user `to_path` is not;
#   * the null byte is ArgumentError, not TypeError, so it is not rewritten.
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
  def to_s = "/from-to-to_s"
end

show { puts Pathname.new(PathLike.new).to_s }

class StringLike
  def to_str = "/from-to_str"
  def to_s = "/from-to_s"
end

show { puts Pathname.new(StringLike.new).to_s }

class Inner
  def to_str = "/inner"
end

class Outer
  def to_path = Inner.new
  def to_s = "/outer-to_s"
end

show { puts Pathname.new(Outer.new).to_s }

class ServesToPath
  def method_missing(name, *args)
    return "/from-method_missing-to_path" if name == :to_path
    super
  end
end

show { puts Pathname.new(ServesToPath.new).to_s }

class ServesToStr
  def method_missing(name, *args)
    return "/from-method_missing-to_str" if name == :to_str
    super
  end
end

show { puts Pathname.new(ServesToStr.new).to_s }

class NamedToPath
  def respond_to_missing?(name, include_private = false) = name == :to_path
  def method_missing(name, *args)
    return "/from-respond_to_missing" if name == :to_path
    super
  end
end

show { puts Pathname.new(NamedToPath.new).to_s }

class BadToStr
  def to_str = raise(TypeError, "inner")
end

show { puts Pathname.new(BadToStr.new).to_s }

class BadToPath
  def to_path = raise(TypeError, "inner path")
end

show { puts Pathname.new(BadToPath.new).to_s }

class NilToPath
  def to_path = nil
  def to_str = "/fallback"
end

show { puts Pathname.new(NilToPath.new).to_s }

class MissingInsideToPath
  def to_path = nil.missing_inner
end

show { puts Pathname.new(MissingInsideToPath.new).to_s }

class RefusesRespondTo
  def to_path = "/refused"
  def to_str = "/refused-str"
  def respond_to?(name, include_private = false) = false
end

show { puts Pathname.new(RefusesRespondTo.new).to_s }

show { p Pathname.new("/a\0b") }

show { p Pathname.new("plain").to_s }
