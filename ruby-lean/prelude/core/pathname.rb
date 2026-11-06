# ─── Pathname — the pure path half ─────────────────────────────────────────
#
# `Version.detect` wraps its argument in `Pathname(spec)` and then asks it for
# `to_s`, `basename`, `dirname` and Homebrew's own `stem` — all pure string
# operations on the path, with no filesystem access anywhere in the slice. So
# `Pathname` is a wrapper over a String with exactly those, plus the
# `extname`/`sub`/`==`/`inspect` that fall out; anything else routes to
# `method_missing` and gates by name, the same guard `File` and `URI` use, so
# `Pathname#exist?` refuses rather than answering.
#
# `Pathname#stem`, which `Version.detect` also calls, is deliberately **not**
# here: it is Homebrew's own extension (`extend/pathname.rb:187`), not Ruby's, so
# putting it in the prelude would make the model answer something the control —
# running the same program without Homebrew's boot path — cannot. It belongs in
# the difftest harness's stub set, alongside `blank?`.
class Pathname
  include Comparable

  def initialize(path)
    @path = path.to_s
  end

  def to_s = @path

  def to_path = @path

  def inspect = "#<Pathname:" + @path + ">"

  def <=>(other) = other.is_a?(Pathname) ? (@path <=> other.to_s) : nil

  def ==(other) = other.is_a?(Pathname) && @path == other.to_s

  def eql?(other) = self == other

  def basename(suffix = nil)
    Pathname.new(suffix.nil? ? File.basename(@path) : File.basename(@path, suffix))
  end

  def dirname = Pathname.new(File.dirname(@path))

  def extname = File.extname(@path)

  def sub(*args, &blk) = Pathname.new(@path.sub(*args, &blk))

  def empty? = @path.empty?

  def method_missing(name, *args, **kw, &blk)
    __unsupported__("Pathname#" + name.to_s + " (only the pure path operations are modeled)")
  end

  def respond_to_missing?(name, include_private = false)
    true
  end
end

module Kernel
  def Pathname(arg)
    arg.is_a?(Pathname) ? arg : Pathname.new(arg)
  end
end

