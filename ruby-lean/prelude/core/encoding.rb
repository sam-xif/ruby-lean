# ─── Encoding ───────────────────────────────────────────────────────────────
#
# Two real instances and one honest placeholder are the whole class: the model's
# Strings are either UTF-8 or ASCII-8BIT, and `UNDETERMINED` stands for
# "UTF-8 or US-ASCII, and this model does not track which" — see `String#encoding`
# above for why that is a refusal rather than a guess.
#
# `ASCII_8BIT` is `BINARY` *by identity*, matching CRuby, where
# `Encoding::BINARY.equal?(Encoding::ASCII_8BIT)` is true [V] — `BINARY` is the
# alias and `ASCII-8BIT` the `name`, which is why `name` and `inspect` disagree
# about which spelling to use.
#
# Anything else CRuby's Encoding can do (`list`, `default_external`,
# `compatible?`, `Encoding.find`) is absent, so it gates by the shadow rule
# rather than by a `method_missing` guard.
class Encoding
  def initialize(name)
    @name = name
  end

  # The raw tag, `nil` for the undetermined one. Not CRuby API — it exists so
  # `String#force_encoding` can act on an encoding that refuses to name itself.
  def __name_raw = @name

  def __gate = __unsupported__("Encoding of an ASCII-only String (US-ASCII vs UTF-8 is not tracked)")

  def name = @name.nil? ? __gate : @name

  def to_s = name

  def inspect
    return __gate if @name.nil?
    @name == "UTF-8" ? "#<Encoding:UTF-8>" : "#<Encoding:BINARY (ASCII-8BIT)>"
  end

  def ==(other)
    return __gate if @name.nil?
    return false unless other.is_a?(Encoding)
    return other.__gate if other.__name_raw.nil?
    other.__name_raw == @name
  end

  def eql?(other) = self == other

  UTF_8 = new("UTF-8")
  BINARY = new("ASCII-8BIT")
  ASCII_8BIT = BINARY

  # The "UTF-8 or US-ASCII, and the model does not know which" instance. One
  # object, memoized, so identity is stable across calls the way the real
  # constants' is.
  UNDETERMINED = new(nil)

  def self.__undetermined = UNDETERMINED
end

