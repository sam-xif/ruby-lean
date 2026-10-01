# frozen_string_literal: true

# ─── URI — the one function the slice reaches ───────────────────────────────
#
# `version.rb:351` calls `URI.decode_www_form_component(spec)` and that is the
# **only** use of `URI` anywhere in the slice's eight files. It is a pure string
# function, so it is modeled; everything else on `URI` routes to
# `method_missing` and gates by name, for the same reason `File` does — defining
# the constant without that guard would turn `URI.parse` from an honest
# Unsupported into a NoMethodError.
#
# One real limit, and it is the byte-string limit again: a `%XX` above 0x7F is a
# *byte* of a multi-byte character (`caf%C3%A9` is `café`), and the model has no
# byte strings, so that gates rather than producing two junk characters.
module URI
  def self.decode_www_form_component(str, enc = nil)
    s = str.to_s
    out = ""
    i = 0
    while i < s.length
      c = s[i]
      if c == "+"
        out += " "
        i += 1
      elsif c == "%"
        hex = s[i + 1, 2]
        if hex.nil? || hex.length < 2 || !__hex2?(hex)
          raise ArgumentError, "invalid %-encoding (" + s + ")"
        end
        n = Integer(hex, 16)
        if n > 127
          return __unsupported__("URI.decode_www_form_component of a multi-byte %-escape " \
                                 "(byte strings are not modeled)")
        end
        out += n.chr
        i += 3
      else
        out += c
        i += 1
      end
    end
    out
  end

  def self.__hex2?(h)
    h.each_char.all? { |c| "0123456789abcdefABCDEF".include?(c) }
  end

  def self.method_missing(name, *args, **kw, &blk)
    __unsupported__("URI." + name.to_s + " (only decode_www_form_component is modeled)")
  end

  def self.respond_to_missing?(name, include_private = false)
    true
  end
end
