# ─── File — the pure path operations only ───────────────────────────────────
#
# `File` is a filesystem class, and the slice reaches exactly one of its
# methods: `File.basename(url)` in `vulns/identify.rb`, used to chop the last
# component off a *URL*. That operation is pure string manipulation with no
# effect at all, so it is modeled; everything else routes to `method_missing`
# and gates by name. Defining the constant without that guard would turn
# `File.read` from an honest Unsupported into a NoMethodError, which is a wrong
# answer rather than a refusal.
class File
  SEPARATOR = "/"

  def self.basename(path, suffix = nil)
    s = path.to_s
    parts = s.split("/")
    base = parts.empty? ? (s.empty? ? "" : "/") : parts[parts.length - 1]
    return base if suffix.nil?
    return base if suffix == base
    if suffix == ".*"
      i = base.length - 1
      while i > 0
        return base[0, i] if base[i] == "."
        i -= 1
      end
      base
    else
      base.end_with?(suffix) ? base[0, base.length - suffix.length] : base
    end
  end

  def self.extname(path)
    b = basename(path)
    i = b.length - 1
    while i > 0
      return b[i, b.length - i] if b[i] == "."
      i -= 1
    end
    ""
  end

  def self.dirname(path)
    s = path.to_s
    i = s.length - 1
    while i >= 0
      if s[i] == "/"
        return "/" if i.zero?
        return s[0, i]
      end
      i -= 1
    end
    "."
  end

  def self.join(*parts)
    parts.map { |x| x.to_s }.join("/")
  end

  def self.method_missing(name, *args, **kw, &blk)
    __unsupported__("File." + name.to_s + " (only the pure path operations are modeled)")
  end

  def self.respond_to_missing?(name, include_private = false)
    true
  end
end

class String
  # `sub`/`gsub` live here because of the **block form**, which a builtin cannot
  # serve: it has to call back into the interpreter once per match. The
  # two-argument replacement form stays a primitive (`__sub_rep`/`__gsub_rep`)
  # and this only dispatches to it, so the common path costs one extra send.
  #
  # The loop walks **absolute offsets into `self`** via `__search_at`, and that is
  # not a style choice. The earlier version matched against a progressively
  # shortened `rest`, which re-anchored the pattern at every step: `\A` and `^`
  # matched at each remainder's start, so `"12".gsub(/\A\d/) { "X" }` answered
  # `"XX"` where CRuby answers `"X2"` — a **wrong answer** that no corpus reached
  # until the W4b heads generated anchored patterns. Offsets also make `$~`
  # come out right: `__search_at` sets it per iteration, so a block can read `$1`,
  # and the spans are relative to the whole string rather than to a remainder.
  #
  # A **zero-width** match advances one character, without which
  # `"aaa".gsub(/a*/) { "X" }` would not terminate.
  def sub(pat, rep = nil, &blk)
    __match_to_caller
    return __sub_rep(pat, rep) unless rep.nil?
    return __unsupported__("String#sub with neither a replacement nor a block") if blk.nil?
    re = pat.is_a?(Regexp) ? pat : Regexp.new(Regexp.escape(pat))
    m = __search_at(re, 0)
    return self if m.nil?
    b = m.begin(0)
    e = m.end(0)
    self[0, b].to_s + blk.call(m[0]).to_s + self[e, length - e].to_s
  end

  def gsub(pat, rep = nil, &blk)
    __match_to_caller
    return __gsub_rep(pat, rep) unless rep.nil?
    return __unsupported__("String#gsub with neither a replacement nor a block") if blk.nil?
    re = pat.is_a?(Regexp) ? pat : Regexp.new(Regexp.escape(pat))
    out = ""
    cur = 0        # absolute offset of the first character not yet copied out
    last = nil     # begin offset of the last successful match, for `$~`
    guard = 0
    while guard <= length + 1
      guard += 1
      m = __search_at(re, cur)
      break if m.nil?
      b = m.begin(0)
      e = m.end(0)
      last = b
      out += self[cur, b - cur].to_s + blk.call(m[0]).to_s
      if e == b
        out += self[e, 1].to_s
        cur = e + 1
      else
        cur = e
      end
      break if cur > length
    end
    out += self[cur, length - cur].to_s if cur <= length
    # CRuby leaves `$~` at the **last successful** match, not at the failed search
    # that ended the loop [V]. Re-searching from that match's own start finds it
    # again (leftmost-first), which is cheaper than carrying the MatchData.
    __search_at(re, last) unless last.nil?
    out
  end

  # `partition`/`rpartition` split around the first / last occurrence of a
  # String separator and always return three parts [V]; a miss puts the whole
  # string in the *head* for `partition` and in the *tail* for `rpartition`.
  # `index`/`rindex` for a String needle (a Regexp needle would go through the
  # matcher and is not needed here).
  def index(needle, start = 0)
    __match_to_caller
    i = start < 0 ? length + start : start
    i = 0 if i < 0
    # A **Regexp** needle searches with the engine and sets `$~`, exactly as
    # `match` does [V]. Without this branch `needle.length` raised NoMethodError
    # where CRuby answers an offset — a wrong answer, not a gate.
    if needle.is_a?(Regexp)
      m = __search_at(needle, i)
      return m.nil? ? nil : m.begin(0)
    end
    n = needle.length
    while i + n <= length
      return i if self[i, n] == needle
      i += 1
    end
    nil
  end

  def rindex(needle, start = nil)
    # Backward search with a pattern is its own algorithm (CRuby scans right to
    # left for the *last* match); not modeled rather than approximated.
    return __unsupported__("String#rindex with a Regexp needle") if needle.is_a?(Regexp)
    n = needle.length
    i = (start.nil? ? length - n : (start < 0 ? length + start : start))
    i = length - n if i > length - n
    while i >= 0
      return i if self[i, n] == needle
      i -= 1
    end
    nil
  end

  def each_char
    return to_enum_chars unless block_given?
    __each_char_blk { |c| yield(c) }
  end

  # `each_char` without a block would need an Enumerator; the two prelude uses
  # (`all?`, `format`'s digit scan) always pass one, and `chars` covers the rest.
  def to_enum_chars
    chars
  end

  def __each_char_blk
    return __unsupported__("Enumerator: String#each_char without a block") unless block_given?
    i = 0
    while i < length
      yield(self[i, 1])
      i += 1
    end
    self
  end

  def partition(sep)
    i = index(sep)
    return [self, "", ""] if i.nil?
    [self[0, i], sep, self[i + sep.length, length - i - sep.length]]
  end

  def rpartition(sep)
    i = rindex(sep)
    return ["", "", self] if i.nil?
    [self[0, i], sep, self[i + sep.length, length - i - sep.length]]
  end

  # `tr` over explicit character lists and `a-z` ranges, with `^` negation. The
  # `to`-list is padded with its last character, and an empty `to` deletes [V].
  def tr(from, to)
    neg = from.start_with?("^") && from.length > 1
    src = __tr_expand(neg ? from[1, from.length - 1] : from)
    dst = __tr_expand(to)
    out = ""
    each_char do |c|
      hit = src.include?(c)
      hit = !hit if neg
      if !hit
        out += c
      elsif dst.empty?
        # delete
      elsif neg
        out += dst[dst.length - 1]
      else
        i = src.index(c)
        out += (i < dst.length ? dst[i] : dst[dst.length - 1])
      end
    end
    out
  end

  def __tr_expand(spec)
    out = []
    i = 0
    while i < spec.length
      if i + 2 < spec.length && spec[i + 1] == "-"
        a = spec[i].ord
        b = spec[i + 2].ord
        while a <= b
          out.push(a.chr)
          a += 1
        end
        i += 3
      else
        out.push(spec[i])
        i += 1
      end
    end
    out
  end

  # ── Encodings ──
  #
  # The model has exactly two: UTF-8 and ASCII-8BIT. A binary String's payload
  # holds one *character per byte*, which is what makes `Purl.encode` —
  # `component.b.gsub(…) { |c| "%%%02X" % c.ord }` — answer `caf%C3%A9` for
  # `"café"` rather than the character-wise `caf%E9` (L110 gated on this).
  #
  # These are one line each over a Lean primitive, and they are here rather than
  # in Lean for L115's reason: the *interesting* part of `force_encoding` is
  # dispatching `Encoding#name` on its argument, which a builtin cannot do.
  #
  # There is a **third** CRuby encoding this model does not track: `US-ASCII`,
  # which CRuby gives to every String it *synthesizes* rather than reads from
  # source — `65.chr`, `1.to_s`, `:a.to_s`, `nil.to_s`, `[1,2].join`,
  # `/a/.source`, `1.inspect` are all US-ASCII while a literal is UTF-8 [V].
  # Tracking it needs a third tag threaded through ~40 String-producing rules;
  # `slice-gates.md` carries it as a known gap.
  #
  # So `encoding` answers only what the tag actually determines: BINARY, or
  # UTF-8 for a String holding a non-ASCII byte (which no US-ASCII String can).
  # For an ASCII-only String it hands back `Encoding.__undetermined`, whose
  # *observations* gate — it is still the right thing to pass to
  # `force_encoding`, which is the only use the slice makes of it
  # (`Identify.decode` ends `.force_encoding(component.encoding)`).
  def encoding
    return Encoding::BINARY if __binary?
    return Encoding::UTF_8 unless __bytes.all? { |x| x < 128 }
    Encoding.__undetermined
  end

  # `force_encoding` **mutates and returns self**, which is why it goes through
  # `__force_*` rather than the copying `__as_*` that `b` uses.
  def force_encoding(enc)
    # `__name_raw`, not `name`: the undetermined encoding refuses to *name*
    # itself but is UTF-8-or-US-ASCII, and re-tagging as either leaves the bytes
    # alone — `__force_utf8` gates on an invalid sequence in both readings.
    n = enc.is_a?(Encoding) ? (enc.__name_raw || "UTF-8") : enc.to_s
    if n == "ASCII-8BIT" || n == "BINARY" || n == "ascii-8bit" || n == "binary"
      __force_binary
    elsif n == "UTF-8" || n == "utf-8"
      __force_utf8
    else
      __unsupported__("String#force_encoding to " + n)
    end
  end

  def bytes = __bytes

  def each_byte
    return __unsupported__("Enumerator: String#each_byte without a block") unless block_given?
    __bytes.each { |x| yield(x) }
    self
  end

  # `b` is a *copy* in ASCII-8BIT, so it is the non-mutating primitive.
  # String#b is native: it copies without dispatching Ruby conversion/copy hooks.
end

