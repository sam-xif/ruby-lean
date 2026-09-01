# Driver for `version.rb` — Homebrew's own version scheme: the `Token`
# hierarchy, the tokenizer, the `<=>` that compares two token lists, and
# `Version.detect`/`Version.parse`, which recover a version from a source URL.
#
# This is the largest file in the slice (63 `def`s across nine classes) and the
# one whose ordering the whole vulnerability decision rests on when an advisory
# range is `ECOSYSTEM`-typed. So the driver exercises the ordering the way a
# caller does — by sorting — and pins the token hierarchy directly underneath.

def show(label)
  puts("#{label} => #{yield.inspect}")
rescue StandardError => e
  puts("#{label} => #{e.class}: #{e.message}")
end

puts("== tokens: `Token.create` picks the subclass off the text")
[
  "1", "10", "0", "a", "alpha", "alpha1", "beta2", "pre3", "rc4", "patch5", "post6", "",
].each do |t|
  show("  #{t.inspect}") do
    tok = Version::Token.create(t)
    [tok.class.to_s, tok.to_s, tok.numeric?, tok.null?]
  end
end
show("  Token.from(3)")     { Version::Token.from(3).to_s }
show("  Token.from(nil)")   { Version::Token.from(nil).null? }

puts
puts("== the token order (the rungs of the scheme)")
# A NullToken is below a numeric zero and above any alphabetic token; the
# prerelease tokens sort alpha < beta < pre < rc < patch < post.
pairs = [
  %w[1 2], %w[10 9], %w[1 1], %w[a b], %w[alpha beta], %w[beta pre], %w[pre rc],
  %w[rc patch], %w[patch post], %w[1 a], %w[alpha 1],
]
pairs.each do |a, b|
  show("  #{a} <=> #{b}") { Version::Token.create(a) <=> Version::Token.create(b) }
end
show("  NULL <=> 0") { Version::NULL_TOKEN <=> Version::Token.create("0") }
show("  NULL <=> a") { Version::NULL_TOKEN <=> Version::Token.create("a") }

puts
puts("== Version#<=>, and the sort it induces")
[
  %w[1.0 1.1], %w[1.10 1.9], %w[1.0 1.0.0], %w[1.0.0 1.0], %w[2.0 1.9.9],
  %w[1.0beta1 1.0], %w[1.0rc1 1.0], %w[1.0 1.0patch1], %w[1.0a 1.0],
  %w[HEAD 1.0], %w[HEAD HEAD],
].each { |a, b| show("  #{a} <=> #{b}") { Version.new(a) <=> Version.new(b) } }
show("sorted") do
  %w[1.10 1.9 1.9.1 2.0 1.9a 1.0rc1 1.0 HEAD].sort_by { |v| Version.new(v) }
end
# `Array#sort`/`#max` over user objects need `<=>` *dispatch*, which the model
# does not do — a demand on the semantics rather than on the checker, so the
# ordering is exercised through an explicit `<=>` above and through `sort_by`
# (which compares the block's results, not the receiver's elements) below.
show("==")   { Version.new("1.0") == Version.new("1.0") }
show("== a string") { Version.new("1.0") == "1.0" }

puts
puts("== the null version, and HEAD")
show("NULL.null?")            { Version::NULL.null? }
show("NULL.to_s")             { Version::NULL.to_s }
show("NULL <=> 1.0")          { Version::NULL <=> Version.new("1.0") }
show("HEAD head?")            { Version.new("HEAD").head? }
show("HEAD-abc123 commit")    { Version.new("HEAD-abc123").commit }
show("1.0 head?")             { Version.new("1.0").head? }
show("empty")                 { Version.new("") }

puts
puts("== the component readers")
[["1.2.3", :major], ["1.2.3", :major_minor], ["1.2.3", :major_minor_patch],
 ["1", :major_minor], ["1.2.3", :to_i], ["1.2.3", :to_f], ["1.2.3", :to_s]].each do |v, m|
  show("  #{v}.#{m}") { Version.new(v).public_send(m).to_s }
end

puts
puts("== detecting a version from a source URL (Version.detect)")
# Every one of these goes through a different `VERSION_PARSERS` entry, which is
# the point: the parser list is ordered and the first match wins.
#
# Two answers keep a `.tar` on the end (`1.4.2.tar`, `0.5.5.1.orig.tar`). That is
# the boot stub, not the slice: `Pathname#stem` is stubbed as
# `File.basename(self, extname)`, which strips one extension where Homebrew's own
# `extend/pathname.rb` strips a whole archive suffix. Both executors run the same
# stub, so it is recorded rather than papered over.
[
  "https://example.test/downloads/libexample-1.4.2.tar.gz",
  "https://github.com/example/libexample/archive/refs/tags/v1.4.2.tar.gz",
  "https://github.com/example/libexample/tarball/v1.2.3",
  "https://github.com/example/libexample/releases/download/v1.2/foo-1.2.0.tar.gz",
  "https://example.test/boost_1_39_0.tar.gz",
  "https://example.test/ruby-1.9.1-p243.tar.gz",
  "https://example.test/foobar-4.5.0-beta1.tar.gz",
  "https://example.test/dash_0.5.5.1.orig.tar.gz",
  "https://example.test/2023-09-28.tar.gz",
  "https://example.test/no-version-here.tar.gz",
].each { |u| show("  #{u}") { Version.detect(u).to_s } }
show("  detect with an explicit tag") { Version.detect("https://example.test/x.tar.gz", tag: "v9.9.9").to_s }
show("  detected_from_url?")          { Version.detect("https://example.test/libexample-1.4.2.tar.gz").detected_from_url? }
