# Driver for `vulns/purl.rb` — a package URL builder, exercised through the two
# things the file actually promises: per-type name normalisation
# (purl-spec PURL-TYPES.rst) and RFC 3986 percent-encoding on serialisation.
#
# A `Purl`'s default `inspect` carries an address, so every observation below
# goes through `to_s` or a field reader (N38: process-independent output).

def show(label)
  puts("#{label} => #{yield.inspect}")
rescue StandardError => e
  puts("#{label} => #{e.class}: #{e.message}")
end

P = Homebrew::Vulns::Purl

puts("== construction and serialisation")
[
  { type: "brew", name: "libexample", version: "1.4.2" },
  { type: "gem", name: "nokogiri", version: "1.16.0" },
  { type: "npm", namespace: "@types", name: "node", version: "20.11.0" },
  { type: "maven", namespace: "org.apache.logging.log4j", name: "log4j-core", version: "2.14.1" },
  { type: "generic", name: "libexample" },                       # no version
  { type: "generic", namespace: "", name: "x", version: "" },     # empty ⇒ absent
].each { |kw| show("  #{kw}") { P.new(**kw).to_s } }

puts
puts("== per-type normalisation (the case rules the spec fixes)")
[
  { type: "PyPI", name: "Foo_Bar", version: "1.0" },              # downcase, _ ⇒ -
  { type: "hex", namespace: "Some_Org", name: "MyPkg", version: "1.0" },
  { type: "cpan", namespace: "mshelor", name: "Digest-SHA", version: "6.04" },
  { type: "brew", name: "MixedCase", version: "1.0" },            # no rule ⇒ unchanged
].each { |kw| show("  #{kw}") { p = P.new(**kw); [p.type, p.namespace, p.name, p.to_s] } }

puts
puts("== percent-encoding")
[
  "a b/c@d",
  "n@me",
  "1.0+x",
  "plain-name_1.0~x",   # the unreserved set, plus `:`, stays literal
  "a:b",
  "ü",                  # multi-byte: encoded per byte
].each { |c| show("  #{c}") { P.encode(c) } }

puts
puts("== a namespace is split on `/` and encoded segment by segment")
show("nested") { P.new(type: "generic", namespace: "a b/c/", name: "n@me", version: "1.0+x").to_s }

puts
puts("== equality is structural")
a = P.new(type: "brew", name: "x", version: "1")
b = P.new(type: "brew", name: "x", version: "1")
c = P.new(type: "brew", name: "x", version: "2")
show("a == b") { a == b }
show("a == c") { a == c }
show("a.eql?(b)") { a.eql?(b) }
show("a == a string") { a == "pkg:brew/x@1" }
# `Purl#hash` delegates to `Array#hash`, which the model does not implement — a
# demand on the semantics, not on the checker, so it is deliberately not called
# here (see AGENTS.md, the note on rungs the model cannot run).

puts
puts("== the constructor's own preconditions")
show("empty type") { P.new(type: "", name: "x").to_s }
show("empty name") { P.new(type: "brew", name: "").to_s }
