# Driver for `version/parser.rb` — the abstract `Version::Parser` hierarchy that
# `Version.parse` drives: a regex plus a rule for what part of the spec the
# regex runs against (the whole URL, or its stem).
#
# This file is the slice's one piece of *classical* OO — an `abstract!` base,
# two concrete `process_spec` overrides, an optional post-processing block — so
# the driver exercises the hierarchy directly rather than through `Version`.

def show(label)
  puts("#{label} => #{yield.inspect}")
rescue StandardError => e
  puts("#{label} => #{e.class}: #{e.message}")
end

TARBALL = "https://example.test/downloads/libexample-1.4.2.tar.gz"
TAGGED  = "https://github.com/example/libexample/archive/refs/tags/v1.4.2.tar.gz"
SFORGE  = "https://sourceforge.net/projects/example/files/libexample-2.0/download"
NOEXT   = "https://example.test/downloads/libexample-1.4.2"

puts("== UrlParser matches against the whole URL")
url_parser = Version::UrlParser.new(%r{/archive/refs/tags/v?(\d+(?:\.\d+)*)\.tar\.gz$})
[TARBALL, TAGGED].each { |u| show("  #{u}") { url_parser.parse(Pathname.new(u)) } }

puts
puts("== StemParser matches against the *stem*, and picks it three ways")
# `process_spec` is the whole content of the subclass: the SourceForge
# `/download` route takes the parent directory's stem, an extension-less path
# takes the basename, and everything else takes the stem.
show("  process_spec tarball")     { Version::StemParser.process_spec(Pathname.new(TARBALL)) }
show("  process_spec sourceforge") { Version::StemParser.process_spec(Pathname.new(SFORGE)) }
show("  process_spec no-extension"){ Version::StemParser.process_spec(Pathname.new(NOEXT)) }
show("  process_spec url")         { Version::UrlParser.process_spec(Pathname.new(TARBALL)) }

stem_parser = Version::StemParser.new(/[-_]v?(\d+(?:\.\d+)*)(?:\.tar)?$/)
[TARBALL, SFORGE, NOEXT].each { |u| show("  parse #{u}") { stem_parser.parse(Pathname.new(u)) } }

puts
puts("== the optional block post-processes the capture")
underscored = Version::StemParser.new(/[-_](v?[\d_]+)(?:\.tar)?$/) { |v| v.tr("_", ".") }
show("  1_4_2") { underscored.parse(Pathname.new("https://example.test/libexample-1_4_2.tar.gz")) }

puts
puts("== no match, and an empty capture, both answer nil")
never = Version::UrlParser.new(/(nothing-matches-this)/)
show("  no match")      { never.parse(Pathname.new(TARBALL)) }
show("  empty capture") { Version::UrlParser.new(/libexample(.*)-1/).parse(Pathname.new(TARBALL)) }

puts
puts("== the abstract base is abstract, and RegexParser has no process_spec")
show("Parser.new")        { Version::Parser.new.parse(Pathname.new(TARBALL)) }
show("RegexParser.parse") { Version::RegexParser.new(/(\d+)/).parse(Pathname.new(TARBALL)) }
