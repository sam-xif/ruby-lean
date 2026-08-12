# frozen_string_literal: true

# Generate regex probe cases (`pattern \t opts \t input`) for the W2a oracle.
#
#   ruby scripts/rxcases.rb [homebrew-root] > cases.tsv
#
# Two sources, deliberately:
#
# 1. **The slice's own patterns**, harvested from the eight files of the version
#    + vulnerability slice, crossed with a corpus of version-shaped strings. This
#    is the population the engine actually has to serve, so it is the population
#    it is measured on. Interpolated patterns are included with their
#    interpolations replaced by plausible sub-patterns, since the desugarer turns
#    them into `Regexp.new` over a built string anyway.
#
# 2. **A hand-written adversarial set** for the constructs where a backtracking
#    engine's *order* is the specification and a plausible implementation can
#    still be wrong: greedy vs lazy, nested and empty-body repetition, capture
#    restoration on backtracking, alternation preference, anchors at the edges,
#    `\Z` before a trailing newline, negated classes, and case folding.

require "prism"

ROOT = ARGV[0] || "/tmp/hb/brew/Library/Homebrew"
FILES = %w[version.rb version/parser.rb pkg_version.rb vulns/semver.rb vulns/cvss.rb
           vulns/purl.rb vulns/vulnerability.rb vulns/identify.rb].freeze

# Stand-ins for `#{…}` inside a pattern: the slice interpolates other patterns'
# sources, so a sub-pattern is the faithful substitution.
INTERP = ["\\d+", "[a-z]+", "\\d+(?:\\.\\d+)*"].freeze

def harvest
  out = []
  FILES.each do |f|
    path = File.join(ROOT, f)
    next unless File.exist?(path)

    res = Prism.parse(File.read(path))
    walk = lambda do |n|
      return unless n.is_a?(Prism::Node)

      opts = 0
      if n.is_a?(Prism::RegularExpressionNode) || n.is_a?(Prism::InterpolatedRegularExpressionNode)
        opts = (n.ignore_case? ? 1 : 0) | (n.extended? ? 2 : 0) |
               (n.multi_line? ? 4 : 0) | (n.ascii_8bit? ? 32 : 0)
      end
      if n.is_a?(Prism::RegularExpressionNode)
        out << [n.unescaped, opts]
      elsif n.is_a?(Prism::InterpolatedRegularExpressionNode)
        INTERP.each do |sub|
          src = n.parts.map { |p| p.is_a?(Prism::StringNode) ? p.unescaped : sub }.join
          out << [src, opts]
        end
      end
      n.compact_child_nodes.each { |c| walk.call(c) }
    end
    walk.call(res.value)
  end
  out.uniq
end

INPUTS = [
  "", "1", "1.2", "1.2.3", "1.2.3.4", "v1.2.3", "V1.2.3", "1.2.3-rc1", "1.2.3rc1",
  "1.2.3.beta.2", "1.2.3-alpha", "1.2.3+build.5", "1.2.3-1.2.3+a.b", "2.0.0-rc.1+exp",
  "1_2_3", "1-2", "20240115", "2024-01-15", "HEAD", "HEAD-abc123", "R1a2-3",
  "foo-1.2.3", "foo_1.2.3.tar.gz", "foo-1.2.3.zip", "libfoo-2.0.tar.bz2",
  "https://github.com/a/b/archive/v1.2.3.tar.gz",
  "https://github.com/a/b/releases/download/v1.2.3/b.tgz",
  "https://rubygems.org/downloads/rails-7.0.0.gem",
  "https://registry.npmjs.org/@scope/pkg/-/pkg-1.0.0.tgz",
  "https://files.pythonhosted.org/packages/aa/bb/cc/x-1.0.tar.gz",
  "https://repo1.maven.org/maven2/org/foo/bar/1.0/bar-1.0.jar",
  "https://static.crates.io/crates/serde/serde-1.0.0.crate",
  "https://cran.r-project.org/src/contrib/abc_1.0.tar.gz",
  "https://hackage.haskell.org/package/aeson-2.0",
  "https://sourceforge.net/projects/x/files/x-1.0.tar.gz/download",
  "pkg:gem/rails@7.0.0", "pkg:npm/%40scope/name@1.0.0",
  "AV:N/AC:L/Au:N/C:P/I:P/A:P", "CVSS:3.1/AV:N/AC:L/PR:N/UI:N/S:U/C:H/I:H/A:H",
  "%2F", "%zz", "a b", "A B", "ALPHA", "Beta3", "rc", "p12", "post1",
  "x-linux", "x-darwin", "java", "mswin32_100", "gnu-linux-gnu",
  "1.2.3\n", "\n1.2.3", "a\nb", "  1.2.3  ", "-", ".", "..", "1..2"
].freeze

ADVERSARIAL = [
  # greedy vs lazy, and which capture survives
  ["(a+)(a*)", 0, %w[aaaa a aa]],
  ["(a+?)(a*)", 0, %w[aaaa a]],
  ["(.*)-(.*)", 0, ["a-b-c", "-", "a-"]],
  ["(.*?)-(.*)", 0, ["a-b-c", "-"]],
  # empty-body repetition must terminate and must not loop
  ["(a*)*", 0, ["", "b", "aaa"]],
  ["(a?)*b", 0, ["b", "ab", "aaab"]],
  ["(|a)*", 0, ["aaa", ""]],
  # captures must be restored on backtracking
  ["(a)|(b)", 0, %w[a b c]],
  ["((a)|b)+", 0, %w[ab ba bb]],
  ["(a(b)?)+", 0, %w[aba aab a]],
  # alternation preference is leftmost, not longest
  ["a|ab", 0, ["ab"]],
  ["(ab|a)(b?)", 0, ["ab"]],
  # bounded repetition
  ["a{2}", 0, %w[a aa aaa]],
  ["a{2,}", 0, %w[a aaaa]],
  ["a{,2}b", 0, %w[b ab aab aaab]],
  ["a{1,2}", 0, %w[a aa aaa]],
  # anchors
  ["\\A\\d+\\z", 0, ["12", "12\n", "a12"]],
  ["\\A\\d+\\Z", 0, ["12", "12\n", "12\n\n"]],
  ["^b", 0, ["a\nb", "b", "ab"]],
  ["a$", 0, ["a\nb", "a", "ba\n"]],
  ["^$", 0, ["", "\n", "a\n\nb"]],
  # dot and multiline
  ["a.b", 0, ["a\nb", "axb"]],
  ["a.b", 4, ["a\nb", "axb"]],
  # classes
  ["[^a-c]+", 0, ["abcd", "abc", "dea"]],
  ["[]a]+", 0, ["]a", "a]"]],
  ["[a-]+", 0, ["a-a", "-"]],
  ["[\\d.]+", 0, ["1.2x", "x"]],
  ["[^\\d]+", 0, ["ab1", "12"]],
  # case folding, including the inline form
  ["ABC", 1, %w[abc ABC AbC]],
  ["(?i:beta)\\d", 0, ["BETA1", "beta1", "Beta1"]],
  ["(?i)rc\\d", 0, ["RC2", "rc2"]],
  ["[a-f]+", 1, %w[ABC abc XYZ]],
  # lookahead
  ["a(?=b)", 0, %w[ab ac]],
  ["a(?!b)", 0, %w[ab ac a]],
  ["(?!-|api/)([^/]+)", 0, ["-x", "api/x", "ok"]],
  # nested groups and named groups
  ["((a)(b))c", 0, ["abc"]],
  ["\\AHEAD(?:-(?<commit>.*))?\\Z", 0, ["HEAD", "HEAD-abc", "HEADX"]],
  # extended mode
  ["a  b  # comment\n  c", 2, %w[abc ab]],
  # a pathological-looking but bounded case: the engine must answer, not hang
  ["(a+)+b", 0, ["aaaaaaaaac", "aaaaaaaaab"]]
].freeze

lines = []
harvest.each do |pat, opts|
  INPUTS.each { |i| lines << [pat, opts, i] }
end
ADVERSARIAL.each do |pat, opts, inputs|
  inputs.each { |i| lines << [pat, opts, i] }
end

# The probe protocol is line- and tab-delimited, and both newlines and tabs are
# load-bearing test data (`\Z` before a trailing newline; `^`/`$` as line
# anchors), so they travel as tokens rather than being skipped. Both probes
# decode them.
def enc(s)
  s.gsub("\n", "<NL>").gsub("\t", "<TAB>")
end

lines.each { |pat, opts, inp| puts [enc(pat), opts, enc(inp)].join("\t") }
