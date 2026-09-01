# Driver for `pkg_version.rb` — a `Version` plus a packaging `revision`, the pair
# Homebrew installs under. Small (8 `def`s) and almost entirely *delegation*:
# `include Comparable`, `extend Forwardable`, a `delegate` of five readers to the
# wrapped version, and an `alias`. So the driver's job is to show the delegation
# and the composite ordering actually working, not to re-test `Version`.

def show(label)
  puts("#{label} => #{yield.inspect}")
rescue StandardError => e
  puts("#{label} => #{e.class}: #{e.message}")
end

puts("== parsing the on-disk form (`<version>_<revision>`)")
[
  "1.2.3", "1.2.3_1", "1.2.3_2", "1.2.3_0", "2.0", "HEAD", "HEAD_1",
  "1.2.3_1_2",      # only the last `_N` is a revision
  "not_a_version",  # `_a_version` is not `_\d+`, so the whole string is the version
  "",
].each { |p| show("  #{p.inspect}") { v = PkgVersion.parse(p); [v.to_s, v.version.to_s, v.revision] } }

puts
puts("== construction, and `to_s`/`to_str`")
[["1.2.3", 0], ["1.2.3", 1], ["1.2.3", 12], ["HEAD", 3]].each do |v, r|
  show("  #{v} rev #{r}") do
    pv = PkgVersion.new(Version.new(v), r)
    [pv.to_s, pv.to_str, "interpolated: #{pv}"]
  end
end

puts
puts("== the composite ordering: version first, revision as the tiebreak")
[
  ["1.2.3_1", "1.2.3_2"],
  ["1.2.3_2", "1.2.3_1"],
  ["1.2.3_1", "1.2.3_1"],
  ["1.2.3", "1.2.3_1"],     # an absent revision is 0
  ["1.2.4", "1.2.3_9"],     # the version wins over any revision
  ["1.10", "1.9_9"],
  ["HEAD", "1.2.3_9"],
].each { |a, b| show("  #{a} <=> #{b}") { PkgVersion.parse(a) <=> PkgVersion.parse(b) } }

puts
puts("== `include Comparable` is what turns that `<=>` into the operators")
a = PkgVersion.parse("1.2.3_1")
b = PkgVersion.parse("1.2.3_2")
show("a < b")            { a < b }
show("a > b")            { a > b }
show("a == a")           { a == PkgVersion.parse("1.2.3_1") }
show("a.between?(a, b)") { a.between?(a, b) }
show("a.clamp(a, b)")    { a.clamp(a, b).to_s }
show("sorted")           { %w[1.2.3_2 1.10 1.2.3 1.9_1].sort_by { |s| PkgVersion.parse(s) }.map(&:to_s) }

puts
puts("== `extend Forwardable`: the five readers delegated to the version")
pv = PkgVersion.parse("1.2.3_1")
[:major, :major_minor, :major_minor_patch].each { |m| show("  #{m}") { pv.public_send(m).to_s } }
show("  head?")    { PkgVersion.parse("HEAD_1").head? }
show("  version")  { pv.version.to_s }
show("  revision") { pv.revision }
