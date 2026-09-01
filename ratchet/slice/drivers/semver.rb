# Driver for `vulns/semver.rb` — SemVer 2.0 §11 comparison, exercised as the
# advisory pipeline exercises it: one `Semver.compare(a, b)` per pair.
#
# Real calls only; nothing here reimplements the file. Output discipline (N38):
# every line is process-independent — no addresses, no hashes, no iteration over
# an unordered structure.

def show(label)
  puts("#{label} => #{yield.inspect}")
rescue StandardError => e
  puts("#{label} => #{e.class}: #{e.message}")
end

S = Homebrew::Vulns::Semver

puts("== the ordering, pair by pair")
[
  ["1.0.0", "1.0.0"],            # equal
  ["1.0.1", "1.0.0"],            # patch
  ["1.1.0", "1.0.9"],            # minor beats patch
  ["2.0.0", "1.99.99"],          # major beats everything
  ["1.0", "1.0.0"],              # minor/patch may be omitted
  ["1", "1.0.0"],
  ["v1.2.3", "1.2.3"],           # a `v` prefix is stripped
  ["V1.2.3", "1.2.3"],
  ["  1.2.3  ", "1.2.3"],        # and surrounding space
  ["1.0.0-rc1", "1.0.0"],        # §11.3: a prerelease sorts below its release
  ["1.0.0-alpha", "1.0.0-alpha.1"],
  ["1.0.0-alpha.1", "1.0.0-alpha.beta"],
  ["1.0.0-alpha.beta", "1.0.0-beta"],
  ["1.0.0-beta.2", "1.0.0-beta.11"],   # §11.4.1: numeric identifiers compare numerically
  ["1.0.0-1", "1.0.0-alpha"],          # §11.4.3: numeric sorts below alphanumeric
  ["1.0.0+build", "1.0.0"],            # §10: build metadata is ignored
  ["1.0.0+a", "1.0.0+b"],
  ["1.0.0-rc1+a", "1.0.0-rc1+b"],
].each { |a, b| show("  #{a} <=> #{b}") { S.compare(a, b) } }

puts
puts("== spec violations answer nil, so callers can fall through")
[
  ["01.0.0", "1.0.0"],           # leading zero in a core segment
  ["1.0.0-", "1.0.0"],           # empty prerelease
  ["1.0.0-01", "1.0.0"],         # leading zero in a numeric identifier
  ["1.2.3.4", "1.2.3"],          # four core segments
  ["not a version", "1.0.0"],
  ["", "1.0.0"],
  ["1.0.0", "garbage"],
].each { |a, b| show("  #{a} <=> #{b}") { S.compare(a, b) } }

puts
puts("== the ordering is a total order on what it accepts")
# Sorting through `compare` is the use the advisory ranges actually make of it.
vs = ["1.0.0", "1.0.0-rc1", "0.9.9", "1.0.0+build", "1.0.0-alpha", "2.0.0", "1.0.1"]
show("sorted") { vs.sort { |a, b| S.compare(a, b) || 0 } }
show("is 1.0.0-rc1 < 1.0.0 < 1.0.1?") do
  (S.compare("1.0.0-rc1", "1.0.0") == -1) && (S.compare("1.0.0", "1.0.1") == -1)
end
