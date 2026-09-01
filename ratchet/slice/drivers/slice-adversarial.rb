# Driver for the whole linked slice, driven by **inputs it did not choose** — the
# ratchet's copy of `homebrew/slice-driver/probes/adversarial-inputs.rb`.
#
# This is the tier's one permanent negative (`unsafe_program`). The probe's point
# is that the unrestricted-input program *is not type-safe*: `range_status` and
# `affects_version?` reach `ArgumentError` (from `Version.new("")`) and
# `TypeError` (from `Integer#[]`) on advisory shapes a caller can supply, and two
# of those are reachable from a schema-conformant record. A checker that
# certified this program would be unsound, so the recorded target is `false` and
# it must stay `false`.
#
# One row of the upstream probe is dropped: `V.new({ "id" => 5 })` raises through
# sorbet-runtime's `T.let`, whose message carries the **caller's file path** —
# process-dependent output, and the model does not enforce sigs, so the two
# executors disagree on it by construction (N38). The `TypeError` the probe is
# about is reached by the `ranges: [1]` row regardless.

def show(label)
  puts("#{label} => #{yield.inspect}")
rescue StandardError => e
  puts("#{label} => #{e.class}: #{e.message}")
end

V = Homebrew::Vulns::Vulnerability

def adv(affected)
  { "id" => "GHSA-probe", "affected" => affected }
end

PKG = { "ecosystem" => "Homebrew", "name" => "libexample" }

def eco_range(events)
  [{ "package" => PKG, "ranges" => [{ "type" => "ECOSYSTEM", "events" => events }] }]
end

def semver_range(events)
  [{ "package" => PKG, "ranges" => [{ "type" => "SEMVER", "events" => events }] }]
end

WELL_FORMED = adv(eco_range([{ "introduced" => "1.0" }, { "fixed" => "2.0" }])).freeze

puts("== control: a well-formed advisory")
show("range_status 1.5") { V.new(WELL_FORMED).range_status("Homebrew", "libexample", "1.5") }
show("range_status 2.5") { V.new(WELL_FORMED).range_status("Homebrew", "libexample", "2.5") }

puts("== the version string is an input (from the formula)")
show("version 'v'")     { V.new(WELL_FORMED).range_status("Homebrew", "libexample", "v") }
show("version ''")      { V.new(WELL_FORMED).range_status("Homebrew", "libexample", "") }
show("version 'HEAD'")  { V.new(WELL_FORMED).range_status("Homebrew", "libexample", "HEAD") }

puts("== the advisory is an input (from the network)")
show("ranges: [1]") do
  V.new(adv([{ "package" => PKG, "ranges" => [1] }]))
   .range_status("Homebrew", "libexample", "1.5")
end
show("ranges: ['x']") do
  V.new(adv([{ "package" => PKG, "ranges" => ["x"] }]))
   .range_status("Homebrew", "libexample", "1.5")
end
show("affected: [[1, 2]]") do
  V.new(adv([[1, 2]])).range_status("Homebrew", "libexample", "1.5")
end
show("empty fixed event") do
  V.new(adv(eco_range([{ "introduced" => "1.0" }, { "fixed" => "" }])))
   .range_status("Homebrew", "libexample", "1.5")
end
show("introduced: 'v'") do
  V.new(adv(eco_range([{ "introduced" => "v" }])))
   .range_status("Homebrew", "libexample", "1.5")
end
show("events: [{}]") do
  V.new(adv(eco_range([{}]))).range_status("Homebrew", "libexample", "1.5")
end
show("events: 'x'") do
  V.new(adv([{ "package" => PKG, "ranges" => [{ "type" => "ECOSYSTEM", "events" => "x" }] }]))
   .range_status("Homebrew", "libexample", "1.5")
end
show("versions: [nil]") do
  V.new(adv([{ "package" => PKG, "versions" => [nil] }]))
   .range_status("Homebrew", "libexample", "1.5")
end
show("no id at all")           { V.new({}).range_status("Homebrew", "libexample", "1.5") }
show("affects_version? empty fixed") do
  V.new(adv(semver_range([{ "introduced" => "1.0.0" }, { "fixed" => "" }])))
   .affects_version?("1.5.0")
end
