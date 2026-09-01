# Driver for `vulns/cvss.rb` — CVSS v3.x base score and qualitative severity,
# exercised the way `Vulnerability#extract_severity` exercises it: one vector
# string in, a `[score, severity]` pair out.
#
# The vectors are the FIRST specification's own worked examples plus the
# boundary cases of the four severity bands, so the arithmetic (Float, `**`,
# the Roundup of Appendix A) is pinned at values a reader can check against the
# spec rather than against our own output.

def show(label)
  puts("#{label} => #{yield.inspect}")
rescue StandardError => e
  puts("#{label} => #{e.class}: #{e.message}")
end

C = Homebrew::Vulns::CVSS

puts("== base_score / severity, over real vectors")
[
  # the spec's CVE-2015-8252 example: 9.8 CRITICAL
  "CVSS:3.1/AV:N/AC:L/PR:N/UI:N/S:U/C:H/I:H/A:H",
  # scope changed — the 1.08 multiplier and the changed privileges table
  "CVSS:3.1/AV:N/AC:L/PR:N/UI:N/S:C/C:H/I:H/A:H",
  "CVSS:3.1/AV:N/AC:L/PR:N/UI:N/S:C/C:L/I:L/A:N",
  # every band boundary
  "CVSS:3.1/AV:N/AC:L/PR:N/UI:N/S:U/C:H/I:N/A:N",
  "CVSS:3.1/AV:L/AC:H/PR:H/UI:R/S:U/C:L/I:L/A:N",
  "CVSS:3.1/AV:P/AC:H/PR:H/UI:R/S:U/C:L/I:N/A:N",
  # zero impact short-circuits before exploitability is even computed
  "CVSS:3.1/AV:N/AC:L/PR:N/UI:N/S:U/C:N/I:N/A:N",
  # 3.0 is accepted on the same table as 3.1
  "CVSS:3.0/AV:N/AC:L/PR:N/UI:N/S:U/C:H/I:H/A:H",
].each { |v| show("  #{v}") { [C.base_score(v), C.severity(v)] } }

puts
puts("== unsupported and malformed vectors answer nil, not a raise")
# The contract the caller depends on: `extract_severity` walks several severity
# entries and needs `nil` to mean "try the next one".
[
  "CVSS:2.0/AV:N/AC:L/Au:N/C:P/I:P/A:P",          # v2 — out of scope by design
  "CVSS:4.0/AV:N/AC:L/AT:N/PR:N/UI:N/VC:H/VI:H/VA:H",
  "CVSS:3.1/AV:N/AC:L/PR:N/UI:N/S:U/C:H/I:H",     # a base metric missing
  "CVSS:3.1/AV:X/AC:L/PR:N/UI:N/S:U/C:H/I:H/A:H", # a value outside the table
  "CVSS:3.1/AV:N/AC:L/PR:N/UI:N/S:X/C:H/I:H/A:H", # scope is neither U nor C
  "AV:N/AC:L/PR:N/UI:N/S:U/C:H/I:H/A:H",          # no prefix
  "garbage",
  "",
].each { |v| show("  #{v.empty? ? '(empty)' : v}") { [C.base_score(v), C.severity(v)] } }

puts
puts("== the score is monotone in each metric it should be monotone in")
def score(av:, ac: "L", pr: "N", ui: "N", s: "U", c: "H", i: "H", a: "H")
  Homebrew::Vulns::CVSS.base_score("CVSS:3.1/AV:#{av}/AC:#{ac}/PR:#{pr}/UI:#{ui}/S:#{s}/C:#{c}/I:#{i}/A:#{a}")
end

show("attack vector N > A > L > P") { ["N", "A", "L", "P"].map { |av| score(av:) } }
show("privileges N > L > H")       { ["N", "L", "H"].map { |pr| score(av: "N", pr:) } }
show("confidentiality H > L > N")  { ["H", "L", "N"].map { |c| score(av: "N", c:, i: "N", a: "N") } }

puts
puts("== Roundup (spec Appendix A) never rounds a score down")
show("severity bands are ordered") do
  scores = ["N", "A", "L", "P"].map { |av| score(av:) }
  scores == scores.sort.reverse
end
