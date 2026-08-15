"""The input-parameterized driver (R1): the slice's decision core, driven over
generated advisory *shapes* × version strings.

This is `slice-driver/driver.rb` with its one hard-coded advisory replaced by an
input, which is the whole point of R1 — the driver is a demonstration with a
single result, and this is a function of its inputs. The three calls are exactly
the three `vulns/match.rb` makes into the slice (`nontrivial-target.md` §2),
plus the aggregation `match.rb` applies to their results, which lives in an
excluded file and is therefore **transcribed and labelled as transcribed**.

Every line is process-independent (N38). Two normalizations earn that:

* `0x…` addresses, as everywhere else in this corpus;
* sorbet's `Caller:` / `Definition:` lines, which carry the *file path* of the
  program — a temp directory here. The blame outcome itself is kept (§5.4 calls
  it a licensed outcome, so a change to it must be visible); only the path goes.

`Object#hash` is never printed: a `sig` failing on a plain object makes sorbet
print `with hash <n>`, which is per-process seeded (L127) — the model gates
there rather than invent a number, so such a case is reported as a gate.
"""

from __future__ import annotations

BODY = r'''
V = Homebrew::Vulns::Vulnerability

def norm(s)
  s.to_s.gsub(/0x[0-9a-f]+/, "0xADDR").gsub(/\n?(Caller|Definition): [^\n]*/, "")
end

def outcome
  r = yield
  r.nil? ? "nil" : norm(r.inspect)
rescue StandardError => e
  "E:" + e.class.to_s + ": " + norm(e.message)
end

# `match.rb`'s `evidence_range_status` aggregation, transcribed: any affected
# subject wins over a fixed one, and a fixed one over anything else. It lives in
# an excluded file, so this is the one line here that is not the slice's own.
def aggregate(statuses)
  hit = statuses.find { |s| !s.nil? && s.affected? }
  hit = statuses.find { |s| !s.nil? && s.fixed? } if hit.nil?
  hit = statuses.first if hit.nil?
  hit.nil? ? "nil" : norm(hit.inspect)
rescue StandardError => e
  "E:" + e.class.to_s + ": " + norm(e.message)
end

puts("advisory " + CASE_ID)
INPUTS.each do |ver|
  print(ver.inspect, "\t")
  print(outcome { V.new(ADVISORY).range_status(ECOSYSTEM, NAME, ver) }, "\t")
  print(outcome { V.new(ADVISORY).affects_version?(ver) }, "\t")
  print(outcome { V.new(ADVISORY).fixed_versions }, "\t")
  print(outcome { V.new(ADVISORY).severity_display }, "\t")
  print(aggregate([begin
                     V.new(ADVISORY).range_status(ECOSYSTEM, NAME, ver)
                   rescue StandardError
                     nil
                   end]))
  puts("")
end
'''


def program(case_id: str, advisory_lit: str, versions: list[str],
            prefix: str, preamble: str, mutations: list[str]) -> str:
    from .gen import ECOSYSTEM, NAME, _dq
    head = "".join(f"# mutation: {m}\n" for m in mutations)
    lits = ",\n  ".join(_dq(v) for v in versions)
    return (head + preamble + prefix
            + f"\nCASE_ID = {_dq(case_id)}\n"
            + f"ECOSYSTEM = {_dq(ECOSYSTEM)}\n"
            + f"NAME = {_dq(NAME)}\n"
            + f"ADVISORY = {advisory_lit}.freeze\n"
            + "INPUTS = [\n  " + lits + "\n].freeze\n" + BODY)
