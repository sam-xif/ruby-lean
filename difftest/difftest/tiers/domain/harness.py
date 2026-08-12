"""Fixed harness programs that drive the slice over generated inputs (W4d).

Each harness is `library prefix + a literal input array + a loop that prints one
line per input`. The loop rescues, so a raise is an observation rather than the
end of the program, and every operation is printed — a model bug that changes a
*value* is caught even where a boolean verdict would not move.

The harnesses are where the plan's headline question lives: `pairs` runs
`Version.new(a) <=> Version.new(b)` and `Semver.compare(a, b)` **on the same
pair** and prints both, which is W4e's disagreement search reduced to a
difftest case. Here it is being used for its other purpose — agreement between
CRuby and the model — but the same programs answer both questions.
"""

from __future__ import annotations

HARNESSES = {
    # ── Version: construction, rendering, comparison, URL parsing ──────────
    "version": {
        "feature": "version",
        "kind": "version",
        "body": '''
INPUTS.each do |s|
  print(s.inspect, "\\t")
  begin
    v = Version.new(s)
    print([v.to_s, v.major.to_s, v.minor.to_s, v.patch.to_s].inspect)
  rescue StandardError => e
    print("E:", e.class.to_s)
  end
  print("\\t")
  begin
    print((Version.new(s) <=> Version.new(s)).inspect)
  rescue StandardError => e
    print("E:", e.class.to_s)
  end
  puts("")
end
''',
    },
    # ── the headline pair: two orderings on the same inputs ────────────────
    "pairs": {
        "feature": "vulns/semver",
        "kind": "semver",
        "extra_features": ["version"],
        "body": '''
i = 0
while i + 1 < INPUTS.length
  a = INPUTS[i]
  b = INPUTS[i + 1]
  i += 2
  print(a.inspect, "\\t", b.inspect, "\\t")
  begin
    print(Homebrew::Vulns::Semver.compare(a, b).inspect)
  rescue StandardError => e
    print("E:", e.class.to_s)
  end
  print("\\t")
  begin
    print((Version.new(a) <=> Version.new(b)).inspect)
  rescue StandardError => e
    print("E:", e.class.to_s)
  end
  puts("")
end
''',
    },
    # ── SemVer parse + compare against itself and its neighbours ───────────
    "semver": {
        "feature": "vulns/semver",
        "kind": "semver",
        "body": '''
INPUTS.each do |s|
  print(s.inspect, "\\t")
  begin
    print(Homebrew::Vulns::Semver.compare(s, "1.0.0").inspect)
  rescue StandardError => e
    print("E:", e.class.to_s)
  end
  print("\\t")
  begin
    print(Homebrew::Vulns::Semver.compare(s, s).inspect)
  rescue StandardError => e
    print("E:", e.class.to_s)
  end
  puts("")
end
''',
    },
    # ── package URLs ───────────────────────────────────────────────────────
    "purl": {
        "feature": "vulns/purl",
        "kind": "purl",
        "body": '''
INPUTS.each do |s|
  print(s.inspect, "\\t")
  begin
    p = Homebrew::Vulns::Purl.parse(s)
    print(p.nil? ? "nil" : [p.type, p.name, p.version, p.to_s].inspect)
  rescue StandardError => e
    print("E:", e.class.to_s)
  end
  puts("")
end
''',
    },
    # ── forge URLs → OSV query keys ────────────────────────────────────────
    "identify": {
        "feature": "vulns/identify",
        "kind": "url",
        "body": '''
INPUTS.each do |s|
  print(s.inspect, "\\t")
  begin
    r = Homebrew::Vulns::Identify.registry_package(s)
    print(r.nil? ? "nil" : r.to_h.inspect)
  rescue StandardError => e
    print("E:", e.class.to_s)
  end
  puts("")
end
''',
    },
}


def program(name: str, inputs: list[str], prefix: str, preamble: str) -> str:
    h = HARNESSES[name]
    lits = ",\n  ".join(_dq(i) for i in inputs)
    return (preamble + prefix
            + "\nINPUTS = [\n  " + lits + "\n].freeze\n" + h["body"])


def _dq(s: str) -> str:
    """A Ruby double-quoted literal. The generator emits only printable ASCII,
    so escaping `\\` and `"` is enough — and `#` has to go too, or `#{`…`}` in a
    generated version string would interpolate."""
    out = s.replace("\\", "\\\\").replace('"', '\\"').replace("#", "\\#")
    return '"' + out + '"'
