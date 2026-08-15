"""A structural generator for OSV **advisory records** — rung R1 of
`homebrew/nontrivial-target.md` §6.

W4d generates the slice's *string* inputs (versions, semvers, purls, URLs). This
generates its other input, and the one the plan calls untrusted: the advisory
Hash that `vulns/match.rb` hands `Vulnerability.new` straight out of
`JSON.parse` of an HTTP body, with no schema validation of the record
(`nontrivial-target.md` §3.1).

Two design choices, both forced by what P1′ says "arbitrary" means (§5.1):

* **The domain is the JSON algebraic datatype**, not a string grammar: nested
  Hash / Array / String / Integer / Float / bool / nil with String keys. That is
  exactly what the network can hand us, and it is what makes an invariant
  statable — where P3's "every version field matches SEMVER_REGEX" would have
  needed the regex's language.
* **Skeleton plus mutation, not uniform random.** A uniformly random JSON value
  fails the `sig` on `initialize` and tests nothing past it. Every case starts
  from a structurally faithful OSV record and then has *k* nodes replaced,
  deleted or retyped — which is how a hand-edited advisory-database entry or a
  generated `BREW-*` record actually goes wrong, and it is the split
  `probes/malformed-shapes.rb` measured: a wrong **scalar** type is survived, a
  wrong **container shape** raises.

Deterministic given a seed, so a disagreement replays.
"""

from __future__ import annotations

import copy
import random
from typing import Any

from ..domain import version_gen

ECOSYSTEM = "Homebrew"
NAME = "libexample"

# Version lexemes the *caller* supplies (a formula's version, or a resource's
# pinned one). The three at the front are §3.1's witnesses: `normalize_version`
# strips a leading `v`, so "v" becomes "" and `version.rb:503` raises.
ADVERSARIAL_VERSIONS = ["", "v", "V", "HEAD", "0", " 1.0 ", "1.0.0+build"]

RANGE_TYPES = ["SEMVER", "ECOSYSTEM", "GIT", "semver", "", "OTHER"]
EVENT_KEYS = ["introduced", "fixed", "last_affected", "limit"]

# The leaves an arbitrary `JSON.parse` can produce. Floats are kept to values
# whose Python and Ruby literals agree exactly; there is no NaN or Infinity in
# JSON, so excluding them is faithful rather than convenient.
SCALARS: list[Any] = [None, True, False, 0, 1, -1, 5, 2.0, 0.5, "", "x", "1.0",
                      "v", "0x10", "1.0.0-rc.1"]


def _version(r: random.Random) -> str:
    if r.random() < 0.25:
        return r.choice(ADVERSARIAL_VERSIONS)
    if r.random() < 0.5:
        return version_gen.semver_string(r)
    return version_gen.version_string(r)


def _json_value(r: random.Random, depth: int = 0) -> Any:
    """An arbitrary `JSON.parse` result, biased shallow."""
    if depth >= 2 or r.random() < 0.55:
        return r.choice(SCALARS)
    if r.random() < 0.5:
        return [_json_value(r, depth + 1) for _ in range(r.randint(0, 2))]
    return {r.choice(["type", "events", "a", "0", ""]): _json_value(r, depth + 1)
            for _ in range(r.randint(0, 2))}


# ── the skeleton ───────────────────────────────────────────────────────────

def _events(r: random.Random) -> list[dict]:
    out: list[dict] = [{"introduced": _version(r)}]
    roll = r.random()
    if roll < 0.55:
        out.append({"fixed": _version(r)})
    elif roll < 0.75:
        out.append({"last_affected": _version(r)})
    return out


def _range(r: random.Random) -> dict:
    return {"type": r.choice(RANGE_TYPES[:2] if r.random() < 0.85 else RANGE_TYPES),
            "events": _events(r)}


def _affected_entry(r: random.Random) -> dict:
    e: dict[str, Any] = {"package": {"ecosystem": ECOSYSTEM, "name": NAME}}
    if r.random() < 0.85:
        e["ranges"] = [_range(r) for _ in range(r.randint(1, 2))]
    if r.random() < 0.35:
        e["versions"] = [_version(r) for _ in range(r.randint(1, 3))]
    return e


def skeleton(r: random.Random) -> dict:
    a: dict[str, Any] = {
        "id": "GHSA-" + "".join(r.choice("abcdefghjkmnpqrstvwxyz") for _ in range(4)),
        "affected": [_affected_entry(r) for _ in range(r.randint(1, 2))],
    }
    if r.random() < 0.4:
        a["summary"] = "generated advisory"
    if r.random() < 0.3:
        a["severity"] = [{"type": "CVSS_V3",
                          "score": "CVSS:3.1/AV:N/AC:L/PR:N/UI:N/S:U/C:H/I:H/A:H"}]
    if r.random() < 0.2:
        a["aliases"] = ["CVE-2024-0001"]
    return a


# ── mutation: walk to a node, then break it the way JSON breaks ────────────

def _paths(node: Any, prefix: tuple = ()) -> list[tuple]:
    out = [prefix]
    if isinstance(node, dict):
        for k, v in node.items():
            out += _paths(v, prefix + (k,))
    elif isinstance(node, list):
        for i, v in enumerate(node):
            out += _paths(v, prefix + (i,))
    return out


def _at(node: Any, path: tuple) -> Any:
    for p in path:
        node = node[p]
    return node


def _set(node: Any, path: tuple, value: Any) -> None:
    for p in path[:-1]:
        node = node[p]
    node[path[-1]] = value


def _delete(node: Any, path: tuple) -> None:
    for p in path[:-1]:
        node = node[p]
    del node[path[-1]]


def mutate(r: random.Random, adv: dict, k: int) -> tuple[dict, list[str]]:
    """`k` structural mutations, each reported so a red row names its own cause."""
    adv = copy.deepcopy(adv)
    log: list[str] = []
    for _ in range(k):
        paths = [p for p in _paths(adv) if p]  # never the root: the sig owns it
        if not paths:
            break
        path = r.choice(paths)
        cur = _at(adv, path)
        kind = r.random()
        try:
            if kind < 0.30:
                # the realistic one: an object where the schema says
                # array-of-objects, or the reverse (`probes/malformed-shapes.rb`)
                if isinstance(cur, list) and cur and isinstance(cur[0], dict):
                    _set(adv, path, cur[0])
                    log.append(f"unwrap-list {'.'.join(map(str, path))}")
                elif isinstance(cur, dict):
                    _set(adv, path, [cur])
                    log.append(f"wrap-object {'.'.join(map(str, path))}")
                else:
                    _set(adv, path, [cur])
                    log.append(f"wrap-scalar {'.'.join(map(str, path))}")
            elif kind < 0.55:
                v = _json_value(r)
                _set(adv, path, v)
                log.append(f"retype {'.'.join(map(str, path))}={v!r}")
            elif kind < 0.75:
                _delete(adv, path)
                log.append(f"delete {'.'.join(map(str, path))}")
            elif kind < 0.90 and isinstance(cur, dict):
                cur[r.choice(["type", "events", "extra"])] = _json_value(r)
                log.append(f"addkey {'.'.join(map(str, path))}")
            else:
                _set(adv, path, _version(r) if isinstance(cur, str) else _json_value(r))
                log.append(f"reshape {'.'.join(map(str, path))}")
        except (KeyError, IndexError, TypeError):
            continue
    return adv, log


# ── the six witnesses of `nontrivial-target.md` §3, as the seed corpus ─────

def _pkg() -> dict:
    return {"ecosystem": ECOSYSTEM, "name": NAME}


def _eco(events: list[dict]) -> list[dict]:
    return [{"package": _pkg(), "ranges": [{"type": "ECOSYSTEM", "events": events}]}]


WITNESSES: list[tuple[str, dict, list[str]]] = [
    # (label, advisory, versions) — §3.2a ranks these; the first two are
    # schema-conformant and so the most realistic.
    ("w1-version-v",
     {"id": "GHSA-w1", "affected": _eco([{"introduced": "1.0"}, {"fixed": "2.0"}])},
     ["v", "", "1.5"]),
    ("w2-event-blank-fixed",
     {"id": "GHSA-w2", "affected": _eco([{"introduced": "1.0"}, {"fixed": ""}])},
     ["1.5"]),
    ("w3-event-introduced-v",
     {"id": "GHSA-w3", "affected": _eco([{"introduced": "v"}])},
     ["1.5"]),
    ("w4-ranges-integer",
     {"id": "GHSA-w4", "affected": [{"package": _pkg(), "ranges": [1]}]},
     ["1.5"]),
    ("w5-affected-nested-array",
     {"id": "GHSA-w5", "affected": [[1, 2]]},
     ["1.5"]),
    ("w6-range-is-object",
     {"id": "GHSA-w6",
      "affected": [{"package": _pkg(),
                    "ranges": {"type": "ECOSYSTEM",
                               "events": [{"introduced": "1.0"}]}}]},
     ["1.5"]),
    # the two out-of-family outcomes §5.4 names, kept so a change to either is
    # visible rather than silent
    ("x1-no-id", {}, ["1.5"]),
    ("x2-silent-verdict",
     {"id": "GHSA-x2", "affected": [{"package": _pkg(), "ranges": ["x"]}]},
     ["1.5"]),
]


def cases(n: int, seed: int, versions_per: int = 8) -> list[dict]:
    """`n` counts (advisory × version) pairs. One advisory per program, so a
    shape that gates costs only its own rows — a gate refuses the *whole*
    program, and this corpus is expected to find gates (§3.3)."""
    r = random.Random(seed)
    out = [{"id": f"witness-{lbl}", "advisory": adv, "versions": vs,
            "mutations": ["(seed witness)"]}
           for lbl, adv, vs in WITNESSES]
    remaining = max(0, n - sum(len(c["versions"]) for c in out))
    for i in range(remaining // versions_per):
        base = skeleton(r)
        k = r.choice([0, 0, 1, 1, 1, 2, 2, 3])
        adv, log = mutate(r, base, k) if k else (base, [])
        out.append({"id": f"gen-{seed}-{i:04d}", "advisory": adv,
                    "versions": [_version(r) for _ in range(versions_per)],
                    "mutations": log or ["(unmutated)"]})
    return out


# ── Ruby literal rendering ─────────────────────────────────────────────────

def to_ruby(v: Any) -> str:
    if v is None:
        return "nil"
    if v is True:
        return "true"
    if v is False:
        return "false"
    if isinstance(v, str):
        return _dq(v)
    if isinstance(v, int):
        return str(v)
    if isinstance(v, float):
        # Python and Ruby agree on the shortest round-tripping literal for the
        # values in SCALARS; anything else would be an oracle question of its own
        return repr(v)
    if isinstance(v, list):
        return "[" + ", ".join(to_ruby(x) for x in v) + "]"
    if isinstance(v, dict):
        return "{" + ", ".join(f"{_dq(str(k))} => {to_ruby(x)}"
                               for k, x in v.items()) + "}"
    raise TypeError(f"not a JSON value: {v!r}")


def _dq(s: str) -> str:
    """A Ruby double-quoted literal. `#` is escaped too, or a generated string
    containing `#{` would interpolate (the same trap `version_gen` has)."""
    out = (s.replace("\\", "\\\\").replace('"', '\\"').replace("#", "\\#")
            .replace("\n", "\\n").replace("\t", "\\t"))
    return '"' + out + '"'
