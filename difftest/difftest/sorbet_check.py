"""The static oracle: what Sorbet says vs. what the program actually does.

`srb tc` is an *oracle*, not truth. Sorbet is unsound by design (§A.3), so
"accepted" is not a safety claim, and "rejected" is not a bug report. What is
informative is the **two-by-two** of static verdict against actual runtime
outcome, and in particular its off-diagonal cells:

  static clean + uncaught type-family error  ->  UNSOUNDNESS WITNESS. Sorbet
      accepted a program that reaches a type-stuck outcome in exactly the sense
      the reachability checker means (`../ruby-lean/AGENTS.md` §Type safety as reachability §2:
      NoMethodError / ArgumentError / TypeError escaping to toplevel). These
      are the seeds of the unsoundness catalogue.
  static errors + terminates normally        ->  CONSERVATIVE REJECTION. The
      program is safe on this run and Sorbet rejected it anyway — the DRuby
      false-positive family (§9.3 of `../ruby-lean/AGENTS.md` §Type safety as reachability), and the
      thing a semantics-driven checker claims to avoid by construction.

The command doubles as the corpus's integrity gate: each sidecar *declares*
both outcomes, and a mismatch fails the run. That keeps the corpus honest as
Sorbet versions move under it — the declarations are checked, not decorative.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

from .control import CRubyRunner
from .checker_relation import CHECK_CELLS, PINNED_ZERO_CELLS, excluded, relate, type_relevant
from .sorbet import FragmentChecker, SorbetStatic, StaticChecker, is_sorbet_runtime_error
from .testcase import TestCase

# Mirrors `typeErrorFamily` in ruby-lean/RubyCore/Proof/TypeSafety.lean. The Lean
# version tests membership with `isA`, so it is closed under subclassing; here
# the check is by class name, which agrees with it for the builtin classes the
# corpus raises. Note NoMethodError < NameError but a *bare* NameError is
# deliberately not in the family (an undefined constant/local is not a type
# error) — matching the Lean definition exactly.
TYPE_ERROR_FAMILY = ("NoMethodError", "ArgumentError", "TypeError")

# The cells of the two-by-two, named. Order matters: the report lists them in
# this order, findings first.
CELLS = {
    "unsoundness-witness": "srb accepted; an uncaught type-family error escaped",
    "conservative-rejection": "srb rejected; the program ran to completion",
    "accepted-blamed": "srb accepted; sorbet-runtime caught it at a boundary",
    "accepted-nontype-error": "srb accepted; a non-type-family error escaped",
    "rejected-and-unsafe": "srb rejected; an error escaped (true positive)",
    "rejected-and-blamed": "srb rejected; sorbet-runtime caught it too",
    "accepted-and-safe": "srb accepted; the program ran to completion",
}


def runtime_kind(exception: tuple[str, str] | None) -> str:
    """value | sorbet_error | ruby_error — the vocabulary the sidecars declare."""
    if exception is None:
        return "value"
    return "sorbet_error" if is_sorbet_runtime_error(exception) else "ruby_error"


def classify(static_ok: bool, kind: str, exc_class: str | None) -> str:
    if static_ok:
        if kind == "value":
            return "accepted-and-safe"
        if kind == "sorbet_error":
            return "accepted-blamed"
        return (
            "unsoundness-witness"
            if exc_class in TYPE_ERROR_FAMILY
            else "accepted-nontype-error"
        )
    if kind == "value":
        return "conservative-rejection"
    return "rejected-and-blamed" if kind == "sorbet_error" else "rejected-and-unsafe"


@dataclass
class CheckResult:
    case: TestCase
    static_ok: bool
    static_errors: list
    runtime_kind: str
    exception: tuple[str, str] | None
    stdout: str
    cell: str
    declared_static: str
    declared_runtime: str
    declared_check: str | None = None
    fragment: object = None  # FragmentResult | None ("cannot say")
    checker: object = None  # CheckResultLean | None ("cannot say")
    check_cell: str = "check-undecidable"

    @property
    def in_theorem_scope(self) -> bool:
        """In the provable subset AND accepted by srb — the set a soundness
        theorem would actually make a claim about."""
        return bool(self.fragment and self.fragment.in_fragment and self.static_ok)

    @property
    def matches_declaration(self) -> bool:
        """Corpus integrity. `check_expect` is **optional**: the 22 pre-existing
        tier-4 programs predate the checker and their verdicts will churn as the
        fragment widens, so requiring a declaration there would make every
        widening a 22-file edit. Where it *is* declared it is enforced — that
        catches a verdict silently flipping `accept` to `unknown`, which breaks
        no pinned zero and would otherwise pass unnoticed."""
        if (
            self.declared_check is not None
            and (self.checker.verdict if self.checker else None) != self.declared_check
        ):
            return False
        return (
            ("clean" if self.static_ok else "errors") == self.declared_static
            and self.runtime_kind == self.declared_runtime
        )

    def to_json(self) -> dict:
        return {
            "id": self.case.id,
            "category": self.case.provenance.get("category"),
            "sigil": self.case.provenance.get("sigil"),
            "cell": self.cell,
            "static": {
                "ok": self.static_ok,
                "errors": [e.to_json() for e in self.static_errors],
            },
            "runtime": {
                "kind": self.runtime_kind,
                "exception": list(self.exception) if self.exception else None,
                "stdout": self.stdout,
            },
            "declared": {
                "static_expect": self.declared_static,
                "runtime_expect": self.declared_runtime,
                "check_expect": self.declared_check,
            },
            "fragment": self.fragment.to_json() if self.fragment else None,
            "checker": self.checker.to_json() if self.checker else None,
            "check_cell": self.check_cell,
            "in_theorem_scope": self.in_theorem_scope,
            "matches_declaration": self.matches_declaration,
            "description": self.case.provenance.get("description"),
            "doc_ref": self.case.provenance.get("doc_ref"),
        }


def check_case(
    case: TestCase,
    static: SorbetStatic,
    control: CRubyRunner,
    fragment: FragmentChecker | None = None,
    checker: StaticChecker | None = None,
) -> CheckResult:
    result = static.check(case.source)
    obs = control.run(case.source)
    kind = runtime_kind(obs.exception)
    verdict = checker.check(case.source) if checker else None
    return CheckResult(
        case=case,
        static_ok=result.ok,
        static_errors=list(result.errors),
        runtime_kind=kind,
        exception=obs.exception,
        stdout=obs.stdout,
        cell=classify(result.ok, kind, obs.exception[0] if obs.exception else None),
        declared_static=case.provenance.get("static_expect", "?"),
        declared_runtime=case.provenance.get("runtime_expect", "?"),
        declared_check=case.provenance.get("check_expect"),
        fragment=fragment.check(case.source) if fragment else None,
        checker=verdict,
        check_cell=relate(
            verdict.verdict if verdict else None,
            result.errors,
            obs.exception[0] if obs.exception else None,
            TYPE_ERROR_FAMILY,
        ),
    )


def render_markdown(results: list[CheckResult]) -> str:
    by_cell: dict[str, list[CheckResult]] = {}
    for r in results:
        by_cell.setdefault(r.cell, []).append(r)
    mismatches = [r for r in results if not r.matches_declaration]

    lines = [
        "# Sorbet static oracle vs. actual behavior",
        "",
        f"{len(results)} programs. `srb tc` is an oracle, not truth: Sorbet is unsound",
        "by design, so the informative content is the off-diagonal cells below.",
        "",
        "| Cell | Count | Meaning |",
        "|---|---|---|",
    ]
    for cell, meaning in CELLS.items():
        lines.append(f"| `{cell}` | {len(by_cell.get(cell, []))} | {meaning} |")
    lines += [
        "",
        "> **Blind spot, stated rather than hidden.** This two-by-two can only see",
        "> *errors*. A hole that lets a wrong-typed value through with no error",
        "> anywhere — `.checked(:never)`, the unchecked `T::Struct` getter — is",
        "> indistinguishable here from a correct program and lands in",
        "> `accepted-and-safe`. Catching those needs behavior compared against a",
        "> *declared* type discipline rather than against the presence of an",
        "> exception: the annotation-conformance check of",
        "> `../ruby-lean/AGENTS.md` §Type safety as reachability §5, which is what the Lean typing layer",
        "> is for. Until it exists, this report undercounts the catalogue.",
        "",
    ]

    # ---- the checker relation (the static-soundness POC note §7) ----
    by_check: dict[str, list[CheckResult]] = {}
    for r in results:
        by_check.setdefault(r.check_cell, []).append(r)
    violations = [r for r in results if r.check_cell in PINNED_ZERO_CELLS]
    lines += [
        "## `check` vs. `srb` — the checker relation",
        "",
        "Soundness of `accept` is *proved*, not tested "
        "(`Proof/StaticSoundness.check_sound`); what this buys is **relevance** —",
        "evidence that `check` formalizes Sorbet rather than a type system we",
        "invented. Two directions, deliberately asymmetric:",
        "",
        "```",
        "accept  =>  srb reports no error in a type-relevant class",
        "reject  =>  srb reports some error, in any class",
        "```",
        "",
        "| Cell | Count | Meaning |",
        "|---|---|---|",
    ]
    for cell, meaning in CHECK_CELLS.items():
        pin = " **(pinned 0)**" if cell in PINNED_ZERO_CELLS else ""
        lines.append(f"| `{cell}` | {len(by_check.get(cell, []))} | {meaning}{pin} |")
    unknown_n = len(by_check.get("check-unknown", []))
    lines += [
        "",
        f"**Ratchet:** {unknown_n}/{len(results)} `unknown` "
        f"(the number to drive down); "
        f"{len(violations)} pinned-zero violations (must be 0).",
        "",
    ]
    if violations:
        lines += ["Violations — **this fails the run**:", ""]
        for r in violations:
            lines.append(f"- `{r.case.id}` — `{r.check_cell}`")
        lines.append("")
    coincidences = by_check.get("check-reject-agrees-verdict-only", [])
    if coincidences:
        lines += [
            "Agreement on the verdict but **not the reason** (§7.2) — not a "
            "failure, but not a win either:",
            "",
        ]
        for r in coincidences:
            codes = ", ".join(str(e.code) for e in excluded(r.static_errors))
            lines.append(f"- `{r.case.id}` — srb erred only on excluded code(s) {codes}")
        lines.append("")

    scope = [r for r in results if r.in_theorem_scope]
    in_frag = [r for r in results if r.fragment and r.fragment.in_fragment]
    unknown = [r for r in results if r.fragment is None]
    lines += [
        "## Theorem scope — what a soundness proof could be about",
        "",
        f"**{len(in_frag)}/{len(results)} in the Sorbet fragment** "
        f"(`ruby-lean/RubyCore/Types/Fragment.lean`); intersected with what `srb` accepts, "
        f"**{len(scope)} are in scope** for a soundness claim.",
        "",
        "In scope: " + (", ".join(f"`{r.case.id}`" for r in scope) or "_none_"),
        "",
    ]
    if unknown:
        lines += [
            "Fragment undecidable (did not desugar/decode — *not* the same as "
            "out-of-fragment): " + ", ".join(f"`{r.case.id}`" for r in unknown),
            "",
        ]
    out = [r for r in results if r.fragment and not r.fragment.in_fragment]
    if out:
        lines += ["Excluded, with the construct responsible:", ""]
        for r in out:
            whats = ", ".join(f"`{v['what']}`" for v in r.fragment.violations[:4])
            lines.append(f"- `{r.case.id}` — {whats}")
        lines.append("")

    if mismatches:
        lines += [
            "## Declaration mismatches (corpus integrity — this fails the run)",
            "",
        ]
        for r in mismatches:
            lines.append(
                f"- `{r.case.id}`: declared "
                f"({r.declared_static}, {r.declared_runtime}, "
                f"{r.declared_check or '-'}), observed "
                f"({'clean' if r.static_ok else 'errors'}, {r.runtime_kind}, "
                f"{(r.checker.verdict if r.checker else '-')})"
            )
        lines.append("")

    for cell, meaning in CELLS.items():
        rs = by_cell.get(cell, [])
        if not rs:
            continue
        lines += [f"## `{cell}` — {meaning}", ""]
        for r in rs:
            lines.append(f"### `{r.case.id}`")
            lines.append("")
            lines.append(f"{r.case.provenance.get('description', '')}")
            lines.append("")
            lines.append("```ruby")
            lines.append(r.case.source.rstrip())
            lines.append("```")
            lines.append("")
            if r.static_errors:
                for e in r.static_errors:
                    lines.append(f"- srb `{e.line}` (srb.help/{e.code}): {e.message}")
            else:
                lines.append("- srb: no errors")
            if r.exception:
                lines.append(f"- runtime: `{r.exception[0]}`: {r.exception[1].splitlines()[0]}")
            else:
                lines.append(f"- runtime: ran to completion, stdout `{r.stdout!r}`")
            lines.append(f"- doc: {r.case.provenance.get('doc_ref', '')}")
            lines.append("")
    return "\n".join(lines)


def run_check(cases: list[TestCase], out_dir: Path, timeout: float = 60.0) -> dict:
    static = SorbetStatic(timeout=timeout)
    control = CRubyRunner(timeout=timeout)
    fragment = FragmentChecker(runner=control)
    checker = StaticChecker(runner=control)
    results = [check_case(c, static, control, fragment, checker) for c in cases]

    out_dir.mkdir(parents=True, exist_ok=True)
    with (out_dir / "cases.jsonl").open("w") as fh:
        for r in results:
            fh.write(json.dumps(r.to_json()) + "\n")
    (out_dir / "report.md").write_text(render_markdown(results))

    counts = {cell: 0 for cell in CELLS}
    for r in results:
        counts[r.cell] += 1
    summary = {
        "total": len(results),
        "cells": counts,
        "mismatches": [r.case.id for r in results if not r.matches_declaration],
        "in_fragment": [r.case.id for r in results if r.fragment and r.fragment.in_fragment],
        "theorem_scope": [r.case.id for r in results if r.in_theorem_scope],
        "unsoundness_witnesses": [
            r.case.id for r in results if r.cell == "unsoundness-witness"
        ],
        "conservative_rejections": [
            r.case.id for r in results if r.cell == "conservative-rejection"
        ],
        "check_cells": {cell: 0 for cell in CHECK_CELLS}
        | {
            cell: sum(1 for r in results if r.check_cell == cell)
            for cell in CHECK_CELLS
        },
        "check_unknown": sum(1 for r in results if r.check_cell == "check-unknown"),
        "check_violations": [
            r.case.id for r in results if r.check_cell in PINNED_ZERO_CELLS
        ],
    }
    (out_dir / "summary.json").write_text(json.dumps(summary, indent=2))
    return summary
