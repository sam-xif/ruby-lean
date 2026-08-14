"""Reporting: per-case JSONL, machine-readable summary, human Markdown."""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path

from .compare import CaseResult, Verdict


class Reporter:
    def __init__(self, out_dir: Path):
        self.out_dir = Path(out_dir)
        self.out_dir.mkdir(parents=True, exist_ok=True)
        self.cases_path = self.out_dir / "cases.jsonl"
        self._fh = self.cases_path.open("w")
        self.results: list[CaseResult] = []

    def record(self, result: CaseResult) -> None:
        self.results.append(result)
        self._fh.write(json.dumps(result.to_json()) + "\n")
        self._fh.flush()

    def finalize(self, sut_name: str, extra: dict | None = None) -> dict:
        self._fh.close()
        counts = Counter(r.verdict.value for r in self.results)
        by_tier: dict[str, Counter] = {}
        for r in self.results:
            by_tier.setdefault(str(r.case.tier), Counter())[r.verdict.value] += 1
        disagreements = [r for r in self.results if r.verdict == Verdict.DISAGREE]
        summary = {
            "sut": sut_name,
            "total": len(self.results),
            "verdicts": dict(counts),
            "by_tier": {k: dict(v) for k, v in by_tier.items()},
            "disagreements": [r.case.id for r in disagreements],
            **(extra or {}),
        }
        (self.out_dir / "summary.json").write_text(json.dumps(summary, indent=2))
        (self.out_dir / "report.md").write_text(self._markdown(summary, disagreements))
        return summary

    def _markdown(self, summary: dict, disagreements: list[CaseResult]) -> str:
        lines = [
            "# Differential test report",
            "",
            f"SUT: **{summary['sut']}** — {summary['total']} cases",
            "",
            "| Verdict | Count |",
            "|---|---|",
        ]
        for v in Verdict:
            lines.append(f"| {v.value} | {summary['verdicts'].get(v.value, 0)} |")
        lines.append("")
        reg = summary.get("regressions")
        if reg:
            # The verdict table above is honest but misleading on its own here: a
            # `still_open` case *is* a disagreement, and is meant to be. This
            # section is what the exit code is computed from (N41).
            lines += [
                "## Regressions corpus — declared status vs observed verdict",
                "",
                f"{reg['ran']} pinned cases. Only `regressed` and `unexpectedly_fixed` fail.",
                "",
                "| outcome | count | means |",
                "|---|---|---|",
            ]
            for name, blurb in reg["legend"].items():
                n = reg["counts"].get(name, 0)
                mark = " **← fails**" if name in ("regressed", "unexpectedly_fixed") and n else ""
                lines.append(f"| `{name}` | {n} | {blurb}{mark} |")
            lines.append("")
            for cid, o in sorted(reg["outcomes"].items()):
                lines.append(
                    f"- `{cid}` — declared **{o['status']}**, observed "
                    f"`{o['verdict']}` → **{o['outcome']}**"
                )
            lines.append("")
        skipped = [
            r
            for r in self.results
            if r.verdict in (Verdict.CONTROL_INVALID, Verdict.HARNESS_ERROR)
        ]
        if skipped:
            lines.append("## Excluded cases (with reasons — nothing is skipped silently)")
            lines.append("")
            for r in skipped:
                lines.append(f"- `{r.case.id}` ({r.verdict.value}): {r.reason}")
            lines.append("")
        if disagreements:
            lines.append("## Disagreements")
            for r in disagreements:
                lines += [
                    "",
                    f"### `{r.case.id}`" + (" (minimized)" if r.minimized else ""),
                    "",
                    "```ruby",
                    r.case.source.rstrip(),
                    "```",
                    "",
                    f"- **diff:** {r.reason}",
                ]
                if r.control_obs:
                    lines.append(f"- control: `{r.control_obs.to_json()}`")
                if r.sut_obs:
                    lines.append(f"- sut: `{r.sut_obs.to_json()}`")
        else:
            lines.append("No disagreements.")
        lines.append("")
        return "\n".join(lines)
