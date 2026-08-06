"""CLI for the differential test engine.

    python -m difftest run --tier 1 -n 200 --sut identity --seed 42
    python -m difftest run --tier 1 -n 100 --sut desugar --inject-bug
    python -m difftest run --tier 0 --sut desugar          # bootstraptest corpus
    python -m difftest gen3 --category eval-order -n 5
    python -m difftest replay corpus/tier3 --sut identity
"""

from __future__ import annotations

import argparse
import datetime
import json
import os
import random
import sys
from pathlib import Path

from .control import CRubyRunner
from .report import Reporter
from .runner import run_campaign
from .sources import load_bootstraptest, load_corpus_cases, load_sorbet_corpus
from .tiers import GENERATIVE_ARMS
from .sut import make_sut

BASE = Path(__file__).resolve().parents[1]  # ruby/difftest/


def _load_dotenv(path: Path = BASE / ".env") -> None:
    """Load KEY=value lines from .env (holds ANTHROPIC_API_KEY for tier 3).
    Real environment variables take precedence; no new dependency needed."""
    if not path.exists():
        return
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, _, value = line.partition("=")
        key, value = key.strip(), value.strip().strip("'\"")
        if key.startswith("export "):
            key = key.removeprefix("export ").strip()
        os.environ.setdefault(key, value)


def _out_dir(arg: str | None, label: str) -> Path:
    if arg:
        return Path(arg)
    stamp = datetime.datetime.now().strftime("%Y%m%d-%H%M%S")
    return BASE / "reports" / f"{stamp}-{label}"


def _print_summary(summary: dict, out_dir: Path) -> None:
    print(json.dumps(summary, indent=2))
    print(f"\nreport: {out_dir / 'report.md'}")


CORPUS_ARMS = ("tier0", "tier3", "sorbet")  # mix arms backed by persisted corpora


def _load_corpus_arm(name: str, args) -> list:
    if name == "tier0":
        return load_bootstraptest(Path(args.corpus) if args.corpus else None)
    if name == "sorbet":
        return load_sorbet_corpus(Path(args.corpus) if args.corpus else None)
    return load_corpus_cases(BASE / "corpus" / "tier3", default_tier=3)


def cmd_run(args) -> int:
    from .campaign import parse_mix, run_generative_campaign

    control = CRubyRunner(timeout=args.timeout)
    sut = make_sut(args.sut, inject_bug=args.inject_bug)
    label = "mix" if args.mix else f"tier{args.tier}"
    out_dir = _out_dir(args.out, f"{label}-{sut.name}")
    reporter = Reporter(out_dir)

    if args.mix:
        mix = parse_mix(args.mix)
        known = set(GENERATIVE_ARMS) | set(CORPUS_ARMS)
        unknown = set(mix) - known
        if unknown:
            print(f"unknown mix arms: {sorted(unknown)}; known: {', '.join(sorted(known))}",
                  file=sys.stderr)
            return 2
        corpus_cases = {name: _load_corpus_arm(name, args)
                        for name in mix if name not in GENERATIVE_ARMS}
        extra = run_generative_campaign(
            control, sut, reporter,
            n=args.n if args.n is not None else 100,
            seed=args.seed,
            mix=mix,
            corpus_cases=corpus_cases,
            regressions_dir=BASE / "corpus" / "regressions",
        )
    elif args.tier == "0":
        cases = load_bootstraptest(Path(args.corpus) if args.corpus else None)
        total = len(cases)
        if args.n is not None and args.n < total:
            picked = random.Random(args.seed).sample(cases, args.n)
            cases = sorted(picked, key=lambda c: c.id)
        run_campaign(cases, control, sut, on_result=reporter.record)
        extra = {"tier0": {"available": total, "ran": len(cases), "seed": args.seed}}
    elif args.tier == "4":
        # The Sorbet corpus (tier 4). Runs whole; it is small and every program
        # is hand-authored to probe a specific feature, so sampling it would
        # lose the point rather than save time.
        cases = load_sorbet_corpus(Path(args.corpus) if args.corpus else None)
        run_campaign(cases, control, sut, on_result=reporter.record)
        extra = {"tier4": {"ran": len(cases), "corpus": "sorbet"}}
    elif args.tier in ("1", "1.5"):
        extra = run_generative_campaign(
            control, sut, reporter,
            n=args.n if args.n is not None else 100,
            seed=args.seed,
            mix={f"tier{args.tier}": 1.0},
            regressions_dir=BASE / "corpus" / "regressions",
        )
    else:
        print(f"tier {args.tier} is not implemented yet (tier 2 is a stub)", file=sys.stderr)
        return 2
    summary = reporter.finalize(sut.name, extra=extra)
    _print_summary(summary, out_dir)
    return 1 if summary["verdicts"].get("disagree") else 0


def cmd_gen3(args) -> int:
    from .tiers.tier3.generate import generate_category
    from .tiers.tier3.prompts import CATEGORIES

    categories = list(CATEGORIES) if args.category == ["all"] else args.category
    unknown = [c for c in categories if c not in CATEGORIES]
    if unknown:
        print(f"unknown categories: {unknown}; known: {list(CATEGORIES)}", file=sys.stderr)
        return 2
    control = CRubyRunner(timeout=args.timeout)
    corpus = Path(args.corpus) if args.corpus else BASE / "corpus" / "tier3"
    for cat in categories:
        print(f"generating {args.n} programs for category {cat!r} with {args.model}...")
        result = generate_category(cat, args.n, corpus, control, model=args.model)
        print(f"  accepted: {len(result.accepted)}")
        for p in result.accepted:
            print(f"    {p}")
        for reason, code in result.rejected:
            print(f"  REJECTED ({reason}):")
            print("    " + "\n    ".join(code.splitlines()[:5]))
    return 0


def cmd_sorbet(args) -> int:
    from .sorbet import SorbetUnavailable, require_toolchain
    from .sorbet_check import run_check

    try:
        require_toolchain()
    except SorbetUnavailable as e:
        print(e, file=sys.stderr)
        return 2
    cases = load_sorbet_corpus(Path(args.corpus) if args.corpus else None)
    out_dir = _out_dir(args.out, "sorbet-check")
    summary = run_check(cases, out_dir, timeout=args.timeout)
    _print_summary(summary, out_dir)
    # Exit 1 on a *declaration mismatch* only. Unsoundness witnesses are
    # findings, not failures — the corpus exists to collect them.
    return 1 if summary["mismatches"] else 0


def cmd_replay(args) -> int:
    control = CRubyRunner(timeout=args.timeout)
    sut = make_sut(args.sut, inject_bug=args.inject_bug)
    corpus = Path(args.corpus)
    cases = load_corpus_cases(corpus)
    if not cases:
        print(f"no .rb files under {corpus}", file=sys.stderr)
        return 2

    out_dir = _out_dir(args.out, f"replay-{sut.name}")
    reporter = Reporter(out_dir)
    run_campaign(cases, control, sut, on_result=reporter.record)
    summary = reporter.finalize(sut.name)
    _print_summary(summary, out_dir)
    return 1 if summary["verdicts"].get("disagree") else 0


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(prog="difftest")
    sub = parser.add_subparsers(dest="cmd", required=True)

    def common(p):
        p.add_argument("--sut", default="stub", choices=["stub", "identity", "desugar", "lean", "sig-strip"])
        p.add_argument("--inject-bug", action="store_true", help="desugar SUT: enable DESUGAR_BUG")
        p.add_argument("--timeout", type=float, default=10.0)
        p.add_argument("--out", help="report directory (default: reports/<timestamp>-<label>)")

    p_run = sub.add_parser("run", help="run a generation-tier or mixed campaign")
    # tier "1.5" is the tier-1 generator with eval-order probes on (no per-tier
    # flag; a distinct tier id keeps selection uniform).
    p_run.add_argument(
        "--tier", type=str, default="1", choices=["0", "1", "1.5", "2", "3", "4"]
    )
    p_run.add_argument(
        "--mix",
        help='weighted mixed campaign over generative (tier1, tier1.5) and corpus '
             '(tier0, tier3, sorbet) arms, e.g. "tier1.5=0.9,tier0=0.05,tier3=0.05" '
             '(overrides --tier)',
    )
    p_run.add_argument(
        "-n", type=int, help="number of cases (tier 1/mix default: 100; tier 0 default: all)"
    )
    p_run.add_argument("--seed", type=int, help="generator seed for reproducibility")
    p_run.add_argument(
        "--corpus", help="corpus dir override for tier 0 (bootstraptest) / tier 4 (sorbet)"
    )
    common(p_run)
    p_run.set_defaults(func=cmd_run)

    p_gen = sub.add_parser("gen3", help="generate tier-3 corpus via the Anthropic API")
    p_gen.add_argument("--category", nargs="+", default=["all"])
    p_gen.add_argument("-n", type=int, default=10, help="programs per category")
    p_gen.add_argument("--model", default="claude-opus-4-8")
    p_gen.add_argument("--corpus", help="corpus root (default: corpus/tier3)")
    p_gen.add_argument("--timeout", type=float, default=10.0)
    p_gen.set_defaults(func=cmd_gen3)

    p_sorbet = sub.add_parser(
        "sorbet", help="Sorbet static oracle vs. actual behavior over the tier-4 corpus"
    )
    p_sorbet.add_argument("subcommand", choices=["check"])
    p_sorbet.add_argument("--corpus", help="corpus dir (default: corpus/sorbet)")
    p_sorbet.add_argument("--timeout", type=float, default=60.0)
    p_sorbet.add_argument("--out", help="report directory")
    p_sorbet.set_defaults(func=cmd_sorbet)

    p_rep = sub.add_parser("replay", help="re-run a persisted corpus directory")
    p_rep.add_argument("corpus")
    common(p_rep)
    p_rep.set_defaults(func=cmd_replay)

    args = parser.parse_args(argv)
    _load_dotenv()
    return args.func(args)
