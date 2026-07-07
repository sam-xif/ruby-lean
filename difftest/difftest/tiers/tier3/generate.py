"""Tier-3 generator: ask Claude for adversarial programs, validate them against
the control, and persist the survivors as a replayable corpus.

Generated cases cost money, so everything that passes the validation gate is
written to corpus/tier3/<category>/NNN.rb with a .json metadata sidecar and can
be re-run forever via `difftest replay`. Rejections are logged with reasons.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

from ...control import CRubyRunner, HarnessError

DEFAULT_MODEL = "claude-opus-4-8"


@dataclass
class GenResult:
    accepted: list[Path]
    rejected: list[tuple[str, str]]  # (reason, code)
    model: str
    category: str


def generate_category(
    category: str,
    n: int,
    corpus_dir: Path,
    control: CRubyRunner,
    model: str = DEFAULT_MODEL,
) -> GenResult:
    import anthropic  # deferred so the rest of the engine works without an API key

    from .prompts import OUTPUT_SCHEMA, build_prompt

    client = anthropic.Anthropic()
    with client.messages.stream(
        model=model,
        max_tokens=32000,
        thinking={"type": "adaptive"},
        output_config={"format": {"type": "json_schema", "schema": OUTPUT_SCHEMA}},
        messages=[{"role": "user", "content": build_prompt(category, n)}],
    ) as stream:
        response = stream.get_final_message()

    if response.stop_reason == "refusal":
        raise RuntimeError(f"model refused the generation request (category={category})")
    if response.stop_reason == "max_tokens":
        raise RuntimeError("generation truncated at max_tokens; lower -n or raise max_tokens")

    text = "".join(b.text for b in response.content if b.type == "text")
    programs = json.loads(text)["programs"]

    cat_dir = corpus_dir / category
    cat_dir.mkdir(parents=True, exist_ok=True)
    existing = sorted(cat_dir.glob("[0-9][0-9][0-9].rb"))
    next_idx = int(existing[-1].stem) + 1 if existing else 0

    accepted: list[Path] = []
    rejected: list[tuple[str, str]] = []
    for prog in programs:
        code, description = prog["code"], prog["description"]
        reason = _validate(code, control)
        if reason is not None:
            rejected.append((reason, code))
            continue
        path = cat_dir / f"{next_idx:03d}.rb"
        path.write_text(code if code.endswith("\n") else code + "\n")
        path.with_suffix(".json").write_text(
            json.dumps(
                {
                    "tier": 3,
                    "category": category,
                    "description": description,
                    "model": model,
                    "response_id": response.id,
                },
                indent=2,
            )
        )
        accepted.append(path)
        next_idx += 1
    return GenResult(accepted=accepted, rejected=rejected, model=model, category=category)


def _validate(code: str, control: CRubyRunner) -> str | None:
    """Gate before a generated program enters the corpus. None = accepted."""
    syntax_err = control.check_parses(code)
    if syntax_err is not None:
        return f"parse error: {syntax_err}"
    try:
        obs, why = control.run_deterministic(code)
    except HarnessError as e:
        return f"harness error: {e}"
    if obs is None:
        return why
    return None
