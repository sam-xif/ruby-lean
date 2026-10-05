"""Integrity of the Sorbet corpus: every program declares what it probes.

These are structural checks only (cheap, no toolchain). Whether each program
*actually behaves* as its sidecar declares is the job of
`difftest sorbet check`, which runs srb and CRuby over the corpus.
"""

import json

from difftest.sources import (
    RUNTIME_EXPECT,
    SORBET_CATEGORIES,
    STATIC_EXPECT,
    load_sorbet_corpus,
)


def test_corpus_loads():
    cases = load_sorbet_corpus()
    assert cases, "the Sorbet corpus is empty"
    assert all(c.tier == 4 for c in cases)


def test_every_program_has_a_wellformed_sidecar():
    for case in load_sorbet_corpus():
        meta = case.provenance
        assert meta.get("category") in SORBET_CATEGORIES, case.id
        assert meta.get("static_expect") in STATIC_EXPECT, case.id
        assert meta.get("runtime_expect") in RUNTIME_EXPECT, case.id
        assert meta.get("description"), case.id
        assert meta.get("doc_ref"), case.id


def test_category_dir_matches_declared_category():
    for case in load_sorbet_corpus():
        assert case.id.split("/")[0] == case.provenance["category"], case.id


def test_every_program_requires_sorbet_runtime():
    # Self-contained by construction: the control must exercise the real
    # runtime enforcement without any wrapper cooperation.
    for case in load_sorbet_corpus():
        assert 'require "sorbet-runtime"' in case.source, case.id


def test_every_program_declares_a_sigil():
    for case in load_sorbet_corpus():
        first = case.source.splitlines()[0]
        assert first.startswith("# typed: "), case.id
        assert first.removeprefix("# typed: ") == case.provenance["sigil"], case.id


def test_every_category_is_populated():
    seen = {c.provenance["category"] for c in load_sorbet_corpus()}
    assert seen == set(SORBET_CATEGORIES), sorted(set(SORBET_CATEGORIES) - seen)


def test_sidecars_are_json_objects_on_disk():
    for case in load_sorbet_corpus():
        path = case.provenance["path"].removesuffix(".rb") + ".json"
        assert isinstance(json.loads(open(path).read()), dict)
