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


# `p0-fragment` programs carry no annotations at all — they exist to exercise the
# *static* checker — so there is no runtime enforcement for the control to
# exercise and the gem would only add load noise. The exemption also buys
# something: without the `require`, these are the only tier-4 programs the Lean
# SUT can run (it gates every other one on it — see `load_sorbet_corpus`).
NO_RUNTIME_CATEGORIES = {"p0-fragment"}


def test_every_program_requires_sorbet_runtime():
    # Self-contained by construction: the control must exercise the real
    # runtime enforcement without any wrapper cooperation.
    for case in load_sorbet_corpus():
        if case.provenance["category"] in NO_RUNTIME_CATEGORIES:
            continue
        assert 'require "sorbet-runtime"' in case.source, case.id


def test_annotation_free_categories_really_are_annotation_free():
    """The exemption above must not become a hiding place: a program that skips
    the `require` had better not be using `T.` either."""
    for case in load_sorbet_corpus():
        if case.provenance["category"] not in NO_RUNTIME_CATEGORIES:
            continue
        assert "T." not in case.source, case.id
        assert "sig " not in case.source and "sig{" not in case.source, case.id


def test_check_expect_is_wellformed_where_declared():
    """Optional (the 22 pre-existing programs predate the checker), but where
    present it must name a real verdict — `difftest sorbet check` then enforces
    it against the model."""
    for case in load_sorbet_corpus():
        declared = case.provenance.get("check_expect")
        if declared is not None:
            assert declared in ("accept", "reject", "unknown"), case.id


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
