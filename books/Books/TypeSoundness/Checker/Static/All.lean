import Books.TypeSoundness.Checker.Static.Kept

/-!
# `Checker/Static/All.lean` — the whole static vocabulary, in one import

`Checker/Static/` is a chain: each file imports its predecessor, in the reading order the
single `Judge.lean` had before it was split. This module is its tail, for the consumers that
want all of it -- `Checker/Judgment/`, the `Guards/`, and `books/Books/TypeSoundness/Conformance/`'s conformance
statements. Import a specific file instead when you only need one pocket.
-/
