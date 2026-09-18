import Ratchet.Static.Kept

/-!
# `Ratchet/Static/All.lean` — the whole static vocabulary, in one import

`Ratchet/Static/` is a chain: each file imports its predecessor, in the reading order the
single `Judge.lean` had before it was split. This module is its tail, for the consumers that
want all of it -- `Ratchet/Judgment/`, the `Guards/`, and `Denote/Sem/`'s conformance
statements. Import a specific file instead when you only need one pocket.
-/
