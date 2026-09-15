import Lean

/-!
# `RubyCore/Proof/FrameAttr.lean` — the framing simp set, registered

`register_simp_attr` has to live in a module *imported* by the one that uses the attribute, so
this one-line file exists: it lets `RubyCore/Proof/KontFrame.lean` tag its lemmas
`@[frameLem]` and write `simp only [frameLem]` without maintaining an explicit list. The list
is what made those proofs order-dependent — a lemma proved after the tactic macro was defined
was invisible to it — and order-dependence is what cost `callClosure` and three `Builtins`
dispatchers on the first pass.
-/

register_simp_attr frameLem
