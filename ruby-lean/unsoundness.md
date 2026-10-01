# Hash iterator transparency (2026-09-30)

The legacy static RetTransparent/NxtTransparent predicates admitted every
iterK. Their unwind lemmas claimed that return, next and raise only pop the
marker and change control. That claim is false after shared Hash insertion locks:
a hashEach marker with hashIterationLocks = [0] removes 0 on unwind.
RubyCore/Proof/Static/IteratorUnwind.lean's hash_unwind_not_transparent is a
kernel-checked counterexample using raise; the same cleanup precedes all jumps.

Restrict exact transparency to IterUnwindInert (all kinds except hashEach).
RetOk/RaiseOk/NxtOk skip premises inherit that correction. KontOk's admitted
iterator uses ignore and retains its proof. This is a stale auxiliary static
judgment, not evidence of a Sorbet bug or an active validateD unsound accept.
No runtime or top-level safety theorem changes.
