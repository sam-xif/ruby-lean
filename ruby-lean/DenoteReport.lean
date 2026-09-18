import Denote.Ty.Examples

/-!
`Denote/Ty/Examples.lean`'s human-readable half. The `#guard`s in that file are the gate — they
fail the *build*; this exe prints the same checks as a table so a reader of the log can see
what the denotation and the semantics agreed about, rather than only that they agreed.
-/

def main : IO Unit := IO.println Ratchet.Denote.Examples.report
