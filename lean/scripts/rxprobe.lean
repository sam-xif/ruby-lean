import RubyCore.Regex.Parse
import RubyCore.Regex.Match

/-!
Regex-engine probe: read `pattern \t opts \t input` lines on stdin, print one
result line each, in exactly the format `scripts/rxprobe.rb` prints for CRuby.
Diffing the two is the engine's oracle (W2a); it needs none of the rest of the
pipeline, so a mismatch is unambiguously a regex bug.

    lake env lean --run scripts/rxprobe.lean < cases.tsv

Result format, tab-separated so an empty capture is visible:
    nil                          — no match
    OOF                          — fuel exhausted (a gate, never a wrong answer)
    ERR <reason>                 — refused at parse time
    <start> <stop> <cap1> …      — match, with each capture as `a,b` or `-`
-/

open RubyCore.Rx

def showCaps (caps : Caps) : String :=
  String.intercalate "\t" (caps.toList.drop 1 |>.map fun
    | some (a, b) => s!"{a},{b}"
    | none => "-")

/-- Decode the probe protocol's newline/tab tokens (see `scripts/rxcases.rb`). -/
def dec (s : String) : String :=
  (s.replace "<NL>" "\n").replace "<TAB>" "\t"

def runOne (line : String) : String :=
  match line.splitOn "\t" with
  | [pat0, opts, inp0] =>
    let pat := dec pat0
    let inp := dec inp0
    match parse pat (opts.toNat!) with
    | .error e => s!"ERR {e}"
    | .ok r =>
      match search r inp.toList.toArray 0 with
      | .no => "nil"
      | .oof => "OOF"
      | .yes a b caps =>
        let cs := showCaps caps
        if cs.isEmpty then s!"{a}\t{b}" else s!"{a}\t{b}\t{cs}"
  | _ => "ERR malformed probe line"

def main : IO Unit := do
  let stdin ← IO.getStdin
  let mut out := ""
  let mut done := false
  while !done do
    let line ← stdin.getLine
    if line.isEmpty then
      done := true
    else
      out := out ++ runOne ((line.dropEndWhile (· == '\n')).toString) ++ "\n"
  IO.print out
