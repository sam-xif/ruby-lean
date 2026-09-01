import Ratchet.Corpus
import Ratchet.Rungs

/-!
The ratchet runner: load every `corpus/*.json` entry (real desugared Ruby) and check
`validate`'s actual verdict against the recorded expectation. See `AGENTS.md` for how to
read the report and `scripts/run_ratchet.sh` for the one-line invocation.

**One number, not two.** This report used to split each tier into "structural" and
"claim-assisted", because `chk` had a certificate-claim fallback and a claim was
trusted. Claims are gone (`AGENTS.md` §Claim-free), so every `true` below is
synthesized by `chk` itself and the two columns collapsed into the honest one.
-/

open Ratchet
open Lean (Json)

structure EntryReport where
  id : String
  tier : Nat
  validateActual : Bool
  validateOk : Bool
  falseReason : Option String

def runEntry (e : CorpusEntry) : EntryReport :=
  let validateActual := validate e.program
  { id := e.id, tier := e.tier
    validateActual := validateActual
    validateOk := validateActual == e.expectValidate
    falseReason := e.falseReason }

def loadEntry (p : System.FilePath) : IO CorpusEntry := do
  let contents ← IO.FS.readFile p
  match Json.parse contents with
  | .error e => throw (IO.userError s!"{p}: JSON parse error: {e}")
  | .ok j =>
    match CorpusEntry.ofJson? j with
    | .error e => throw (IO.userError s!"{p}: {e}")
    | .ok entry => pure entry

-- A display-only rendering of `Ty`, for `--stdin`'s output — not part of the trusted
-- checker (`Ratchet/Ty.lean`/`Validate.lean` are untouched), just a printer over it, in
-- Sorbet's own vocabulary where one exists (`T.untyped`, `T.nilable`, `T::Array[...]`,
-- `T.noreturn` for `.never`) since that is the vocabulary `--check`'s `type` field
-- already prints in. `.inst`/`.clos`'s ivar/capture spines print as `{@x: Integer, ...}`;
-- an empty spine (`.ivar0`) prints as the empty string, so a bare `.inst "Point" .ivar0`
-- renders `Point{}` rather than `Point{}}`.
namespace Ratchet
partial def Ty.render : Ty → String
  | .int => "Integer"
  | .bool => "Boolean"
  | .nilT => "NilClass"
  | .sym => "Symbol"
  | .cls c => c
  | .any => "T.untyped"
  | .clsOf n => s!"T.class_of({n})"
  | .nilable τ => s!"T.nilable({Ty.render τ})"
  | .float => "Float"
  | .arrayOf τ => s!"T::Array[{Ty.render τ}]"
  | .hashOf k v => s!"T::Hash[{Ty.render k}, {Ty.render v}]"
  | .never => "T.noreturn"
  | .union σ τ => s!"T.any({Ty.render σ}, {Ty.render τ})"
  | .arrow0 τ => s!"() -> {Ty.render τ}"
  | .arrowCons p rest => s!"({Ty.render p}) -> {Ty.render rest}"
  | .inst name ivars => name ++ "{" ++ Ty.render ivars ++ "}"
  | .ivar0 => ""
  | .ivarCons n τ .ivar0 => s!"{n}: {Ty.render τ}"
  | .ivarCons n τ rest => s!"{n}: {Ty.render τ}, {Ty.render rest}"
  -- Tier 12: an alias binding. Rendered with the name it aliases, because that is the whole
  -- content of it (see `Ty.sameAs`); nothing but `narrowEnvs` reads it.
  | .sameAs n τ => s!"{Ty.render τ} (= {n})"
  | .clos idx .ivar0 .never => s!"<closure#{idx}>"
  | .clos idx captured .never => s!"<closure#{idx}>" ++ "{" ++ Ty.render captured ++ "}"
  -- Tier 11: a closure created where `self` was typed also renders its creation `self`,
  -- because that is what its body will be checked against (see `Ty.clos`).
  | .clos idx .ivar0 cself => s!"<closure#{idx} self={Ty.render cself}>"
  | .clos idx captured cself =>
    s!"<closure#{idx} self={Ty.render cself}>" ++ "{" ++ Ty.render captured ++ "}"
end Ratchet

-- `--stdin`: check one program instead of the corpus — RubyCore JSON (the same
-- `{"v":.., "ast":..}` shape `export-json`/the corpus's `program` field carry) on
-- stdin. For an interactive caller (the playground); the corpus run above is what
-- climbs the ladder.
--
-- Reports `chk`'s **whole** result triple, not just `validate`'s `Bool`: the
-- program's result type, the final local environment (the types of its locals —
-- "the different terms" a reader of the program would want typed), and the final
-- self-ivar spine. `validate` itself is `(chk ...).isSome` (`Validate.lean` L474-475),
-- so this is the same call, read further rather than a second checker.
def runStdin : IO UInt32 := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  match Json.parse input with
  | .error e =>
    IO.eprintln s!"bad input JSON: {e}"
    return 1
  | .ok j =>
    match Decode.program j with
    | .error e =>
      IO.eprintln s!"undecodable RubyCore: {e}"
      return 1
    | .ok prog =>
      match chk fuelDefault (ctx0.withBlocks prog) [] .ivar0 prog with
      | none =>
        IO.println (Json.mkObj [("validate", Json.bool false)]).compress
        return 0
      | some (τ, Γ, I) =>
        let localsJson := Json.arr (Γ.map (fun (n, t) =>
          Json.mkObj [("name", Json.str n), ("type", Json.str t.render)])).toArray
        IO.println (Json.mkObj [
          ("validate", Json.bool true),
          ("type", Json.str τ.render),
          ("locals", localsJson),
          ("ivars", Json.str ("{" ++ I.render ++ "}"))]).compress
        return 0

def main (args : List String) : IO UInt32 := do
  if args.contains "--stdin" then
    return ← runStdin
  let corpusDir : System.FilePath := args.headD "corpus"
  let dirEntries ← corpusDir.readDir
  let files := (dirEntries.map (·.path)).toList.filter (fun p => p.toString.endsWith ".json")
  let sorted := files.toArray.qsort (fun a b => a.toString < b.toString) |>.toList
  let entries ← sorted.mapM loadEntry
  if entries.isEmpty then
    IO.eprintln s!"no corpus entries found under {corpusDir}"
    return 1
  let reports := entries.map runEntry

  for r in reports do
    let mark := if r.validateOk then "ok" else "MISMATCH"
    let tag := match r.falseReason with
      | some reason => s!" [{reason}]"
      | none => ""
    IO.println s!"tier {r.tier} {r.id}{tag}: validate={r.validateActual} ({mark})"

  IO.println "\n--- tier summary (certified well-typed / total) ---"
  let tiers := (reports.map (·.tier)).eraseDups |>.toArray |>.qsort (· < ·) |>.toList
  for t in tiers do
    let tReports := reports.filter (·.tier == t)
    let certified := tReports.filter (·.validateActual)
    IO.println s!"tier {t}: {certified.length}/{tReports.length} certified well-typed"

  -- Always shown, independent of pass/fail: the standing list of rungs whose target is
  -- permanently `false` because the *type language* (not just `chk`'s implementation)
  -- has no value describing the type at all. This is the thing worth watching for
  -- growth — each entry names a concrete `Ty` extension, not a rule to implement.
  let gaps := reports.filter (fun r => r.falseReason == some "ty_language_gap")
  IO.println s!"\n--- flagged: Ty language gaps ({gaps.length}) ---"
  for g in gaps do
    IO.println s!"  {g.id} (tier {g.tier})"

  IO.println s!"\nhand-authored derivations on file (Ratchet/Rungs.lean): {rungs.length} \
-- each one a `Judge` proof term, cross-checked against the real semantics by `lake exe checkrungs`"

  let mismatches := reports.filter (fun r => !r.validateOk)
  IO.println s!"\nrungs where validate's current answer differs from the recorded target (expect_validate): {mismatches.length}"
  if mismatches.isEmpty then
    IO.println "(every rung's target is met, and nothing is trusted anywhere. The tier \
fractions above are below 1 only for the recorded permanent negatives and Ty language gaps \
-- see AGENTS.md.)"
  else
    IO.println "(nothing is trusted; a mismatch is either a rung not yet climbed or, if it \
targets `false`, a soundness bug -- see AGENTS.md)"
  for m in mismatches do
    IO.eprintln s!"  not yet climbed: {m.id} (tier {m.tier})"

  if mismatches.isEmpty then
    IO.println "RATCHET OK"
    return 0
  else
    IO.println "RATCHET: climb remaining"
    return 1
