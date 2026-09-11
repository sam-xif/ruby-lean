import Ratchet.Corpus
import Semantics.Interp

/-!
# `probes/kont_census.lean` — how many of the 49 `Kont` frames does `KontOk` actually need?

`Denote/Sem/Invariant.lean` §4 names this as the cheapest way to size the remaining work:
`KontOk` is one constructor per continuation frame, and the judged fragment of `Expr` is a
tier-≤16 subset, so most frames may be unreachable. This walks **every corpus program**
(the 254 committed rungs) under the real `stepFn` from the prelude-booted heap and collects
the head constructor of every continuation frame that is ever pushed.

It is a *reachability* measurement over the corpus, not a theorem: a frame absent here is
absent from the programs the ladder is built on, which is what bounds the work in practice.
A frame present here is definitely needed.

Run:  lake env lean probes/kont_census.lean
-/

open Lean (Json)

def kontTag : RubyCore.Kont → String
  | .seqK .. => "seqK"
  | .asgnK .. => "asgnK"
  | .casgnK .. => "casgnK"
  | .classDefK .. => "classDefK"
  | .newK .. => "newK"
  | .methodAddedK .. => "methodAddedK"
  | .raiseNewK .. => "raiseNewK"
  | .includeK .. => "includeK"
  | .defsK .. => "defsK"
  | .sclassK .. => "sclassK"
  | .cpathK .. => "cpathK"
  | .cpathAsgnK .. => "cpathAsgnK"
  | .cpathAsgnValK .. => "cpathAsgnValK"
  | .scopedClassDefK .. => "scopedClassDefK"
  | .ifK .. => "ifK"
  | .whileCondK .. => "whileCondK"
  | .whileBodyK .. => "whileBodyK"
  | .forStartK .. => "forStartK"
  | .forBodyK .. => "forBodyK"
  | .iterK .. => "iterK"
  | .recvK .. => "recvK"
  | .argsK .. => "argsK"
  | .argsSplatK .. => "argsSplatK"
  | .blkCoerceK .. => "blkCoerceK"
  | .kwPairK .. => "kwPairK"
  | .kwDynKeyK .. => "kwDynKeyK"
  | .kwDynValK .. => "kwDynValK"
  | .kwSplatK .. => "kwSplatK"
  | .yieldArgK .. => "yieldArgK"
  | .yieldSplatK .. => "yieldSplatK"
  | .superArgK .. => "superArgK"
  | .superSplatK .. => "superSplatK"
  | .arrK .. => "arrK"
  | .arrSplatK .. => "arrSplatK"
  | .hshKeyK .. => "hshKeyK"
  | .hshValK .. => "hshValK"
  | .jumpValK .. => "jumpValK"
  | .optDefK .. => "optDefK"
  | .frameK .. => "frameK"
  | .blkFrameK .. => "blkFrameK"
  | .catchK .. => "catchK"
  | .beginBodyK .. => "beginBodyK"
  | .rescMatchK .. => "rescMatchK"
  | .rescueK .. => "rescueK"
  | .elseK .. => "elseK"
  | .definedRecvK .. => "definedRecvK"
  | .definedCpathK .. => "definedCpathK"
  | .definedGuardK .. => "definedGuardK"
  | .ensureK .. => "ensureK"

def allKontTags : List String :=
  ["seqK", "asgnK", "casgnK", "classDefK", "newK", "methodAddedK", "raiseNewK", "includeK", "defsK", "sclassK", "cpathK", "cpathAsgnK", "cpathAsgnValK", "scopedClassDefK", "ifK", "whileCondK", "whileBodyK", "forStartK", "forBodyK", "iterK", "recvK", "argsK", "argsSplatK", "blkCoerceK", "kwPairK", "kwDynKeyK", "kwDynValK", "kwSplatK", "yieldArgK", "yieldSplatK", "superArgK", "superSplatK", "arrK", "arrSplatK", "hshKeyK", "hshValK", "jumpValK", "optDefK", "frameK", "blkFrameK", "catchK", "beginBodyK", "rescMatchK", "rescueK", "elseK", "definedRecvK", "definedCpathK", "definedGuardK", "ensureK"]

/-- Step `m` up to `fuel` times, accumulating the tag of every frame ever seen on `kont`. -/
partial def census (fuel : Nat) (m : RubyCore.Machine) (acc : List String) : List String :=
  let acc := m.kont.foldl (fun a k => let t := kontTag k; if a.contains t then a else t :: a) acc
  match fuel with
  | 0 => acc
  | f + 1 =>
    match RubyCore.Interp.stepFn m with
    | .next m' => census f m' acc
    | _ => acc



def main : IO Unit := do
  let dir : System.FilePath := "corpus"
  let entries ← dir.readDir
  let files := (entries.map (·.path)).toList.filter (fun p => p.toString.endsWith ".json")
  let mut seen : List String := []
  let mut seenJudged : List String := []
  let mut n := 0
  let mut nj := 0
  let mut gated := 0
  for f in files.toArray.qsort (fun a b => a.toString < b.toString) |>.toList do
    let txt ← IO.FS.readFile f
    match Json.parse txt with
    | .error _ => pure ()
    | .ok j =>
      match j.getObjVal? "program" with
      | .error _ => pure ()
      | .ok pj =>
        match RubyCore.Decode.program pj with
        | .error _ => gated := gated + 1
        | .ok p =>
          match Ratchet.Semantics.bootedMachine with
          | .error _ => pure ()
          | .ok mp =>
            n := n + 1
            let m0 := { RubyCore.Machine.initOn mp.heap p with globals := mp.globals }
            let tags := census 60000 m0 []
            seen := tags.foldl (fun a t => if a.contains t then a else t :: a) seen
            -- the fragment the judgment is meant to cover: the rungs targeting `true`
            let judged := (j.getObjVal? "expect_validate").toOption.bind (·.getBool?.toOption)
            if judged == some true then
              nj := nj + 1
              seenJudged := tags.foldl (fun a t => if a.contains t then a else t :: a) seenJudged
  let missing := allKontTags.filter (fun t => ! seen.contains t)
  let missingJ := allKontTags.filter (fun t => ! seenJudged.contains t)
  IO.println s!"corpus programs walked: {n} (undecodable: {gated}); targeting validate=true: {nj}"
  IO.println s!"Kont constructors: {allKontTags.length}"
  IO.println s!"  pushed by SOME corpus program: {seen.length}"
  IO.println s!"    {(seen.toArray.qsort (· < ·)).toList}"
  IO.println s!"  pushed by a program the judgment is meant to accept: {seenJudged.length}"
  IO.println s!"    {(seenJudged.toArray.qsort (· < ·)).toList}"
  IO.println s!"  never reached at all ({missing.length}): {missing}"
  IO.println s!"  never reached from the judged fragment ({missingJ.length}): {missingJ}"

#eval main
