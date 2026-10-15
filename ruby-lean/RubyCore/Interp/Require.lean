import RubyCore.Interp.Dispatch

/-! Execute modeled feature bodies on require, at a fresh top level.
    Completed features are cached; a raise preserves effects but permits retry.

    `require` (this file's lower half) runs the small set of modeled standard
    libraries, keyed by feature name. `require_relative` (upper half, issue #7 /
    M1) resolves its argument against the running file's directory in the
    symbolic filesystem and runs the pre-desugared body of the file it names. -/
namespace RubyCore.Interp

def requireBid (bid : String) : Bool :=
  bid == "Object#require" || bid == "Object#require_relative"

/-- The directory of an absolute path: `/lib/greeting.rb` → `/lib`, `/x` → `/`. -/
def parentDir (p : String) : String :=
  match ((p.splitOn "/").filter (· != "")).dropLast with
  | [] => "/"
  | ds => "/" ++ "/".intercalate ds

/-- Run a resolved library body at a fresh top level, caching it under its
    canonical path. Shared by both loaders once a file's `(id, path, body)` is in
    hand. A root `const_added` hook is gated (as `require` does), because it would
    observe the constants the body defines and the model does not run it. -/
def runLibraryBody (m : Machine) (canonical : String) (body : Expr) : StepResult :=
  if m.loadedFeatures.contains canonical || m.loadingFeatures.contains canonical then
    .next { m with ctl := .value (.bool false) }
  else if (lookup m.heap (.ref Boot.objectId) "const_added").any
      (fun (_, md) => md.builtin.isNone && !md.undefined && !md.fromPrelude) then
    .unsupported "require with a root const_added hook"
  else
    let frame : Frame :=
      { self := .ref Boot.mainId, defmod := Boot.objectId, kind := .toplevel,
        defVis := .priv, libraryOrigin := true, sourcePath := some canonical }
    let fid := m.frames.size
    .next { m with ctl := .eval body, frames := m.frames.push frame, stack := fid :: m.stack, kont := .requireK canonical fid :: m.kont, loadingFeatures := canonical :: m.loadingFeatures, attemptedFeatures := canonical :: m.attemptedFeatures.filter (· != canonical) }

/-- `require_relative raw` from a file whose path is `source`. Join the argument
    onto the source's directory, resolve it through the VFS, and run the body the
    fixture carries for that file. The cache is keyed by object identity, so any
    spelling of the same file loads once (CRuby keys realpaths). -/
def callRequireRelative (m : Machine) (source : String) (raw : String) : StepResult :=
  let joined := if raw.startsWith "/" then raw else parentDir source ++ "/" ++ raw
  let target := if joined.endsWith ".rb" then joined else joined ++ ".rb"
  match VFS.resolve m.heap target with
  | none =>
    -- CRuby raises LoadError; the error classes/messages are issue #7 step 7.
    .unsupported s!"require_relative cannot resolve {raw} (LoadError is unmodeled)"
  | some id =>
    match m.requireBodies.find? (·.1 == id) with
    | none => .unsupported s!"require_relative of a file with no modeled body: {raw}"
    | some (_, canonical, body) => runLibraryBody m canonical body

def callRequire (m : Machine) (bid : String) (args : List Value)
    (kw : List (Value × Value)) : StepResult :=
  let argc := args.length + if kw.isEmpty then 0 else 1
  if argc != 1 then .next (raiseErr m Boot.argumentErrorId
      s!"wrong number of arguments (given {argc}, expected 1)") else
  match Builtins.strPayload? m.heap (args.headD .nil) with
  | none =>
    if bid == "Object#require_relative" then
      .unsupported "require_relative feature conversion through to_path/to_str"
    else .unsupported "require feature conversion through to_path/to_str"
  | some raw =>
    if bid == "Object#require_relative" then
      match m.currentFrame.sourcePath with
      | none =>
        -- CRuby: LoadError "cannot infer basepath" (e.g. from `-e`/eval).
        .unsupported "require_relative with no source file (cannot infer basepath)"
      | some source => callRequireRelative m source raw
    else
    let feature := if raw.endsWith ".rb" then (raw.dropEnd 3).toString else raw
    if m.loadedFeatures.contains feature || m.loadingFeatures.contains feature then
      .next { m with ctl := .value (.bool false) }
    else match m.featurePrograms.find? (·.1 == feature) with
    | none => .unsupported s!"require of an unmodeled library: {raw}"
    | some (_, body) =>
      if feature == "forwardable" && (methodOn m.heap Boot.stringId "freeze").any
          (fun (_, md) => md.builtin.isNone) then
        .unsupported "Forwardable loading with an overridden String#freeze needs frozen literal compilation" else
      if (lookup m.heap (.ref Boot.objectId) "const_added").any
          (fun (_, md) => md.builtin.isNone && !md.undefined && !md.fromPrelude) then
        .unsupported "require with a root const_added hook" else
      -- Native reopening diagnostics include the earlier source location.
      -- The AST does not yet retain it; do not invent a shorter error message.
      let rootName := if feature == "sorbet-runtime" then "T"
        else if feature == "json" then "JSON"
        else if feature == "uri" then "URI"
        else if feature == "forwardable" then "Forwardable" else ""
      let roots := if feature == "forwardable" then [rootName, "SingleForwardable"] else [rootName]
      let conflict := roots.any fun root => match constOwn m.heap Boot.objectId root with
        | none => false
        | some (.ref o) => match m.heap.classPayload? o with
          | some cp => !cp.isModule
          | none => true
        | some _ => true
      if conflict then .unsupported "require namespace conflict needs original source location" else
      let frame : Frame := { self := .ref Boot.mainId, defmod := Boot.objectId, kind := .toplevel, defVis := .priv, libraryOrigin := true }
      let fid := m.frames.size
      .next { m with ctl := .eval body, frames := m.frames.push frame, stack := fid :: m.stack, kont := .requireK feature fid :: m.kont, loadingFeatures := feature :: m.loadingFeatures, attemptedFeatures := feature :: m.attemptedFeatures.filter (· != feature) }

end RubyCore.Interp
