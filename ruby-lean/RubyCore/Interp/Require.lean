import RubyCore.Interp.Support

/-! L281: execute modeled feature bodies on require, at a fresh top level.
    Completed features are cached; a raise preserves effects but permits retry. -/
namespace RubyCore.Interp

def requireBid (bid : String) : Bool :=
  bid == "Object#require" || bid == "Object#require_relative"

def callRequire (m : Machine) (bid : String) (args : List Value)
    (kw : List (Value × Value)) : StepResult :=
  let argc := args.length + if kw.isEmpty then 0 else 1
  if argc != 1 then .next (raiseErr m Boot.argumentErrorId
      s!"wrong number of arguments (given {argc}, expected 1)") else
  if bid == "Object#require_relative" then .unsupported "require_relative needs source-file resolution" else
  match Builtins.strPayload? m.heap (args.headD .nil) with
  | none => .unsupported "require feature conversion through to_path/to_str"
  | some raw =>
    let feature := if raw.endsWith ".rb" then (raw.dropEnd 3).toString else raw
    if m.loadedFeatures.contains feature || m.loadingFeatures.contains feature then
      .next { m with ctl := .value (.bool false) }
    else match m.featurePrograms.find? (·.1 == feature) with
    | none => .unsupported s!"require of an unmodeled library: {raw}"
    | some (_, body) =>
      -- Native reopening diagnostics include the earlier source location.
      -- The AST does not yet retain it; do not invent a shorter error message.
      let rootName := if feature == "sorbet-runtime" then "T"
        else if feature == "json" then "JSON"
        else if feature == "uri" then "URI"
        else if feature == "forwardable" then "Forwardable" else ""
      let conflict := match constOwn m.heap Boot.objectId rootName with
        | none => false
        | some (.ref o) => match m.heap.classPayload? o with
          | some cp => !cp.isModule
          | none => true
        | some _ => true
      if conflict then .unsupported "require namespace conflict needs original source location" else
      let frame : Frame := { self := .ref Boot.mainId, defmod := Boot.objectId, kind := .toplevel, cref := [Boot.objectId], libraryOrigin := true }
      let fid := m.frames.size
      .next { m with ctl := .eval body, frames := m.frames.push frame, stack := fid :: m.stack, kont := .requireK feature fid :: m.kont, loadingFeatures := feature :: m.loadingFeatures, attemptedFeatures := feature :: m.attemptedFeatures.filter (· != feature) }

end RubyCore.Interp
