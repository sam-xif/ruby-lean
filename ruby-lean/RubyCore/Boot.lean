/-
Booting the core library.

Much of Ruby's core library is written in Ruby here too: `prelude/prelude.rb`
defines `Enumerable`, `Comparable` and many other methods. Boot has two
phases. The first runs the prelude (the term `Prelude.program`) on the initial
heap with `preludeMode := true`, so that the methods it defines are marked as
the model's own. The second runs the user's program on the heap that leaves.

A prelude that raises, is declined or runs out of fuel is a bug in the model,
not an outcome of the user's program: it is reported as an error and `rubycore`
exits with status 1.
-/
import RubyCore.Generated.Prelude
import RubyCore.Generated.VfsFixture
import RubyCore.Interp

namespace RubyCore
namespace Prelude

/-! ## Mounting the require/require_relative library fixture (issue #7 / M1)

The library files (`VfsFixtureJson.rawFiles`) are mounted into the symbolic
filesystem as ordinary heap writes on the booted heap — new `.file`/`.dir`
objects and entries appended to existing directories. This is not part of
`Boot.initHeap` (the heap the metatheory reasons about); it is boot-time initial
data layered on top, exactly as issue #7 frames the fixture tree as a boot
parameter rather than ambient state. -/

/-- The id of `name` directly under directory `parent`, if present. -/
private def childId (h : Heap) (parent : ObjId) (name : String) : Option ObjId :=
  match (h.get parent).payload with
  | .dir entries _ => (entries.find? (·.1 == name)).map (·.2)
  | _ => none

/-- Append `(name, child)` to `parent`'s directory listing (no-op off a dir). -/
private def addEntry (h : Heap) (parent : ObjId) (name : String) (child : ObjId) : Heap :=
  match (h.get parent).payload with
  | .dir entries par => h.set parent { h.get parent with payload := .dir (entries ++ [(name, child)]) par }
  | _ => h

/-- Find or create a subdirectory `name` under `parent`, returning its id. -/
private def ensureDir (h : Heap) (parent : ObjId) (name : String) : Heap × ObjId :=
  match childId h parent name with
  | some id => (h, id)
  | none =>
    let (id, h) := h.alloc { klass := Boot.dirId, payload := .dir [] (some parent) }
    (addEntry h parent name id, id)

/-- Mount one file given its path components (dirs then filename): create any
    missing ancestor directories under the fixture root, then allocate the
    regular file and link it in. Returns the heap and the file's `(path, id)`.
    Components are supplied pre-split (the generator does it) because
    `String.splitOn` does not reduce in the kernel and the booted heap must. -/
private def mountOne (h : Heap) (path : String) (comps : List String) (bytes : String) :
    Heap × (String × ObjId) :=
  match comps.reverse with
  | [] => (h, (path, Boot.vfsRootId))
  | fileName :: revDirs =>
    let (h, parent) := revDirs.reverse.foldl
      (fun (acc : Heap × ObjId) name => ensureDir acc.1 acc.2 name) (h, Boot.vfsRootId)
    let (fid, h) := h.alloc { klass := Boot.fileId, payload := .file bytes }
    (addEntry h parent fileName fid, (path, fid))

/-- Mount every fixture file, returning the heap and each file's `(path, id)` in
    the input order (so boot can pair them with `bodies` by position). -/
def mountFiles (h : Heap) (files : List (String × List String × String)) :
    Heap × List (String × ObjId) :=
  files.foldl (fun (acc : Heap × List (String × ObjId)) f =>
    let (h, pr) := mountOne acc.1 f.1 f.2.1 f.2.2
    (h, acc.2 ++ [pr])) (h, [])

/-- Fuel for phase 1. The prelude only installs methods (no loops at load time),
    so this is generous by orders of magnitude; it exists so a mistake in the
    prelude fails fast instead of hanging. -/
def bootFuel : Nat := 200_000

/-- Run phase 1 and return the booted machine (heap + globals). -/
def boot : Except String Machine :=
  match program with
  | .error e => .error s!"prelude decode: {e}"
  | .ok p =>
    -- main's native singleton macros have their own place in lookup; they are
    -- not instance methods on every Object.
    let (e, initial) := Interp.eigenclassOf { Machine.init p with preludeMode := true } Boot.mainId
    let h := crubyMainSingletonNames.foldl (fun h name =>
      let repr := name == "inspect" || name == "to_s"
      defineMethod h e name
        { params := [], body := .nil, owner := e,
          visibility := if repr then .pub else .priv,
          builtin := some ((if repr then "Object#" else "Main#") ++ name) }) initial.heap
    let initial := { initial with heap := h }
    let (exceptionEigen, initial) := Interp.eigenclassOf initial Boot.exceptionId
    let h := defineMethod initial.heap exceptionEigen "exception"
      { params := [], body := .nil, owner := exceptionEigen, builtin := some "Exception.exception" }
    let initial := { initial with heap := h }
    -- Boot classes also inherit Exception's singleton constructor before any
    -- Ruby class body has had a chance to realize their eigenclass chains.
    let initial := Boot.classTable.foldl (fun m entry =>
      if (ancestors m.heap entry.1).contains Boot.exceptionId then
        (Interp.eigenclassOf m entry.1).2 else m) initial
    -- Filesystem singleton methods (issue #7 step 1): the `File.`/`Dir.`/`IO.`
    -- class methods that actually exist in CRuby and are modeled, installed on
    -- the constants' eigenclasses here exactly like `Exception.exception`, and
    -- reached by ordinary dispatch — no interpreter special case, and the
    -- prelude's own `File.basename`/`method_missing` continue to resolve as
    -- before. Only real CRuby class methods are installed, so an unknown call
    -- still reaches the prelude's `method_missing` and gates rather than
    -- answering.
    let fsSingleton : List (ObjId × List String) :=
      [ (Boot.fileId, ["read", "write", "exist?", "file?", "directory?", "size"]),
        (Boot.dirId, ["exist?"]),
        (Boot.ioId, ["read", "write"]) ]
    let initial := fsSingleton.foldl (fun m (cls, names) =>
      let (eigen, m) := Interp.eigenclassOf m cls
      let cname := match m.heap.classPayload? cls with | some c => c.name | none => ""
      names.foldl (fun m name =>
        let bid := cname ++ "#" ++ name
        let md : MethodDef := { params := [], body := .nil, owner := eigen, builtin := some bid }
        { m with heap := defineMethod m.heap eigen name md }) m) initial
    match Interp.run bootFuel initial with
    | .value _ m => .ok m
    | .uncaught exc m =>
      let cls := className m.heap (realClassOf m.heap exc)
      .error s!"prelude raised {cls}"
    | .unsupported r _ => .error s!"prelude gated: {r}"
    | .outOfFuel _ => .error "prelude out of fuel"
    | .stuck msg _ => .error s!"prelude stuck: {msg}"

/-- Initial machine for `prog` on the booted (prelude-loaded) heap. The heap
    and globals carry over from phase 1; frames/kont/stdout/`$!` are fresh, and
    `preludeMode` is back to `false` so program `def`s are ordinary. -/
def initWithPrelude (prog : Expr) : Except String Machine := do
  let mp ← boot
  let featurePrograms ← features
  let (heap, pathToId) := mountFiles mp.heap VfsFixture.rawFiles
  -- `pathToId` and `bodies` are in the same (generator) order, so pair them by
  -- position: each body is keyed by the heap id of the file it was mounted as,
  -- carrying the canonical path for the loaded frame's `sourcePath` (so a nested
  -- `require_relative` resolves from the right directory). Positional pairing
  -- keeps boot free of string matching, which the kernel must reduce.
  let requireBodies : List (ObjId × String × Expr) :=
    (pathToId.zip VfsFixture.bodies).map fun ((path, id), e) => (id, path, e)
  return { Machine.initOn heap prog with
    globals := mp.globals, numericLiterals := mp.numericLiterals, featurePrograms, requireBodies }

end Prelude
end RubyCore
