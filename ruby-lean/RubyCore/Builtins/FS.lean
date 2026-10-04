import RubyCore.Builtins.Regex

/-!
The filesystem singleton methods of issue #7 step 1: `File.read`/`write`/
`exist?`/`file?`/`directory?`/`size` over the symbolic boot fixture
(`RubyCore/Heap.lean` §Virtual filesystem).

The pure machine never performs OS effects; every operation here reads or mutates
the fixture tree that lives in the heap. An unmodeled operation is a named
`Unsupported` — never a guessed value and never a fake `Errno` (issue #7's
"gate stays honest"). `Errno` classes and message fidelity are step 7.

`File.write` mutates inode bytes in place; `flush` is a no-op because descriptor
writes update the inode on write (the documented step-2 simplification, and the
only descriptor behavior step 1 needs).
-/

namespace RubyCore

namespace Builtins

/-- Read a String argument as a path, or `none` if it is not a String. -/
def pathArg? (m : Machine) : Value → Option String
  | .ref o => match (m.heap.get o).payload with
    | .str s => some s
    | _ => none
  | _ => none

/-- A `File.*` / `Dir.*` / `IO.*` singleton operation. `recv` is the class
    object; `args` are the Ruby arguments. -/
def runFS (bid : String) (recv : Value) (args : List Value) (m : Machine) : BRes :=
  let h := m.heap
  match bid with
  | "File#read" | "IO#read" =>
    match args with
    | [p] =>
      match pathArg? m p with
      | some path =>
        match VFS.lookup h path with
        | some o =>
          match (h.get o).payload with
          | .file bytes => okStr m bytes
          | .dir _ _ => .unsupported "File.read: is a directory (Errno::EISDIR gated at step 1)"
          | _ => .unsupported "File.read: not a regular file"
        | none => .unsupported "File.read: no such file (Errno::ENOENT gated at step 1)"
      | none => .unsupported "File.read: path argument is not a String"
    | _ => .unsupported s!"{bid}: argument shape outside step 1"
  | "File#write" | "IO#write" =>
    match args with
    | [p, data] =>
      match pathArg? m p, pathArg? m data with
      | some path, some bytes =>
        match VFS.lookup h path with
        | some o =>
          match (h.get o).payload with
          | .file _ =>
            let h' := h.set o { h.get o with payload := .file bytes }
            .ok (.int (Int.ofNat bytes.length)) { m with heap := h' }
          | .dir _ _ => .unsupported "File.write: is a directory (Errno::EISDIR gated at step 1)"
          | _ => .unsupported "File.write: not a regular file"
        | none => .unsupported "File.write: no such file (Errno::ENOENT gated at step 1)"
      | _, _ => .unsupported "File.write: path or data argument is not a String"
    | _ => .unsupported s!"{bid}: argument shape outside step 1"
  | "File#exist?" | "Dir#exist?" =>
    match args with
    | [p] => (match pathArg? m p with
      | some path => .ok (.bool (VFS.lookup h path).isSome) m
      | none => .unsupported s!"{bid}: path argument is not a String")
    | _ => .unsupported s!"{bid}: argument shape outside step 1"
  | "File#file?" =>
    match args with
    | [p] => (match pathArg? m p with
      | some path => match VFS.lookup h path with
        | some o => .ok (.bool (match (h.get o).payload with | .file _ => true | _ => false)) m
        | none => .ok (.bool false) m
      | none => .unsupported s!"{bid}: path argument is not a String")
    | _ => .unsupported s!"{bid}: argument shape outside step 1"
  | "File#directory?" =>
    match args with
    | [p] => (match pathArg? m p with
      | some path => match VFS.lookup h path with
        | some o => .ok (.bool (match (h.get o).payload with | .dir _ _ => true | _ => false)) m
        | none => .ok (.bool false) m
      | none => .unsupported s!"{bid}: path argument is not a String")
    | _ => .unsupported s!"{bid}: argument shape outside step 1"
  | "File#size" =>
    match args with
    | [p] => (match pathArg? m p with
      | some path => match VFS.lookup h path with
        | some o => match (h.get o).payload with
          | .file bytes => .ok (.int (Int.ofNat bytes.length)) m
          | .dir _ _ => .unsupported "File.size: is a directory (Errno::EISDIR gated at step 1)"
          | _ => .unsupported "File.size: not a regular file"
        | none => .unsupported "File.size: no such file (Errno::ENOENT gated at step 1)"
      | none => .unsupported "File.size: path argument is not a String")
    | _ => .unsupported "File#size: argument shape outside step 1"
  | _ => runRegex bid recv args m

end Builtins

end RubyCore
