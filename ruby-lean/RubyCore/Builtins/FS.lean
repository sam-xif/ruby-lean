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

Step 2 adds descriptors: non-block `File.open` allocates an `IO` object
(`Payload.io`) naming its inode, `IO#read`/`#write` move a per-descriptor
position, `IO#close` marks it closed, and `IO#closed?` observes that. A
read/write on a closed stream, or a write on a read-only descriptor, would raise
`IOError`/`Errno` in CRuby; those classes are step 7, so those shapes return a
named `Unsupported` rather than fabricating an error object.
-/

namespace RubyCore

namespace Builtins

/-- Read a String argument as a path, or `none` if it is not a String. -/
def pathArg? (m : Machine) : Value → Option String
  | .ref o => match (m.heap.get o).payload with
    | .str s => some s
    | _ => none
  | _ => none

/-- Parse a `File.open` mode string into an `IOMode`. `none` for a mode outside
    the step-2 fragment (`b`-suffixed forms and anything else), which gates by
    name. -/
def ioMode? (s : String) : Option IOMode :=
  match s with
  | "r" => some .read
  | "w" => some .write
  | "a" => some .append
  | "r+" => some .readWrite
  | _ => none

/-- Parse the argument list of `IO#read`: `[]` means read-to-EOF (`some none`),
    `[Integer n]` means read at most `n` bytes (`some (some n)`), and any other
    shape is `none` (gate). A negative length, or a non-Integer argument, is
    outside the step-2 fragment. -/
def readLen : List Value → Option (Option Nat)
  | [] => some none
  | [.int n] => if n < 0 then none else some (some n.toNat)
  | _ => none

/-- Open `path` (already resolved from a String argument) for `modeStr`,
    returning a fresh `IO` descriptor object (issue #7 step 2, non-block form).
    `"w"` truncates the inode to empty at open; `"a"` leaves the bytes and
    starts the position at end of file; `"r"`/`"r+"` start at zero. A missing
    path, a directory, or a mode outside `ioMode?` gates (ENOENT/EISDIR/mode are
    step 7), and nothing here fabricates an `Errno`. -/
def openIO (path modeStr : String) (m : Machine) : BRes :=
  let h := m.heap
  match ioMode? modeStr with
  | none => .unsupported s!"File.open: mode {modeStr} outside step 2"
  | some mode =>
    match VFS.lookup h path with
    | some inode =>
      match (h.get inode).payload with
      | .file existing =>
        let startPos := if mode == .append then existing.length else 0
        let h := if mode == .write then h.set inode { h.get inode with payload := .file "" } else h
        let (o, h) := h.alloc { klass := Boot.fileId, payload := .io inode mode startPos false }
        .ok (.ref o) { m with heap := h }
      | .dir _ _ => .unsupported "File.open: is a directory (Errno::EISDIR gated at step 7)"
      | _ => .unsupported "File.open: not a regular file"
    | none => .unsupported "File.open: no such file (Errno::ENOENT gated at step 7)"

/-- A `File.*` / `Dir.*` / `IO.*` singleton operation. `recv` is the class
    object; `args` are the Ruby arguments. -/
def runFS (bid : String) (recv : Value) (args : List Value) (m : Machine) : BRes :=
  let h := m.heap
  match bid with
  | "File#read" | "IO#read" =>
    -- Instance `IO#read` (step 2) vs the step-1 class method `IO.read(path)`:
    -- a descriptor receiver carries an `.io` payload and reads from its inode.
    match recv with
    | .ref ro =>
      match (h.get ro).payload with
      | .io inode mode pos closed =>
        if closed then .unsupported "IO#read: closed stream (IOError gated at step 2)"
        else match mode with
          | .write | .append => .unsupported "IO#read: not opened for reading (IOError gated at step 2)"
          | _ =>
            match (h.get inode).payload with
            | .file bytes =>
              if bytes.length < pos then
                .unsupported "IO#read: position past end of file"
              else match readLen args with
              | none => .unsupported "IO#read: argument shape outside step 2"
              | some none =>
                -- `read` reads to EOF, answers `""` there, and leaves the
                -- position at end of file.
                let rest := (bytes.drop pos).toString
                let h' := h.set ro { h.get ro with payload := .io inode mode bytes.length closed }
                okStrEnc { m with heap := h' } (h.get inode).binary rest
              | some (some n) =>
                let avail := bytes.length - pos
                if avail == 0 then
                  -- `read(n)` answers `nil` at end of file.
                  .ok .nil m
                else
                  let taken := (bytes.drop pos).take (min n avail) |>.toString
                  let h' := h.set ro { h.get ro with
                    payload := .io inode mode (pos + taken.length) closed }
                  okStrEnc { m with heap := h' } (h.get inode).binary taken
            | _ => .unsupported "IO#read: inode is not a regular file"
      | _ =>
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
        | _ => .unsupported s!"{bid}: argument shape outside step 2"
    | _ => .unsupported s!"{bid}: unexpected receiver"
  | "File#write" | "IO#write" =>
    -- Instance `IO#write` (step 2) vs the step-1 class method `IO.write(path, data)`.
    match recv with
    | .ref ro =>
      match (h.get ro).payload with
      | .io inode mode pos closed =>
        match args with
        | [data] =>
          match pathArg? m data with
          | some bytes =>
            if closed then .unsupported "IO#write: closed stream (IOError gated at step 2)"
            else match mode with
            | .read => .unsupported "IO#write: not opened for writing (IOError gated at step 2)"
            | _ =>
              match (h.get inode).payload with
              | .file existing =>
                let writeAt := if mode == .append then existing.length else pos
                let merged := (existing.take writeAt).toString ++ bytes ++
                  (existing.drop (min (writeAt + bytes.length) existing.length)).toString
                let h' := h.set inode { h.get inode with payload := .file merged }
                let h' := h'.set ro { h'.get ro with payload := .io inode mode (writeAt + bytes.length) closed }
                .ok (.int (Int.ofNat bytes.length)) { m with heap := h' }
              | _ => .unsupported "IO#write: inode is not a regular file"
          | none => .unsupported "IO#write: data argument is not a String"
        | _ => .unsupported s!"{bid}: argument shape outside step 2"
      | _ =>
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
    | _ => .unsupported s!"{bid}: unexpected receiver"
  -- `File#__open` is the **internal** primitive behind `File.open` (issue #7
  -- step 4). The public `File.open` is a prelude method (prelude.rb) so the
  -- block form can `begin … ensure … close` around a real `yield`; a pure
  -- builtin cannot push a block frame. The prelude's non-block arm delegates
  -- here, so the descriptor semantics below are the single definition and the
  -- `File.open` argument shape stays entirely in the prelude.
  | "File#__open" =>
    match args with
    | [p] =>
      match pathArg? m p with
      | some path => openIO path "r" m
      | none => .unsupported "File.open: path argument is not a String"
    | [p, modeArg] =>
      match pathArg? m p, pathArg? m modeArg with
      | some path, some modeStr => openIO path modeStr m
      | _, _ => .unsupported "File.open: path or mode argument is not a String"
    | _ => .unsupported "File.open: argument shape outside step 2"
  | "IO#close" =>
    match recv with
    | .ref ro =>
      match (h.get ro).payload with
      | .io inode mode pos closed =>
        if closed then .unsupported "IO#close: closed stream (IOError gated at step 2)"
        else
          let h' := h.set ro { h.get ro with payload := .io inode mode pos true }
          .ok .nil { m with heap := h' }
      | _ => .unsupported "IO#close: not an open IO (singleton form is step 2+)"
    | _ => .unsupported "IO#close: unexpected receiver"
  | "IO#closed?" =>
    match recv with
    | .ref ro =>
      match (h.get ro).payload with
      | .io _ _ _ closed => .ok (.bool closed) m
      | _ => .unsupported "IO#closed?: not an open IO"
    | _ => .unsupported "IO#closed?: unexpected receiver"
  | "IO#flush" =>
    -- Descriptor writes update the inode immediately, so `flush` is a no-op on
    -- a live descriptor and gates on anything else (issue #7's documented
    -- simplification).
    match recv with
    | .ref ro =>
      match (h.get ro).payload with
      | .io _ _ _ false => .ok recv m
      | .io _ _ _ true => .unsupported "IO#flush: closed stream (IOError gated at step 2)"
      | _ => .unsupported "IO#flush: not an open IO"
    | _ => .unsupported "IO#flush: unexpected receiver"
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
