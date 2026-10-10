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

Step 5 adds line reads and positioning over those descriptors: `IO#gets` (all
four CRuby forms, including the `gets(0) = ""` corner), `IO#pos`/`#pos=`, and
`IO#rewind`. `IO#readline` and `IO#each_line` are not primitives — they are
defined in the prelude over `gets`, so that the block form is ordinary Ruby
evaluation; both forward their `*args` to `gets`, and the blockless `each_line`
and the EOF `readline` gate on the unmodeled `Enumerator`/`EOFError`.
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

/-- Parse an `IO#gets` argument list (issue #7 step 5): an optional separator
    (`none` for `gets(nil)`, which reads to EOF) and an optional byte limit.
    The outer `Option` is `none` when the shape is outside the fragment and
    gates.

    CRuby's forms are `gets`, `gets(sep)`, `gets(limit)`, `gets(sep, limit)`
    and `gets(nil)`. The first argument is the separator when it is a String
    or `nil`; a lone Integer is a limit. A negative limit gates. Takes the heap
    because a String separator is a `.ref` whose payload only `strPayload?` can
    read. -/
def getsArgsH (h : Heap) : List Value → Option (Option String × Option Nat)
  | [] => some (some "\n", none)
  | [.nil] => some (none, none)
  | [.int n] => if n < 0 then none else some (some "\n", some n.toNat)
  | [p] =>
    match strPayload? h p with
    | some s => some (some s, none)
    | none => none
  | [.nil, .int n] =>
    -- `gets(nil, limit)`: no separator (read the rest), capped at `limit`.
    if n < 0 then none else some (none, some n.toNat)
  | [p, .int n] =>
    if n < 0 then none
    else match strPayload? h p with
      | some s => some (some s, some n.toNat)
      | none => none
  | _ => none

/-- One `IO#gets` result: the bytes read (`none` at end of file, which CRuby
    answers as `nil`) and the new descriptor position. `limit = some 0` is the
    one shape that answers `""` even at EOF, without moving the position — CRuby
    probes confirm both. A separator `none` reads to EOF; otherwise the line
    runs through the first occurrence of the separator (whole remainder if it is
    absent). A limit truncates the line. Positions and lengths are counted in
    characters, matching the rest of the model's `String` arithmetic (the
    fixture is ASCII). -/
def getsLine (bytes : String) (pos : Nat) (sep : Option String) (limit : Option Nat) :
    Option (Option String × Nat) :=
  let rest := (bytes.drop pos).toString
  match limit with
  | some 0 => some (some "", pos)
  | _ =>
    if pos >= bytes.length then none
    else
      let line :=
        match sep with
        | none => rest
        | some s =>
          if s.isEmpty then rest
          else match rest.splitOn s with
            | first :: _ :: _ => first ++ s
            | _ => rest
      let line := match limit with
        | some n => (line.take n).toString
        | none => line
      some (some line, pos + line.length)

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
  | "File#open" =>
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
  | "IO#gets" =>
    -- Step 5. `gets` reads a separator-delimited line (newline by default),
    -- answers `nil` at end of file, and leaves the position just past the line.
    -- `readline` and `each_line` are built on this in the prelude.
    match recv with
    | .ref ro =>
      match (h.get ro).payload with
      | .io inode mode pos closed =>
        if closed then .unsupported "IO#gets: closed stream (IOError gated at step 5)"
        else match mode with
          | .write | .append => .unsupported "IO#gets: not opened for reading (IOError gated at step 5)"
          | _ =>
            match (h.get inode).payload with
            | .file bytes =>
              if bytes.length < pos then
                .unsupported "IO#gets: position past end of file"
              else match getsArgsH h args with
              | none => .unsupported "IO#gets: argument shape outside step 5"
              | some (sep, limit) =>
                match getsLine bytes pos sep limit with
                | none => .ok .nil m
                | some (some line, newPos) =>
                  let h' := h.set ro { h.get ro with payload := .io inode mode newPos closed }
                  okStrEnc { m with heap := h' } (h.get inode).binary line
                | some (none, _) => .ok .nil m
            | _ => .unsupported "IO#gets: inode is not a regular file"
      | _ => .unsupported "IO#gets: not an open IO"
    | _ => .unsupported "IO#gets: unexpected receiver"
  | "IO#pos" =>
    match recv with
    | .ref ro =>
      match (h.get ro).payload with
      | .io _ _ pos _ => .ok (.int (Int.ofNat pos)) m
      | _ => .unsupported "IO#pos: not an open IO"
    | _ => .unsupported "IO#pos: unexpected receiver"
  | "IO#pos=" =>
    -- `pos=` seeks to an absolute byte offset. A negative offset would raise
    -- `Errno::EINVAL`; that class is step 7, so those shapes gate.
    match recv with
    | .ref ro =>
      match (h.get ro).payload with
      | .io inode mode pos closed =>
        if closed then .unsupported "IO#pos=: closed stream (IOError gated at step 5)"
        else match args with
        | [.int n] =>
          if n < 0 then .unsupported "IO#pos=: negative offset (Errno::EINVAL gated at step 5)"
          else
            let h' := h.set ro { h.get ro with payload := .io inode mode n.toNat closed }
            .ok (.int n) { m with heap := h' }
        | _ => .unsupported "IO#pos=: argument shape outside step 5"
      | _ => .unsupported "IO#pos=: not an open IO"
    | _ => .unsupported "IO#pos=: unexpected receiver"
  | "IO#rewind" =>
    -- `rewind` resets the position to zero. CRuby also flushes writes and resets
    -- the line number; the model's descriptor writes update the inode directly,
    -- so the position reset is the whole observable effect.
    match recv with
    | .ref ro =>
      match (h.get ro).payload with
      | .io inode mode _ closed =>
        if closed then .unsupported "IO#rewind: closed stream (IOError gated at step 5)"
        else
          let h' := h.set ro { h.get ro with payload := .io inode mode 0 closed }
          .ok (.int 0) { m with heap := h' }
      | _ => .unsupported "IO#rewind: not an open IO"
    | _ => .unsupported "IO#rewind: unexpected receiver"
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
