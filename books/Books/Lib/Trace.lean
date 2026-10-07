import Books.Lib.Boot
import RubyCore.Trace

/-!
# Looking at a concrete run

`#eval Books.trace 200 (start (program 3 2))` prints one line per transition:
its index, the activation stack, the sizes of the frame store and heap, the
control, and the continuation. This is where the frame and object numbers a
proof's states mention come from. It runs compiled code, so it is instant; it
proves nothing.
-/
namespace Books
open RubyCore RubyCore.Interp

def trace (fuel : Nat) (m : Machine) (i : Nat := 0) : IO Unit := do
  match fuel with
  | 0 => IO.println "(out of fuel)"
  | fuel + 1 =>
    IO.println s!"{i} stack={m.stack} frames={m.frames.size} heap={m.heap.objs.size} | {Trace.ctlBrief m.heap m.ctl} | {m.kont.map Trace.kontLabel}"
    match stepFn m with
    | .next m' => trace fuel m' (i + 1)
    | .done v m' => IO.println s!"DONE {Trace.valBrief m'.heap 3 v} out={m'.out.quote}"
    | .uncaught _ _ => IO.println "UNCAUGHT"
    | .unsupported r => IO.println s!"UNSUPPORTED {r}"
    | .stuck r => IO.println s!"STUCK {r}"

/-- The locals of frame `fid` and the instance variables of object `o`. -/
def showState (m : Machine) (fid : Nat) (o : ObjId) : String :=
  let render := fun (kv : String × Value) => s!"{kv.1}={Trace.valBrief m.heap 2 kv.2}"
  s!"frame {fid} locals: {(m.frames.getD fid default).locals.map render}; " ++
  s!"object {o} ivars: {(m.heap.get o).ivars.map render} revision {(m.heap.get o).revision}"

end Books
