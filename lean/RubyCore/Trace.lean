/-
Playground trace mode: serialize every `stepFn` configuration to JSON so a UI
can step through execution. This is a tooling view, NOT the Ruby-faithful
observation (`Obs.lean`) — the renderers here are deliberately lossy and
never gate (a partial Float or a Proc just prints a short label).
-/
import RubyCore.Interp

namespace RubyCore
namespace Trace

open Lean (Json)

/-- Short, non-gating rendering of a value (bounded depth against cycles). -/
partial def valBrief (h : Heap) : Nat → Value → String
  | _, .int n => toString n
  | _, .flt x => toString x
  | _, .sym s => ":" ++ s
  | _, .bool b => toString b
  | _, .nil => "nil"
  | 0, _ => "…"
  | d+1, .ref o =>
    match (h.get o).payload with
    | .str s => "\"" ++ s ++ "\""
    | .arr xs => "[" ++ String.intercalate ", " (xs.toList.map (valBrief h d)) ++ "]"
    | .hsh xs => "{" ++ String.intercalate ", "
        (xs.toList.map (fun (k, v) => valBrief h d k ++ " => " ++ valBrief h d v)) ++ "}"
    | .cls c => c.name
    | .exc msg =>
      let cn := className h (h.get o).klass
      if msg.isEmpty then cn else s!"#<{cn}: {msg}>"
    | .proc c => if c.lam then "#<Proc (lambda)>" else "#<Proc>"
    | .rng _ => "#<Random>"
    | .range lo hi excl => valBrief h d lo ++ (if excl then "..." else "..") ++ valBrief h d hi
    | .regexp src _ => "/" ++ src ++ "/"
    | .mdata _ caps _ => s!"#<MatchData {caps.size} slots>"
    | .none =>
      if o == Boot.mainId then "main"
      else s!"#<{className h (h.get o).klass}##{o}>"

/-- One-line head label for the expression about to be evaluated. -/
def exprBrief : Expr → String
  | .int n => s!"int {n}"
  | .flt x => s!"flt {x}"
  | .str s => s!"str \"{s}\""
  | .sym s => s!"sym :{s}"
  | .tru => "true" | .fls => "false" | .nil => "nil" | .self' => "self"
  | .var _ n => s!"var {n}"
  | .vasgn _ n _ => s!"{n} = …"
  | .const n => s!"const {n}"
  | .casgn n _ => s!"{n} = …"
  | .cpath _ n => s!"…::{n}" | .cpathAsgn _ n _ => s!"…::{n} = …"
  | .defined _ => "defined?(…)"
  | .send _ m _ _ => s!"send .{m}(…)"
  | .vcall m => s!"vcall {m}"
  | .kwargs _ => "kwargs(…)" | .fwd => "..."
  | .block .. => "block { … }"
  | .yield' _ => "yield"
  | .blockpass _ => "&block"
  | .if' .. => "if" | .while' .. => "while" | .dowhile .. => "do-while"
  | .for' .. => "for"
  | .def' n _ _ => s!"def {n}"
  | .array _ => "array [ … ]" | .hash _ => "hash { … }"
  | .splat _ => "splat *"
  | .ret _ => "return" | .brk _ => "break" | .nxt _ => "next" | .retry' => "retry"
  | .redo' => "redo"
  | .class' n _ _ => s!"class {n}" | .module' n _ => s!"module {n}"
  | .scopedClass _ n _ => s!"class …::{n}" | .scopedModule _ n _ => s!"module …::{n}"
  | .sclass .. => "class << …" | .defs _ n _ _ => s!"def self.{n}"
  | .begin' .. => "begin" | .super' .. => "super(…)" | .zsuper _ => "super"
  | .undef ns => s!"undef {ns.length}" | .alias' n o => s!"alias {n} {o}"
  | .seq es => s!"seq[{es.length}]"

def jumpBrief (h : Heap) : Jump → String
  | .raiseJ e => s!"raise {valBrief h 3 e}"
  | .retJ v t => s!"return {valBrief h 3 v} →frame#{t}"
  | .brkJ v => s!"break {valBrief h 3 v}"
  | .nxtJ v => s!"next {valBrief h 3 v}"
  | .retryJ => "retry"
  | .redoJ => "redo"
  | .throwJ t v => s!"throw {valBrief h 3 t}, {valBrief h 3 v}"

def ctlBrief (h : Heap) : Ctl → String
  | .eval e => "eval  " ++ exprBrief e
  | .value v => "value  " ++ valBrief h 5 v
  | .jump j => "jump  " ++ jumpBrief h j

/-- Continuation-frame label (top of the kont stack = what happens next). -/
def kontLabel : Kont → String
  | .seqK rest => s!"seq (+{rest.length} more)"
  | .asgnK _ x => s!"then {x} = ▢"
  | .casgnK n => s!"then {n} = ▢"
  | .classDefK name _ => s!"then open class {name} < ▢"
  | .newK _ => "then yield new instance"
  | .methodAddedK n => s!"then yield :{n} (method_added hook)"
  | .raiseNewK _ => "then raise the new exception"
  | .includeK _ => "then yield include receiver"
  | .defsK name .. => s!"then def ▢.{name}"
  | .sclassK _ => "then open singleton class of ▢"
  | .cpathK n => s!"then ▢::{n}"
  | .cpathAsgnK n _ => s!"then ▢::{n} = …"
  | .cpathAsgnValK n _ => s!"then …::{n} = ▢"
  | .scopedClassDefK n _ _ => s!"then open ▢::{n}"
  | .ifK .. => "then pick if-branch"
  | .whileCondK .. => "while: test ▢"
  | .whileBodyK .. => "while: after body"
  | .forStartK .. => "for: start ▢"
  | .forBodyK .. => "for: after body"
  | .iterK _ _ rest .. => s!"iterate (+{rest.length} more)"
  | .optDefK n .. => s!"then bind opt {n} = ▢"
  | .definedRecvK m => s!"then defined?(▢.{m})"
  | .definedCpathK n => s!"then defined?(▢::{n})"
  | .definedGuardK => "defined?: swallow a raise"
  | .recvK m .. => s!"then send .{m}"
  | .argsK _ _ m .. => s!"collect args for .{m}"
  | .argsSplatK _ _ m .. => s!"splat args for .{m}"
  | .blkCoerceK _ _ m _ _ => s!"coerce &block for .{m}"
  | .kwPairK k .. => s!"kwarg {k}: ▢"
  | .kwDynKeyK .. => "kwarg ▢ => _"
  | .kwDynValK .. => "kwarg _ => ▢"
  | .kwSplatK .. => "kwarg **▢"
  | .yieldArgK .. => "collect yield args"
  | .yieldSplatK .. => "splat yield args"
  | .superArgK .. => "collect super args"
  | .superSplatK .. => "splat super args"
  | .arrK .. => "array: next element"
  | .arrSplatK .. => "array: splat element"
  | .hshKeyK .. => "hash: value for key ▢"
  | .hshValK .. => "hash: next pair"
  | .jumpValK _ => "then jump with ▢"
  | .frameK fid => s!"◀ method frame #{fid}"
  | .blkFrameK fid .. => s!"◀ block frame #{fid}"
  | .catchK _ => "catch: await throw"
  | .beginBodyK _ => "begin body (rescues live)"
  | .rescMatchK .. => "rescue: match class ▢"
  | .rescueK .. => "rescue handler"
  | .elseK _ => "else clause"
  | .ensureK .. => "ensure clause"

def frameKindStr : FrameKind → String
  | .toplevel => "toplevel" | .method => "method" | .block => "block"
  | .classBody => "class-body"

/-- Snapshot of one machine configuration. -/
def snapshot (m : Machine) : Json :=
  let h := m.heap
  let frames := m.stack.map fun fid =>
    let f := m.frames.getD fid default
    Json.mkObj [
      ("id", Json.str (toString fid)),
      ("kind", Json.str (frameKindStr f.kind)),
      ("self", Json.str (valBrief h 3 f.self)),
      ("blk", Json.str (if f.blk.isSome then "block?=yes" else "")),
      ("lam", Json.str (if f.lam then "λ" else "")),
      ("locals", Json.arr (f.locals.reverse.map (fun (n, v) =>
        Json.mkObj [("name", Json.str n), ("val", Json.str (valBrief h 4 v))])).toArray)]
  Json.mkObj [
    ("ctl", Json.str (ctlBrief h m.ctl)),
    ("out", Json.str m.out),
    ("exc", Json.str (match m.currentExc with | some e => valBrief h 3 e | none => "")),
    ("frames", Json.arr frames.toArray),
    ("konts", Json.arr (m.kont.map (fun k => Json.str (kontLabel k))).toArray)]

/-- Collect a snapshot before each step until termination or the step cap. -/
partial def collect (steps maxSteps : Nat) (acc : Array Json) (m : Machine) :
    Array Json × String × String :=
  if steps ≥ maxSteps then (acc.push (snapshot m), "step-cap", s!"stopped at {maxSteps} steps")
  else
    let acc := acc.push (snapshot m)
    match Interp.stepFn m with
    | .next m' => collect (steps + 1) maxSteps acc m'
    | .done v m' => (acc.push (snapshot m'), "done", valBrief m'.heap 6 v)
    | .uncaught exc m' => (acc.push (snapshot m'), "uncaught", valBrief m'.heap 4 exc)
    | .unsupported r => (acc, "unsupported", r)
    | .stuck msg => (acc, "stuck", msg)

def traceJson (maxSteps : Nat) (m : Machine) : Json :=
  let (steps, status, detail) := collect 0 maxSteps #[] m
  Json.mkObj [
    ("steps", Json.arr steps),
    ("status", Json.str status),
    ("detail", Json.str detail)]

end Trace
end RubyCore
