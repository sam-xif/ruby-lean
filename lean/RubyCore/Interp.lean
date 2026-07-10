/-
The executable step function (lean-model-sketch §3): `stepFn` is one
small-step transition of the machine; `run` iterates it under fuel.

The inductive `Step : Config → Config → Prop` (the definition of record)
will be authored against this — `stepFn` is its constructive witness; for
now the interpreter comes first so the model can meet the difftest engine
immediately (sketch §4). Note the helpers below are NOT mutually recursive:
each performs exactly one transition — evidence the machine really is
small-step.

Out-of-fragment RubyCore constructs surface as `.unsupported` — the SUT
contract's clean gate, never a guessed value.
-/
import RubyCore.Builtins
import RubyCore.CRubyNames

namespace RubyCore

inductive StepResult where
  | next (m : Machine)
  | done (v : Value) (m : Machine)
  | uncaught (exc : Value) (m : Machine)
  | unsupported (reason : String)
  | stuck (msg : String)

namespace Interp

/-- User `def`s of these names shadow builtins that pure repr silently
    assumes; flip `reprPure` when one lands (Builtins.pureOk gates). -/
def reprSensitive : List String :=
  ["to_s", "inspect", "==", "eql?", "message", "to_str"]

def raiseErr (m : Machine) (cls : ObjId) (msg : String) : Machine :=
  let (v, m) := Builtins.allocExc m cls msg
  { m with ctl := .jump (.raiseJ v) }

def withCtl (m : Machine) (c : Ctl) : Machine := { m with ctl := c }

def withKont (m : Machine) (c : Ctl) (k : Kont) : Machine :=
  { m with ctl := c, kont := k :: m.kont }

def bindIvar (m : Machine) (x : String) (v : Value) : Machine :=
  match m.currentFrame.self with
  | .ref o =>
    let obj := m.heap.get o
    let obj := { obj with ivars := (x, v) :: obj.ivars.filter (·.1 != x) }
    { m with heap := m.heap.set o obj }
  | _ => m

/-- Enter the ensure body (if any) with `pending` to resume; else resume
    pending immediately. While an ensure runs for an in-flight raise, `$!`
    is that exception [V] (test_exception_010). -/
def finishRegion (m : Machine) (ens : Option Expr) (pending : Pending) : Machine :=
  match ens with
  | some e =>
    match pending with
    | .jmp (.raiseJ exc) =>
      let saved := m.currentExc
      withKont { m with currentExc := some exc } (.eval e)
        (.ensureK pending (some saved))
    | _ => withKont m (.eval e) (.ensureK pending none)
  | none =>
    match pending with
    | .val v => withCtl m (.value v)
    | .jmp j => withCtl m (.jump j)

/-- Transfer control into a rescue handler: set `$!`, bind the `=> x`
    target, remember the outer `$!` for restore (artifact 04 §5). -/
def enterHandler (m : Machine) (node : BeginNode) (exc : Value)
    (ref : Option (TargetKind × String)) (handler : Expr) : Machine :=
  let saved := m.currentExc
  let m := { m with currentExc := some exc }
  let m := match ref with
    | some (.lvar, x) => m.setLocal x exc
    | some (.gvar, x) => m.setGlobal x exc
    | some (.ivar, x) => bindIvar m x exc
    | some (.const, n) => { m with heap := constSet m.heap n exc }
    | some (.cvar, _) => m   -- gated at begin' eval; unreachable
    | none => m
  withKont m (.eval handler) (.rescueK node saved)

/-- Advance rescue-clause matching for in-flight `exc` (artifact 04 §5).
    Clause exprs evaluate lazily, one at a time; an empty exc list is the
    default `[StandardError]` and needs no evaluation. -/
def nextClause (m : Machine) (node : BeginNode) (exc : Value)
    (clauses : List (List Expr × Option (TargetKind × String) × Expr)) : Machine :=
  match clauses with
  | [] => finishRegion m node.ens (.jmp (.raiseJ exc))
  | (excs, ref, handler) :: rest =>
    match excs with
    | [] =>
      if isA m.heap exc Boot.standardErrorId then
        enterHandler m node exc ref handler
      else nextClause m node exc rest
    | e :: es =>
      withKont m (.eval e) (.rescMatchK node exc es ref handler rest)

/-- How a NoMethodError describes its receiver [V]:
    main / nil / true / false literally; classes as "class C";
    everything else "an instance of C". -/
def receiverDesc (h : Heap) (v : Value) : String :=
  match v with
  | .nil => "nil"
  | .bool b => toString b
  | .ref o =>
    if o == Boot.mainId then "main"
    else match (h.get o).payload with
      | .cls c => (if c.isModule then "module " else "class ") ++ c.name
      | _ => s!"an instance of {className h (h.get o).klass}"
  | _ => s!"an instance of {className h (classOf h v)}"

/-- Would CRuby find `mname` on some class of `chain` (per the generated
    name tables) even though our model doesn't define it there? -/
def crubyShadow (h : Heap) (chain : List ObjId) (mname : String) : Option String :=
  chain.firstM fun k =>
    let cname := className h k
    if crubyClassDefines cname mname then some cname else none

/-- For a *class object* receiver: would CRuby find `mname` on the class's
    singleton chain (e.g. `Hash.ruby2_keywords_hash`)? We have no
    eigenclasses yet, so any singleton hit is unmodeled. Only consulted when
    our lookup did NOT resolve to a builtin (our class-aware builtins like
    Class#new deliberately subsume the common singleton constructors). -/
def crubySingletonShadow (h : Heap) (recv : Value) (mname : String) : Option String :=
  match recv with
  | .ref o =>
    match (h.get o).payload with
    | .cls _ =>
      (ancestors h o).firstM fun k =>
        let cname := className h k
        if crubySingletonDefines cname mname then some cname else none
    | _ => none
  | _ => none

/-- Split a desugared param list: `"*name"` marks the rest param (post-rest
    required params are allowed: `a, *b, c`). -/
def parseParams (ps : List String) : List String × Option String × List String :=
  match ps.findIdx? (·.startsWith "*") with
  | none => (ps, none, [])
  | some i =>
    (ps.take i, some ((ps[i]!).drop 1 |>.toString), ps.drop (i + 1))

/-- Spread a splat operand [V]: array splices, nil vanishes, anything else
    (without to_a) is itself. Hash's pair-conversion is gated for now. -/
def spread (m : Machine) (v : Value) : Except String (List Value) :=
  match v with
  | .ref o =>
    match (m.heap.get o).payload with
    | .arr xs => .ok xs.toList
    | .hsh _ => .error "splat of a Hash (to_a pairs)"
    | _ => .ok [v]
  | .nil => .ok []
  | _ => .ok [v]

/-- All args evaluated → dispatch (artifact 02 §3 SEND-INVOKE). -/
def invoke (m : Machine) (recv : Value) (implicit : Bool) (mname : String)
    (args : List Value) : StepResult :=
  let chain := ancestors m.heap (classOf m.heap recv)
  match lookup m.heap recv mname with
  | some (owner, md) =>
    -- Dispatch fidelity: if CRuby defines `mname` on a class BETWEEN the
    -- receiver's class and our resolved owner, CRuby would dispatch there —
    -- we'd be running the wrong method. Gate. (Builtins are exempt only
    -- from their own owner downward.)
    let between := chain.takeWhile (· != owner)
    match crubyShadow m.heap between mname with
    | some cname => .unsupported s!"unmodeled builtin would shadow: {cname}#{mname}"
    | none =>
      match md.builtin with
      | some bid =>
        match Builtins.run bid recv args m with
        | .ok v m => .next (withCtl m (.value v))
        | .err cls msg m => .next (raiseErr m cls msg)
        | .throwV v m => .next (withCtl m (.jump (.raiseJ v)))
        | .unsupported r => .unsupported r
      | none =>
        match crubySingletonShadow m.heap recv mname with
        | some cname => .unsupported s!"unmodeled singleton method {cname}.{mname}"
        | none =>
          -- a RubyCore-defined method: required + rest binding (L0+splat)
          let (pre, rest?, post) := parseParams md.params
          let required := pre.length + post.length
          let arityOk := match rest? with
            | some _ => args.length ≥ required
            | none => args.length == required
          if !arityOk then
            let expected := match rest? with
              | some _ => s!"{required}+"
              | none => toString required
            .next (raiseErr m Boot.argumentErrorId
              s!"wrong number of arguments (given {args.length}, expected {expected})")
          else
            let preArgs := args.take pre.length
            let postArgs := args.drop (args.length - post.length)
            let midArgs := (args.drop pre.length).take (args.length - required)
            let (locals, m) := match rest? with
              | none => (pre.zip preArgs ++ post.zip postArgs, m)
              | some rname =>
                let (rv, m) := Builtins.allocArr m midArgs.toArray
                (pre.zip preArgs ++ [(rname, rv)] ++ post.zip postArgs, m)
            let frame : Frame :=
              { self := recv, locals, defmod := md.owner, kind := .method }
            let fid := m.frames.size
            let m := { m with frames := m.frames.push frame,
                              stack := fid :: m.stack }
            .next (withKont m (.eval md.body) (.frameK fid))
  | none =>
    match crubySingletonShadow m.heap recv mname with
    | some cname => .unsupported s!"unmodeled singleton method {cname}.{mname}"
    | none =>
    match crubyShadow m.heap chain mname with
    | some cname =>
      -- exists in CRuby, not in the model — the fragment gate
      .unsupported s!"unmodeled method {cname}#{mname}"
    | none =>
      -- total miss: CRuby wouldn't find it either. A bare implicit-self
      -- zero-arg send is ambiguous (vcall → NameError with a different
      -- message vs fcall → NoMethodError; RubyCore conflates them) — gate.
      if implicit && args.isEmpty then
        .unsupported s!"vcall/fcall NameError ambiguity: {mname}"
      else
        .next (raiseErr m Boot.noMethodErrorId
          s!"undefined method '{mname}' for {receiverDesc m.heap recv}")

/-- Evaluate the next pending argument, or dispatch if none remain. -/
def startArgs (m : Machine) (recv : Value) (implicit : Bool) (mname : String)
    (acc : List Value) (rest : List Expr) : StepResult :=
  match rest with
  | [] => invoke m recv implicit mname acc
  | e :: rest' =>
    match e with
    | .splat (some e) =>
      .next (withKont m (.eval e) (.argsSplatK recv implicit mname acc rest'))
    | .splat none => .unsupported "anonymous splat forwarding"
    | _ => .next (withKont m (.eval e) (.argsK recv implicit mname acc rest'))

/-- Evaluate the next pending array-literal element, or allocate. -/
def continueArray (m : Machine) (acc : List Value) (rest : List Expr) : StepResult :=
  match rest with
  | [] =>
    let (av, m) := Builtins.allocArr m acc.toArray
    .next (withCtl m (.value av))
  | e :: rest' =>
    match e with
    | .splat (some e) => .next (withKont m (.eval e) (.arrSplatK acc rest'))
    | .splat none => .unsupported "anonymous splat in array literal"
    | _ => .next (withKont m (.eval e) (.arrK acc rest'))

/-- Deliver a value to the top continuation. -/
def applyKont (m : Machine) (v : Value) : StepResult :=
  match m.kont with
  | [] => .done v m
  | k :: rest =>
    let m := { m with kont := rest }
    match k with
    | .seqK es =>
      match es with
      | [] => .next (withCtl m (.value v))
      | e :: rest' => .next (withKont m (.eval e) (.seqK rest'))
    | .asgnK kind x =>
      match kind with
      | .lvar => .next (withCtl (m.setLocal x v) (.value v))
      | .gvar => .next (withCtl (m.setGlobal x v) (.value v))
      | .ivar =>
        match m.currentFrame.self with
        | .ref _ => .next (withCtl (bindIvar m x v) (.value v))
        | selfV =>
          -- immediates are frozen: @x= with Integer self → FrozenError [V]
          match Builtins.inspectP m selfV with
          | .ok r => .next (raiseErr m Boot.frozenErrorId
              s!"can't modify frozen {className m.heap (classOf m.heap selfV)}: {r}")
          | .error e => .unsupported e
      | .cvar => .unsupported "class variables"
    | .casgnK n =>
      .next (withCtl { m with heap := constSet m.heap n v } (.value v))
    | .ifK t e =>
      if v.truthy then .next (withCtl m (.eval t))
      else
        match e with
        | some e => .next (withCtl m (.eval e))
        | none => .next (withCtl m (.value .nil))  -- fall-through if → nil [V]
    | .whileCondK c body =>
      if v.truthy then .next (withKont m (.eval body) (.whileBodyK c body))
      else .next (withCtl m (.value .nil))
    | .whileBodyK c body =>
      .next (withKont m (.eval c) (.whileCondK c body))
    | .recvK mname args implicit =>
      startArgs m v implicit mname [] args
    | .argsK recv implicit mname acc rest =>
      startArgs m recv implicit mname (acc ++ [v]) rest
    | .argsSplatK recv implicit mname acc rest =>
      match spread m v with
      | .ok vs => startArgs m recv implicit mname (acc ++ vs) rest
      | .error e => .unsupported e
    | .arrK acc rest => continueArray m (acc ++ [v]) rest
    | .arrSplatK acc rest =>
      match spread m v with
      | .ok vs => continueArray m (acc ++ vs) rest
      | .error e => .unsupported e
    | .hshKeyK acc vExpr rest =>
      .next (withKont m (.eval vExpr) (.hshValK acc v rest))
    | .hshValK acc key rest =>
      -- duplicate keys keep first position, last value [V]
      let acc := match acc.findIdx? (fun (k', _) => valueEql m.heap k' key) with
        | some i => acc.set i (acc[i]!.1, v)
        | none => acc ++ [(key, v)]
      match rest with
      | [] =>
        let (hv, m) := Builtins.allocHsh m acc.toArray
        .next (withCtl m (.value hv))
      | (kE, vE) :: rest' =>
        .next (withKont m (.eval kE) (.hshKeyK acc vE rest'))
    | .jumpValK kind =>
      let j := match kind with
        | .retK => Jump.retJ v
        | .brkK => Jump.brkJ v
        | .nxtK => Jump.nxtJ v
      .next (withCtl m (.jump j))
    | .frameK _ =>
      -- normal completion of a method body: pop the activation
      .next (withCtl { m with stack := m.stack.tail } (.value v))
    | .beginBodyK node =>
      match node.els with
      | some e => .next (withKont m (.eval e) (.elseK node))
      | none => .next (finishRegion m node.ens (.val v))
    | .rescMatchK node exc pend ref handler rest =>
      -- v is a candidate exception-class value
      match v with
      | .ref k =>
        if (m.heap.classPayload? k).isSome then
          if isA m.heap exc k then .next (enterHandler m node exc ref handler)
          else
            match pend with
            | e :: es => .next (withKont m (.eval e)
                (.rescMatchK node exc es ref handler rest))
            | [] => .next (nextClause m node exc rest)
        else
          .next (raiseErr m Boot.typeErrorId
            "class or module required for rescue clause")
      | _ =>
        .next (raiseErr m Boot.typeErrorId
          "class or module required for rescue clause")
    | .rescueK node saved =>
      -- handler completed normally; $! restores [V]
      .next (finishRegion { m with currentExc := saved } node.ens (.val v))
    | .elseK node =>
      .next (finishRegion m node.ens (.val v))
    | .ensureK pending restore =>
      -- ensure's value is discarded; resume what was pending
      let m := match restore with
        | some old => { m with currentExc := old }
        | none => m
      match pending with
      | .val v' => .next (withCtl m (.value v'))
      | .jmp j => .next (withCtl m (.jump j))

/-- Propagate an in-flight jump one kont at a time (artifact 04 §3–6:
    markers consume matching jumps; begin regions interpose rescues/ensures;
    everything else pops). -/
def unwind (m : Machine) (j : Jump) : StepResult :=
  match m.kont with
  | [] =>
    match j with
    | .raiseJ exc => .uncaught exc m
    | _ => .stuck "jump escaped the program (return/break/next/retry at toplevel)"
  | k :: rest =>
    let m := { m with kont := rest }
    match k with
    | .whileCondK c body | .whileBodyK c body =>
      match j with
      | .brkJ v => .next (withCtl m (.value v))
      | .nxtJ _ => .next (withKont m (.eval c) (.whileCondK c body))
      | _ => .next (withCtl m (.jump j))
    | .frameK _ =>
      match j with
      | .retJ v => .next (withCtl { m with stack := m.stack.tail } (.value v))
      | .raiseJ _ => .next (withCtl { m with stack := m.stack.tail } (.jump j))
      | .brkJ _ | .nxtJ _ => .unsupported "break/next crossing a method boundary"
      | .retryJ => .unsupported "retry crossing a method boundary"
    | .beginBodyK node =>
      match j with
      | .raiseJ exc =>
        if node.rescues.isEmpty then
          .next (finishRegion m node.ens (.jmp j))
        else
          .next (nextClause m node exc node.rescues)
      | _ => .next (finishRegion m node.ens (.jmp j))
    | .rescMatchK node _ _ _ _ _ =>
      -- a clause-class expression itself raised/jumped: it supersedes, but
      -- the region's ensure still runs (artifact 04 §5)
      .next (finishRegion m node.ens (.jmp j))
    | .rescueK node saved =>
      match j with
      | .retryJ =>
        -- restart the begin body; ensure does NOT run on retry [V]
        .next (withKont { m with currentExc := saved }
          (.eval node.body) (.beginBodyK node))
      | _ =>
        .next (finishRegion { m with currentExc := saved } node.ens (.jmp j))
    | .elseK node =>
      .next (finishRegion m node.ens (.jmp j))
    | .ensureK _ restore =>
      -- a jump out of an ensure supersedes whatever was pending [V]
      let m := match restore with
        | some old => { m with currentExc := old }
        | none => m
      .next (withCtl m (.jump j))
    | _ => .next (withCtl m (.jump j))

/-- Evaluate one expression head. -/
def evalExpr (m : Machine) (e : Expr) : StepResult :=
  match e with
  | .int n => .next (withCtl m (.value (.int n)))
  | .flt x => .next (withCtl m (.value (.flt x)))
  | .str s =>
    -- string literals allocate a fresh unfrozen String [V]
    let (v, m) := Builtins.allocStr m s
    .next (withCtl m (.value v))
  | .sym s => .next (withCtl m (.value (.sym s)))
  | .tru => .next (withCtl m (.value (.bool true)))
  | .fls => .next (withCtl m (.value (.bool false)))
  | .nil => .next (withCtl m (.value .nil))
  | .self' => .next (withCtl m (.value m.currentFrame.self))
  | .var kind x =>
    match kind with
    | .lvar => .next (withCtl m (.value (m.getLocal x)))
    | .gvar => .next (withCtl m (.value (m.getGlobal x)))
    | .ivar =>
      match m.currentFrame.self with
      | .ref o =>
        let v := ((m.heap.get o).ivars.find? (·.1 == x)).map (·.2) |>.getD .nil
        .next (withCtl m (.value v))
      | _ => .next (withCtl m (.value .nil))  -- unset ivar on immediate self → nil
    | .cvar => .unsupported "class variables"
  | .vasgn kind x rhs =>
    match kind with
    | .cvar => .unsupported "class variables"
    | _ => .next (withKont m (.eval rhs) (.asgnK kind x))
  | .const n =>
    match constLookup m.heap n with
    | some v => .next (withCtl m (.value v))
    | none =>
      -- same fidelity split as methods: a constant CRuby has but we don't
      -- model gates as Unsupported; a genuine miss is a real NameError
      if crubyToplevelConstants.contains n then
        .unsupported s!"unmodeled constant {n}"
      else
        .next (raiseErr m Boot.nameErrorId s!"uninitialized constant {n}")
  | .casgn n rhs => .next (withKont m (.eval rhs) (.casgnK n))
  | .send recv mname args blk =>
    if blk.isSome then .unsupported "block argument (L1)"
    else
      match recv with
      | some r => .next (withKont m (.eval r) (.recvK mname args false))
      | none => startArgs m m.currentFrame.self true mname [] args
  | .block .. => .stuck "bare block node outside send"
  | .if' c t e => .next (withKont m (.eval c) (.ifK t e))
  | .while' c body => .next (withKont m (.eval c) (.whileCondK c body))
  | .def' name params body =>
    let defmod := m.currentFrame.defmod
    let md : MethodDef := { params, body, owner := defmod }
    let m := { m with heap := defineMethod m.heap defmod name md }
    let m := if reprSensitive.contains name then { m with reprPure := false } else m
    .next (withCtl m (.value (.sym name)))
  | .array elems => continueArray m [] elems
  | .hash pairs =>
    match pairs with
    | [] =>
      let (v, m) := Builtins.allocHsh m #[]
      .next (withCtl m (.value v))
    | (kE, vE) :: rest =>
      .next (withKont m (.eval kE) (.hshKeyK [] vE rest))
  | .splat _ => .unsupported "splat outside call/array position"
  | .ret e =>
    -- only meaningful inside a method (the desugar gates toplevel return)
    match e with
    | some e => .next (withKont m (.eval e) (.jumpValK .retK))
    | none => .next (withCtl m (.jump (.retJ .nil)))
  | .brk e =>
    match e with
    | some e => .next (withKont m (.eval e) (.jumpValK .brkK))
    | none => .next (withCtl m (.jump (.brkJ .nil)))
  | .nxt e =>
    match e with
    | some e => .next (withKont m (.eval e) (.jumpValK .nxtK))
    | none => .next (withCtl m (.jump (.nxtJ .nil)))
  | .retry' => .next (withCtl m (.jump .retryJ))
  | .begin' body rescues els ens =>
    -- gate rescue targets we can't bind yet
    if rescues.any (fun (_, ref, _) => match ref with
        | some (.cvar, _) => true | _ => false) then
      .unsupported "class-variable rescue target"
    else
      let node : BeginNode := { body, rescues, els, ens }
      .next (withKont m (.eval body) (.beginBodyK node))
  | .class' .. => .unsupported "class definition (L2)"
  | .module' .. => .unsupported "module definition (L2)"
  | .sclass .. => .unsupported "singleton class (L2)"
  | .defs .. => .unsupported "singleton def (L2)"
  | .super' .. | .zsuper .. => .unsupported "super (L2)"
  | .seq es =>
    match es with
    | [] => .next (withCtl m (.value .nil))
    | [e] => .next (withCtl m (.eval e))
    | e :: rest => .next (withKont m (.eval e) (.seqK rest))

/-- One small step. -/
def stepFn (m : Machine) : StepResult :=
  match m.ctl with
  | .eval e => evalExpr m e
  | .value v => applyKont m v
  | .jump j => unwind m j

inductive RunResult where
  | value (v : Value) (m : Machine)
  | uncaught (exc : Value) (m : Machine)
  | unsupported (reason : String) (m : Machine)
  | outOfFuel (m : Machine)
  | stuck (msg : String) (m : Machine)

/-- Iterate `stepFn` under fuel. `outOfFuel` is distinguished from `stuck`
    from day one (sketch §5: keep co-divergence checking possible). -/
def run (fuel : Nat) (m : Machine) : RunResult :=
  match fuel with
  | 0 => .outOfFuel m
  | fuel + 1 =>
    match stepFn m with
    | .next m' => run fuel m'
    | .done v m' => .value v m'
    | .uncaught exc m' => .uncaught exc m'
    | .unsupported r => .unsupported r m
    | .stuck msg => .stuck msg m

end Interp

end RubyCore
