import RubyCore.Interp.Send

/-!
Continuation application (`applyKont`) and jump unwinding (`unwind`) — what
happens when a value or a jump reaches the top of the kont stack.

Split out of `RubyCore/Interp.lean` (L99) with no behaviour change. The helpers
in this machine are deliberately *not* mutually recursive — each performs one
transition — so the file cuts along that existing order and the import chain
records it.
-/

namespace RubyCore

namespace Interp

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
        | .ref o =>
          if (m.heap.get o).frozen then
            match Builtins.inspectP m (.ref o) with
            | .ok r => .next (raiseErr m Boot.frozenErrorId
                s!"can't modify frozen {className m.heap (m.heap.get o).klass}: {r}")
            | .error e => .unsupported e
          else .next (withCtl (bindIvar m x v) (.value v))
        | selfV =>
          -- immediates are frozen: @x= with Integer self → FrozenError [V]
          match Builtins.inspectP m selfV with
          | .ok r => .next (raiseErr m Boot.frozenErrorId
              s!"can't modify frozen {className m.heap (realClassOf m.heap selfV)}: {r}")
          | .error e => .unsupported e
      | .cvar =>
        match cvarScope m with
        | none => .unsupported "class variable in a singleton-class scope"
        | some scope =>
          if scope == Boot.objectId && m.currentFrame.kind == .toplevel then
            .next (raiseErr m Boot.runtimeErrorId "class variable access from toplevel")
          else
            .next (withCtl { m with heap := cvarSetIn m.heap scope x v } (.value v))
    | .casgnK n =>
      let defmod := m.currentFrame.defmod
      let qual := if defmod == Boot.objectId then n else s!"{className m.heap defmod}::{n}"
      let h := nameIfAnonymous m.heap qual v
      .next (withCtl { m with heap := constSetIn h defmod n v } (.value v))
    | .classDefK name body =>
      -- v is the resolved superclass: it must be a non-module Class object [V]
      match v with
      | .ref k =>
        match m.heap.classPayload? k with
        | some c =>
          if c.isModule then
            .next (raiseErr m Boot.typeErrorId
              s!"superclass must be an instance of Class (given an instance of {className m.heap (realClassOf m.heap v)})")
          else enterClassBody m name false (some k) body
        | none =>
          .next (raiseErr m Boot.typeErrorId
            s!"superclass must be an instance of Class (given an instance of {className m.heap (realClassOf m.heap v)})")
      | .nil | .bool _ =>
        -- CRuby phrases these as "given nil"/"given false" — gate rather than
        -- emit the "an instance of …" form.
        .unsupported "superclass is nil/true/false"
      | _ =>
        .next (raiseErr m Boot.typeErrorId
          s!"superclass must be an instance of Class (given an instance of {className m.heap (realClassOf m.heap v)})")
    | .newK inst =>
      -- `initialize` returned; its value is discarded, `new` yields the instance
      .next (withCtl m (.value inst))
    | .methodAddedK name =>
      -- the `method_added` hook returned; its value is discarded and `def`
      -- yields the method name, as if the hook had not run
      .next (withCtl m (.value (.sym name)))
    | .raiseNewK inst =>
      -- `raise C[, msg]` with a user `initialize`: now raise the built instance
      .next (withCtl m (.jump (.raiseJ inst)))
    | .includeK recv =>
      -- `included` hook returned; its value is discarded, `include` yields recv
      .next (withCtl m (.value recv))
    | .defsK name params body =>
      -- `def RECV.name`: install on RECV's eigenclass (v = the evaluated RECV)
      match v with
      | .ref o =>
        let (e, m) := eigenclassOf m o
        -- `def self.m` in a module keeps that module's lexical cref for constant
        -- lookup even though its dispatch owner is the eigenclass (artifact 03).
        let md : MethodDef :=
          { params, body, owner := e, cref := m.currentFrame.cref,
            fromPrelude := m.preludeMode }
        let m := { m with heap := defineMethod m.heap e name md }
        .next (withCtl m (.value (.sym name)))
      | _ =>
        -- singleton def on an immediate (`def 1.m`) — TypeError; message-gate
        .unsupported "singleton def on an immediate"
    | .sclassK body =>
      -- `class << OBJ`: run body with self/cref = OBJ's eigenclass
      match v with
      | .ref o =>
        let (e, m) := eigenclassOf m o
        let frame : Frame := { self := .ref e, defmod := e, kind := .classBody, cref := e :: m.currentFrame.cref }
        let fid := m.frames.size
        let m := { m with frames := m.frames.push frame, stack := fid :: m.stack }
        .next (withKont m (.eval body) (.frameK fid))
      | _ => .unsupported "singleton class of an immediate"
    | .cpathK name =>
      -- v is the evaluated base `A`; resolve constant `name` in its namespace.
      match cpathContainer m v with
      | .error sr => sr
      | .ok o =>
        -- A `private_constant` is invisible through `A::B` even though it is
        -- still there for lexical lookup inside the module (L104), so the miss
        -- path — `const_missing`, else NameError — is the right one.
        let isPrivate := (ancestors m.heap o).any fun a =>
          match m.heap.classPayload? a with
          | some cp => cp.privateConsts.contains name
          | none => false
        match (if isPrivate then none else constLookupFrom m.heap o name) with
        | some cv => .next (withCtl m (.value cv))
        | none =>
          -- CRuby invokes `const_missing` before raising; if the base defines it
          -- (a singleton method), gate rather than emit a spurious NameError.
          let hasCM := match (m.heap.get o).eigen with
            | some e => (methodOn m.heap e "const_missing").isSome
            | none => false
          if hasCM then .unsupported "const_missing hook"
          else if isPrivate then
            -- CRuby distinguishes the two misses [V]: a private constant that
            -- *exists* says so, rather than claiming to be uninitialized.
            .next (raiseErr m Boot.nameErrorId
              s!"private constant {className m.heap o}::{name} referenced")
          else .next (raiseErr m Boot.nameErrorId
            s!"uninitialized constant {className m.heap o}::{name}")
    | .cpathAsgnK name rhs =>
      -- v is base `A`; evaluate `rhs`, then assign (base then rhs order [V]).
      match cpathContainer m v with
      | .error sr => sr
      | .ok o => .next (withKont m (.eval rhs) (.cpathAsgnValK name o))
    | .cpathAsgnValK name base =>
      -- v is the rhs; write it into base's namespace; assignment yields rhs [V].
      let qual := if base == Boot.objectId then name
                  else s!"{className m.heap base}::{name}"
      let h := nameIfAnonymous m.heap qual v
      .next (withCtl { m with heap := constSetIn h base name v } (.value v))
    | .scopedClassDefK name isMod body =>
      -- v is base `A`; open (or create) `name` inside it.
      match cpathContainer m v with
      | .error sr => sr
      | .ok o => enterScopedClassBody m o name isMod body
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
    | .forStartK targets body =>
      -- v is the collection: iterate it natively (the model resolves `each` on a
      -- lookup miss, so `for` cannot desugar to it). `spread` supplies the
      -- element list — Arrays directly, integer Ranges expanded (L63) — and
      -- gates anything whose expansion would need a dispatch.
      match v with
      | .ref o =>
        match (m.heap.get o).payload with
        | .arr xs => forStep m targets body xs.toList v
        | .range .. =>
          match spread m v with
          | .ok vs => forStep m targets body vs v
          | .error e => .unsupported e
        | _ => .unsupported "for over a non-Array collection"
      | _ => .unsupported "for over a non-Array collection"
    | .forBodyK targets body rest coll =>
      forStep m targets body rest coll
    | .iterK cl brk rest kind acc retVal cur =>
      -- v is the block's result for the current element; fold it, then continue.
      match kind with
      | .ignore => iterStep m cl brk rest kind acc retVal
      | .collect => iterStep m cl brk rest kind (acc ++ [v]) retVal
      | .fold => iterStep m cl brk rest kind [v] retVal
      | .maxBy | .minBy =>
        -- keep [bestElem, bestKey]; replace only on a *strict* improvement so ties
        -- keep the earliest element (CRuby's max_by/min_by tie-break).
        match acc with
        | [] => iterStep m cl brk rest kind [cur, v] retVal
        | _ :: bestKey :: _ =>
          match Builtins.numOrd? v bestKey with
          | none => .unsupported "max_by/min_by: non-numeric block value (needs <=> dispatch)"
          | some ord =>
            -- replace only on a strict improvement (ties keep the earliest element).
            let newAcc := match kind, ord with
              | .maxBy, .gt => [cur, v]
              | .minBy, .lt => [cur, v]
              | _, _ => acc
            iterStep m cl brk rest kind newAcc retVal
        | _ => iterStep m cl brk rest kind acc retVal
    | .recvK mname args pblk implicit =>
      startArgs m v implicit mname [] args pblk
    | .argsK recv implicit mname acc rest pblk =>
      startArgs m recv implicit mname (acc ++ [v]) rest pblk
    | .argsSplatK recv implicit mname acc rest pblk =>
      match spreadA m v with
      | .ok (vs, m) => startArgs m recv implicit mname (acc ++ vs) rest pblk
      | .error e => .unsupported e
    | .blkCoerceK recv implicit mname acc kw =>
      match coerceToProc m v with
      | .ok (blkV, m) => invoke m recv implicit mname acc blkV kw
      | .error e => .unsupported e
    | .kwPairK key rest kwacc recv implicit mname posArgs pblk =>
      startKwargs m recv implicit mname posArgs (kwAdd kwacc (.sym key) v) rest pblk
    | .kwDynKeyK valE rest kwacc recv implicit mname posArgs pblk =>
      .next (withKont m (.eval valE) (.kwDynValK v rest kwacc recv implicit mname posArgs pblk))
    | .kwDynValK key rest kwacc recv implicit mname posArgs pblk =>
      startKwargs m recv implicit mname posArgs (kwAdd kwacc key v) rest pblk
    | .kwSplatK rest kwacc recv implicit mname posArgs pblk =>
      match v with
      | .ref o =>
        match (m.heap.get o).payload with
        | .hsh pairs =>
          let kwacc := pairs.foldl (fun acc (p : Value × Value) => kwAdd acc p.1 p.2) kwacc
          startKwargs m recv implicit mname posArgs kwacc rest pblk
        | _ => .unsupported "** of a non-Hash"
      | _ => .unsupported "** of a non-Hash"
    | .superArgK acc rest blk => startSuperArgs m (acc ++ [v]) rest blk
    | .superSplatK acc rest blk =>
      match spreadA m v with
      | .ok (vs, m) => startSuperArgs m (acc ++ vs) rest blk
      | .error e => .unsupported e
    | .yieldArgK acc rest => startYield m (acc ++ [v]) rest
    | .yieldSplatK acc rest =>
      match spreadA m v with
      | .ok (vs, m) => startYield m (acc ++ vs) rest
      | .error e => .unsupported e
    | .arrK acc rest => continueArray m (acc ++ [v]) rest
    | .arrSplatK acc rest =>
      match spreadA m v with
      | .ok (vs, m) => continueArray m (acc ++ vs) rest
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
      match kind with
      | .retK => doReturn m v
      | .brkK => .next (withCtl m (.jump (.brkJ v)))
      | .nxtK => .next (withCtl m (.jump (.nxtJ v)))
    | .optDefK name rest post body =>
      -- v is the default value for `name`; bind it, then the next default, or
      -- (all defaults done) install post/rest/block and run the body.
      let m := m.setLocal name v
      match rest with
      | [] =>
        let m := post.foldl (fun m (nv : String × Value) => m.setLocal nv.1 nv.2) m
        .next (withCtl m (.eval body))
      | (n0, d0) :: more => .next (withKont m (.eval d0) (.optDefK n0 more post body))
    | .frameK _ =>
      -- normal completion of a method body: pop the activation
      .next (withCtl { m with stack := m.stack.tail } (.value v))
    | .blkFrameK .. =>
      -- normal completion of a block body: pop the block frame
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
    | .catchK _ =>
      -- the catch block finished normally: its value is `catch`'s value
      .next (withCtl m (.value v))
    | .definedRecvK mname =>
      -- v is the evaluated receiver of `defined?(recv.m)`
      match definedMethod? m v mname .explicit with
      | some true => let (sv, m) := Builtins.allocStr m "method"; .next (withCtl m (.value sv))
      | some false => .next (withCtl m (.value .nil))
      | none => .unsupported s!"defined?(unmodeled method {mname})"
    | .definedCpathK name =>
      -- v is the evaluated base of `defined?(A::B)`; a non-namespace base is a
      -- TypeError in CRuby, so gate rather than answer nil.
      match v with
      | .ref o =>
        if (m.heap.classPayload? o).isSome then
          match constLookupFrom m.heap o name with
          | some _ => let (sv, m) := Builtins.allocStr m "constant"; .next (withCtl m (.value sv))
          | none => .next (withCtl m (.value .nil))
        else .unsupported "defined?(A::B) with a non-namespace base"
      | _ => .unsupported "defined?(A::B) with a non-namespace base"
    | .definedGuardK =>
      -- the operand evaluated without raising: pass its `defined?` answer on
      .next (withCtl m (.value v))
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
    | .retJ _ _ =>
      -- a non-lambda block `return` whose home method already exited [V]
      .next (raiseErr m Boot.localJumpErrorId "unexpected return")
    | .throwJ tag _ =>
      match Builtins.inspectP m tag with
      | .ok r => .next (raiseErr m Boot.uncaughtThrowErrorId s!"uncaught throw {r}")
      | .error e => .unsupported e
    | _ => .stuck "jump escaped the program (break/next/retry at toplevel)"
  | k :: rest =>
    let m := { m with kont := rest }
    match k with
    | .whileCondK c body | .whileBodyK c body =>
      match j with
      | .brkJ v => .next (withCtl m (.value v))
      | .nxtJ _ => .next (withKont m (.eval c) (.whileCondK c body))
      | .redoJ => .next (withKont m (.eval body) (.whileBodyK c body))  -- re-run body, skip cond [V]
      | _ => .next (withCtl m (.jump j))
    | .forStartK .. =>
      -- a jump raised while evaluating the collection is not the loop's: pass on
      .next (withCtl m (.jump j))
    | .forBodyK targets body rest coll =>
      match j with
      | .brkJ v => .next (withCtl m (.value v))           -- break value is for's value [V]
      | .nxtJ _ => forStep m targets body rest coll        -- next → next element
      | .redoJ =>                                          -- re-run body for the same element [V]
        .next (withKont m (.eval body) (.forBodyK targets body rest coll))
      | _ => .next (withCtl m (.jump j))
    | .frameK fid =>
      match j with
      | .retJ v target =>
        if target == fid then
          .next (withCtl { m with stack := m.stack.tail } (.value v))
        else  -- return targets an outer method: pop and keep unwinding
          .next (withCtl { m with stack := m.stack.tail } (.jump j))
      | .raiseJ _ | .throwJ .. => .next (withCtl { m with stack := m.stack.tail } (.jump j))
      | .brkJ _ | .nxtJ _ | .retryJ | .redoJ =>
        -- A **class/module body** is transparent to these: `3.times { class C;
        -- break; end }` breaks out of the `times` block [V] (test_flow_027/029).
        -- Crossing a *method* activation is not valid Ruby, so it still gates.
        if (m.frames.getD fid default).kind == .classBody then
          .next (withCtl { m with stack := m.stack.tail } (.jump j))
        else .unsupported "break/next/retry/redo crossing a method boundary"
    | .blkFrameK fid lam brk cl args =>
      match j with
      | .nxtJ v =>
        -- `next` ends this block invocation with value v (artifact 04 §4)
        .next (withCtl { m with stack := m.stack.tail } (.value v))
      | .brkJ v =>
        if lam then  -- `break` in a lambda returns from the lambda
          .next (withCtl { m with stack := m.stack.tail } (.value v))
        else match brk with
          | some t =>  -- return v from the method the block was passed to
            .next (withCtl { m with stack := m.stack.tail } (.jump (.retJ v t)))
          | none =>
            .next (raiseErr { m with stack := m.stack.tail }
              Boot.localJumpErrorId "break from proc-closure")
      | .retJ v target =>
        if lam && target == fid then  -- lambda's own return
          .next (withCtl { m with stack := m.stack.tail } (.value v))
        else  -- non-lambda return heads to its home method: pop and propagate
          .next (withCtl { m with stack := m.stack.tail } (.jump j))
      | .raiseJ _ | .throwJ .. => .next (withCtl { m with stack := m.stack.tail } (.jump j))
      | .retryJ => .unsupported "retry crossing a block boundary"
      | .redoJ =>
        -- `redo` re-runs *this* block invocation from the top with the same
        -- arguments (artifact 04, L69): pop the frame and re-enter the closure.
        callClosure { m with stack := m.stack.tail } cl args brk
    | .definedGuardK =>
      -- any exception while evaluating a `defined?` operand makes it nil [V]
      match j with
      | .raiseJ _ => .next (withCtl m (.value .nil))
      | _ => .next (withCtl m (.jump j))
    | .catchK tag =>
      match j with
      | .throwJ t v =>
        if t.identEq tag then .next (withCtl m (.value v))
        else .next (withCtl m (.jump j))
      | _ => .next (withCtl m (.jump j))
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

/-- The `NameError` `undef`/`alias` raise when the target method is not defined
    on the current definee (artifact 02). CRuby names the definee `class 'C'` /
    `module 'M'`; an eigenclass definee has an address-dependent name we cannot
    reproduce byte-exactly → gate. A method CRuby *does* define on the chain but
    the model doesn't (`Kernel#binding`, …) gates Unsupported rather than raising
    a spurious `NameError` — the same fidelity split dispatch uses. -/
def undefAliasMiss (m : Machine) (name : String) : StepResult :=
  match crubyShadow m.heap (ancestors m.heap m.currentFrame.defmod) name with
  | some cname => .unsupported s!"undef/alias of unmodeled method {cname}#{name}"
  | none =>
  match m.heap.classPayload? m.currentFrame.defmod with
  | some c =>
    if c.name.startsWith "#<" then
      .unsupported "undef/alias of a missing method in a singleton class"
    else
      let kind := if c.isModule then "module" else "class"
      .next (raiseErr m Boot.nameErrorId
        s!"undefined method '{name}' for {kind} '{c.name}'")
  | none => .unsupported "undef/alias outside a class/module body"

/-- `undef n₁, n₂, …` (artifact 02): install a tombstone per name on the current
    definee, left to right. Each name must currently resolve (including
    inherited, excluding an existing tombstone) else `NameError` [V]. -/
def undefNames (m : Machine) (defmod : ObjId) : List String → StepResult
  | [] => .next (withCtl m (.value .nil))  -- `undef` evaluates to nil [V]
  | n :: rest =>
    match methodOn m.heap defmod n with
    | some (_, md) =>
      if md.undefined then undefAliasMiss m n
      else undefNames { m with heap := undefMethod m.heap defmod n } defmod rest
    | none => undefAliasMiss m n

end Interp

end RubyCore
