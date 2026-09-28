import RubyCore.Interp.BlockPass
import RubyCore.Interp.Frozen

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
    | .requireK feature _ =>
      .next { m with ctl := .value (.bool true), stack := m.stack.tail, loadingFeatures := m.loadingFeatures.filter (· != feature), loadedFeatures := feature :: m.loadedFeatures }
    | .objectInspectK recv filter remaining text source =>
      resumeObjectInspect m recv filter remaining text source v
    | .enumFinishK o => finishEnumerator m o v
    | .enumStopK owner exc result => finishStop m owner exc result
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
            raiseFrozen m (.ref o)
          else .next (withCtl (bindIvar m x v) (.value v))
        | selfV =>
          -- immediates are frozen: @x= with Integer self → FrozenError [V]
          raiseFrozen m selfV
      | .cvar =>
        match cvarScope m with
        | none => .next (raiseErr m Boot.runtimeErrorId "class variable access from toplevel")
        | some scope =>
          .next (withCtl { m with heap := cvarSetIn m.heap scope x v } (.value v))
    | .casgnK n =>
      assignConstant m m.lexicalNamespace n v
    | .classDefK name body =>
      match inheritableClass m v false with
      | .error result => result
      | .ok k => enterClassBody m name false (some k) body
    | .constClassK klass superclass libraryName body =>
      inheritClassBody m klass superclass libraryName body
    | .classBodyK klass libraryName body => pushClassFrame m klass libraryName body
    | .classInitK klass block => finishClassInitialize m klass block
    | .classNameErrorK klass lead tail => finishClassNameError m klass lead tail v
    | .newK inst =>
      -- `initialize` returned; its value is discarded, `new` yields the instance
      .next (withCtl m (.value inst))
    | .raiseValueK =>
      if isA m.heap v Boot.exceptionId then .next (withCtl m (.jump (.raiseJ v)))
      else .next (raiseErr m Boot.typeErrorId "exception object expected")
    | .exceptionCopyK copy message original =>
      let freeze := match original with | .ref o => (m.heap.get o).frozen | _ => true
      let m := if freeze then match copy with
        | .ref o => { m with heap := m.heap.set o { m.heap.get o with frozen := true } }
        | _ => m
        else m
      constructResult (Builtins.run "Exception#initialize" copy [message] m)
    | .blockCallK _ => .next (withCtl m (.value v))
    | .arrayInitK recv block index size => arrayInitNext m recv block index size v
    | .methodEditsK remaining result => runMethodEdits m remaining result
    | .methodAddedK name =>
      -- the `method_added` hook returned; its value is discarded and `def`
      -- yields the method name, as if the hook had not run
      .next (withCtl m (.value (.sym name)))
    | .uncaughtInspectK source => finishUncaughtInspect m source v
    | .raiseNewK inst =>
      -- Native error initialize returned; discard its result and raise the instance.
      .next (withCtl m (.jump (.raiseJ inst)))
    | .includeK recv =>
      -- `included` hook returned; its value is discarded, `include` yields recv
      .next (withCtl m (.value recv))
    | .defsK name params body =>
      -- `def RECV.name`: install on RECV's eigenclass (v = the evaluated RECV)
      match v with
      | .ref o =>
        if (m.heap.get o).frozen then raiseFrozen m v else
        let (e, m) := eigenclassOf m o
        if let some receiver := frozenMethodReceiver? m.heap e then raiseFrozen m receiver else
        -- `def self.m` in a module keeps that module's lexical cref for constant
        -- lookup even though its dispatch owner is the eigenclass (artifact 03).
        let md : MethodDef :=
          { params, body, owner := e, definee := some m.currentFrame.defmod, cref := m.currentFrame.cref,
            fromPrelude := m.preludeMode || m.currentFrame.libraryOrigin }
        runMethodEdits m [.define e name md] (.sym name)
      | _ =>
        -- singleton def on an immediate (`def 1.m`) — TypeError; message-gate
        .unsupported "singleton def on an immediate"
    | .sclassK body =>
      -- `class << OBJ`: run body with self/cref = OBJ's eigenclass
      match v with
      | .ref o =>
        let (e, m) := eigenclassOf m o
        let frame : Frame := { self := .ref e, defmod := e, kind := .classBody, cref := e :: m.currentFrame.cref, libraryOrigin := m.currentFrame.libraryOrigin }
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
        let isPrivate := isPrivateConst m.heap o name
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
          else if unmodeledNamespaceConstant m o name then
            .unsupported s!"unmodeled constant {className m.heap o}::{name}"
          else .next (raiseErr m Boot.nameErrorId
            s!"uninitialized constant {className m.heap o}::{name}")
    | .cpathAsgnK name rhs =>
      -- v is base `A`; evaluate `rhs`, then assign (base then rhs order [V]).
      match cpathContainer m v with
      | .error sr => sr
      | .ok o => .next (withKont m (.eval rhs) (.cpathAsgnValK name o))
    | .cpathAsgnValK name base =>
      assignConstant m base name v
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
    | .forStartK targets body multiple => startFor m targets body multiple v
    | .forAssignK pending body => .next (queueForAssignments m pending body)
    | .iterK cl brk rest kind acc retVal cur =>
      -- v is the block's result for the current element; fold it, then continue.
      match kind with
      | .ignore | .arrayEach .. | .arrayIndex .. | .hashEach .. | .times .. | .scan .. => iterStep m cl brk rest kind acc retVal
      | .arrayMap .. => iterStep m cl brk rest kind (acc ++ [v]) retVal
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
      startSplat m (.args recv implicit mname acc rest pblk) v
    | .blkCoerceK recv implicit mname acc kw =>
      coerceBlockPass m ⟨recv, implicit, mname, acc, kw⟩ v
    | .blkConvertK call source phase =>
      resumeBlockPass m call source phase v
    | .frozenErrorK recv phase => resumeFrozen m recv phase v
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
      startSplat m (.superArgs acc rest blk) v
    | .yieldArgK acc rest => startYield m (acc ++ [v]) rest
    | .yieldSplatK acc rest =>
      startSplat m (.yieldArgs acc rest) v
    | .arrK acc rest => continueArray m (acc ++ [v]) rest
    | .arrSplatK acc rest =>
      startSplat m (.array acc rest) v
    | .hshKeyK acc vExpr rest =>
      .next (withKont m (.eval vExpr) (.hshValK acc v rest))
    | .hshValK acc key rest =>
      if Builtins.complexEqualityImpure m.heap 100 key ||
          acc.any (fun (k, _) => Builtins.complexEqualityImpure m.heap 100 k) then
        .unsupported "Hash literal with effectful Complex key comparison" else
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
    | .paramBindK pending body => stepParamBinding m pending body
    | .optDefK name rest post body =>
      -- v is the default value for `name`; bind it, then the next default, or
      -- (all defaults done) install post/rest/block and run the body.
      let m := m.setLocal name v
      match rest with
      | [] =>
        let m := post.foldl (fun m (nv : String × Value) => m.setLocal nv.1 nv.2) m
        .next (withCtl m (.eval body))
      | (n0, d0) :: more => .next (withKont m (.eval d0) (.optDefK n0 more post body))
    | .frameK _ | .dmFrameK .. =>
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
          | none => if unmodeledNamespaceConstant m o name then
              .unsupported s!"defined? of unmodeled constant {className m.heap o}::{name}"
            else .next (withCtl m (.value .nil))
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
    | .throwJ tag value => .next (raiseUncaughtThrow m tag value)
    | _ => .stuck "jump escaped the program (break/next/retry at toplevel)"
  | k :: rest =>
    let m := { m with kont := rest }
    match k with
    | .blockCallK scope =>
      match j with
      | .retJ v target =>
        if target == scope then .next (withCtl m (.value v))
        else .next (withCtl m (.jump j))
      | _ => .next (withCtl m (.jump j))
    | .requireK feature fid =>
      let m := { m with stack := m.stack.tail, loadingFeatures := m.loadingFeatures.filter (· != feature) }
      match j with
      | .retJ _ target =>
        if target == fid then .next { m with ctl := .value (.bool true), loadedFeatures := feature :: m.loadedFeatures }
        else .next { m with ctl := .jump j }
      | _ => .next { m with ctl := .jump j }
    | .enumFinishK o =>
      let st := enumState m o
      match st.caller with
      | none => .stuck "Enumerator unwind without caller"
      | some caller =>
        let m := restoreExecution (setEnumState m o {}) caller
        match j with
        | .raiseJ _ => .next { m with ctl := .jump j }
        | .retJ .. => .next (raiseErr m Boot.localJumpErrorId "unexpected return")
        | .throwJ tag value => .next (raiseUncaughtThrow m tag value)
        | _ => .unsupported "nonlocal transfer out of Enumerator"
    | .whileCondK c body | .whileBodyK c body =>
      match j with
      | .brkJ v => .next (withCtl m (.value v))
      | .nxtJ _ => .next (withKont m (.eval c) (.whileCondK c body))
      | .redoJ => .next (withKont m (.eval body) (.whileBodyK c body))  -- re-run body, skip cond [V]
      | _ => .next (withCtl m (.jump j))
    | .forStartK .. =>
      -- a jump raised while evaluating the collection is not the loop's: pass on
      .next (withCtl m (.jump j))
    | .dmFrameK fid body =>
      match j with
      | .brkJ v | .nxtJ v => .next (withCtl { m with stack := m.stack.tail } (.value v))
      | .redoJ => .next (withKont m (.eval body) (.dmFrameK fid body))
      | .retJ v target =>
        if target == fid then .next (withCtl { m with stack := m.stack.tail } (.value v))
        else .next (withCtl { m with stack := m.stack.tail } (.jump j))
      | .raiseJ _ | .throwJ .. => .next (withCtl { m with stack := m.stack.tail } (.jump j))
      | .retryJ => .unsupported "retry crossing a define_method boundary"
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
        -- Redo restarts the body in the same activation. Parameter/local writes
        -- remain visible, and argument conversion/defaults must not run again.
        .next (withKont m (.eval cl.body) (.blkFrameK fid lam brk cl args))
    | .blkConvertK call source phase =>
      unwindBlockPass m call source phase j
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
