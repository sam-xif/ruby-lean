import RubyCore.Judgment.Frag

/-!
# `Census` — the Judge-side fragment census (J4 groundwork)

**Report-only, untrusted.** `--census-j` walks a program and reports, per method
body (and per class body / toplevel), every node the machine-typed fragment
(`MFrag`, `Frag.lean`) refuses — with the fact the J31 claim route turns on:
whether the node sits in **statement position** (a direct `seq` element), which is
the only position a semantic claim can occupy, and whether its head is
`fragHead`-false, which is the only head shape a claim may have. A node with both
is *claimable* — admissible today via a `SemClaim` whose `EvalOkAt` obligation is
then the (real) remaining bill. A node with neither needs an `MFrag`/preservation
rung before any certificate can cover it.

The walk **mirrors** `mfragBody`'s shape tests rather than calling them (it needs
to say *why* a node is out, not just that it is), so it carries the same drift
risk as `homebrew/fragment-gap.py`'s `SUPPORTED` list. The guard is the
`mfragOk` cross-check emitted per body: for bodies containing no nested
definition, `entries = []` must coincide with `mfragB [] body`; a divergence is
reported as `drift = true` and means this file's mirror is stale.
-/

namespace RubyCore.Judgment

open RubyCore

/-- One out-of-fragment node, located. -/
structure CensusEntry where
  owner : String
  /-- Why the node is out (a label, not just the constructor). -/
  head : String
  /-- Statement position: a direct element of a `seq` (or the program root). -/
  stmt : Bool
  /-- `stmt` ∧ `fragHead = false` — admissible via a `SemClaim` today. -/
  claimable : Bool
  /-- Inside a claimable ancestor's subtree: if that ancestor is claimed, this
      node never meets the checker (the claim's Lean obligation absorbs it), so
      it does not count toward the *effective* blocker set. -/
  shadowed : Bool
deriving Repr

namespace Census

/-- Marker-argument scan: `splat`/`kwargs`/`blockpass`/`fwd` in an argument list
    make the *containing* send out-of-fragment while its own head stays
    `fragHead`-true (markers are counted in the syntactic universe), so the send
    is unclaimable — the label records which marker. -/
private def markerLabel : Expr → Option String
  | .splat _ => some "splat-arg"
  | .kwargs _ => some "kwargs-arg"
  | .blockpass _ => some "blockpass-arg"
  | .fwd => some "fwd-arg"
  | _ => none

private def mkEntry (owner head : String) (stmt sh : Bool) (e : Expr) : CensusEntry :=
  { owner, head, stmt, claimable := stmt && !fragHead e, shadowed := sh }

/-- Is this node claimable (statement position, `fragHead`-false)? Children of a
    claimable node are walked `shadowed`. -/
private def clm (stmt : Bool) (e : Expr) : Bool := stmt && !fragHead e

mutual

/-- The walk. `owner` is the enclosing body's label; `stmt` is true exactly when
    `e` is a direct `seq` element (or the program root). Children of every head
    other than `seq` are non-statement positions — mirroring where `MFrag`
    demands `fragHead = true` of subterms. -/
partial def walk (owner : String) (cls : Option String) (stmt sh : Bool)
    (e0 : Expr) : List CensusEntry :=
  -- Children of a claimable node are shadowed: if the node is claimed, the
  -- checker never descends into it.
  let sh2 := sh || clm stmt e0
  match e0 with
  | .int _ | .flt _ | .str _ | .sym _ | .tru | .fls | .nil => []
  | .self' | .vcall _ | .const _ => []
  | .var .lvar _ | .var .ivar _ | .var .gvar _ => []
  | e@(.var .cvar _) => [mkEntry owner "cvar-read" stmt sh e]
  | .vasgn .lvar _ rhs | .vasgn .ivar _ rhs | .vasgn .gvar _ rhs =>
    walk owner cls false sh2 rhs
  | e@(.vasgn .cvar _ rhs) =>
    mkEntry owner "cvar-asgn" stmt sh e :: walk owner cls false sh2 rhs
  | .seq es => es.flatMap (walk owner cls true sh)
  | .if' c t els =>
    walk owner cls false sh2 c ++ walk owner cls false sh2 t ++
      (match els with | some e' => walk owner cls false sh2 e' | none => [])
  | .while' c b => walk owner cls false sh2 c ++ walk owner cls false sh2 b
  | e@(.send r mname args blk) =>
    let sub := (match r with | some re => walk owner cls false sh2 re | none => []) ++
      args.flatMap (walk owner cls false sh2) ++
      (match blk with
       | some (.block _ _ body) => walk (owner ++ "{blk}") cls false sh2 body
       | some (.blockpass (some pe)) => walk owner cls false sh2 pe
       | _ => [])
    let markers := (args.filterMap markerLabel).eraseDups
    if blk.isSome then mkEntry owner "send-block" stmt sh e :: sub
    else if mname = "call" && r.isSome then
      mkEntry owner "send-call" stmt sh e :: sub
    else if !markers.isEmpty then
      markers.map (fun l => mkEntry owner s!"send-{l}" stmt sh e) ++ sub
    else sub
  | .def' name _ body =>
    let owner' := (match cls with | some c => c | none => "Object") ++ "#" ++ name
    walk owner' cls false sh2 body
  | e@(.defs _ name _ body) =>
    let owner' := (match cls with | some c => c | none => "Object") ++ "." ++ name
    mkEntry owner "defs" stmt sh e :: walk owner' cls false sh2 body
  | .class' name none body =>
    walk s!"(class {name})" (some name) false sh2 body
  | e@(.class' name (some sup) body) =>
    mkEntry owner "class-superclass" stmt sh e ::
      (walk owner cls false sh2 sup ++ walk s!"(class {name})" (some name) false sh2 body)
  | e@(.module' name body) =>
    mkEntry owner "module" stmt sh e :: walk s!"(module {name})" (some name) false sh2 body
  | e@(.scopedClass _ name body) =>
    mkEntry owner "scoped-class" stmt sh e ::
      walk s!"(class {name})" (some name) false sh2 body
  | e@(.scopedModule _ name body) =>
    mkEntry owner "scoped-module" stmt sh e ::
      walk s!"(module {name})" (some name) false sh2 body
  | e@(.sclass _ body) =>
    mkEntry owner "sclass" stmt sh e :: walk owner cls false sh2 body
  | e@(.array es) =>
    let markers := (es.filterMap markerLabel).eraseDups
    markers.map (fun l => mkEntry owner s!"array-{l}" stmt sh e) ++
      es.flatMap (walk owner cls false sh2)
  | e@(.hash prs) =>
    mkEntry owner "hash" stmt sh e ::
      prs.flatMap (fun (k, v) => walk owner cls false sh2 k ++ walk owner cls false sh2 v)
  | e@(.casgn _ rhs) => mkEntry owner "casgn" stmt sh e :: walk owner cls false sh2 rhs
  -- J38: cpath is in the fragment; only its base is walked.
  | .cpath none _ => []
  | .cpath (some b) _ => walk owner cls false sh2 b
  | e@(.cpathAsgn _ _ rhs) =>
    mkEntry owner "cpath-asgn" stmt sh e :: walk owner cls false sh2 rhs
  | e@(.yield' args) =>
    mkEntry owner "yield" stmt sh e :: args.flatMap (walk owner cls false sh2)
  | e@(.dowhile b c) =>
    mkEntry owner "dowhile" stmt sh e :: (walk owner cls false sh2 b ++ walk owner cls false sh2 c)
  | e@(.for' _ c b) =>
    mkEntry owner "for" stmt sh e :: (walk owner cls false sh2 c ++ walk owner cls false sh2 b)
  -- J39: `return` is in the fragment; only the operand is walked.
  | .ret o =>
    (match o with | some e' => walk owner cls false sh2 e' | none => [])
  | e@(.brk o) =>
    mkEntry owner "break" stmt sh e ::
      (match o with | some e' => walk owner cls false sh2 e' | none => [])
  | e@(.nxt o) =>
    mkEntry owner "next" stmt sh e ::
      (match o with | some e' => walk owner cls false sh2 e' | none => [])
  | e@(.retry') => [mkEntry owner "retry" stmt sh e]
  | e@(.redo') => [mkEntry owner "redo" stmt sh e]
  | e@(.begin' body rescues els ens) =>
    mkEntry owner "begin" stmt sh e ::
      (walk owner cls false sh2 body ++
       rescues.flatMap (fun (excs, _, h) =>
         excs.flatMap (walk owner cls false sh2) ++ walk owner cls false sh2 h) ++
       (match els with | some e' => walk owner cls false sh2 e' | none => []) ++
       (match ens with | some e' => walk owner cls false sh2 e' | none => []))
  | e@(.super' args blk) =>
    mkEntry owner "super" stmt sh e :: (args.flatMap (walk owner cls false sh2) ++
      (match blk with
       | some (.block _ _ body) => walk (owner ++ "{blk}") cls false sh2 body
       | _ => []))
  | e@(.zsuper _) => [mkEntry owner "zsuper" stmt sh e]
  | e@(.undef _) => [mkEntry owner "undef" stmt sh e]
  | e@(.alias' _ _) => [mkEntry owner "alias" stmt sh e]
  | e@(.defined _) => [mkEntry owner "defined" stmt sh e]
  -- Marker shapes reached in evaluable position (should not occur in exporter
  -- output; recorded rather than dropped).
  | e@(.splat _) => [mkEntry owner "splat" stmt sh e]
  | e@(.kwargs _) => [mkEntry owner "kwargs" stmt sh e]
  | e@(.block _ _ body) => mkEntry owner "block" stmt sh e :: walk owner cls false sh2 body
  | e@(.blockpass _) => [mkEntry owner "blockpass" stmt sh e]
  | e@(.fwd) => [mkEntry owner "fwd" stmt sh e]

end

/-- Collect the `def`/`defs` bodies for the per-body `mfragB` cross-check:
    `(owner, body, hasNestedDef)`. -/
partial def bodies (cls : Option String) : Expr → List (String × Expr)
  | .def' name _ body =>
    let owner := (match cls with | some c => c | none => "Object") ++ "#" ++ name
    (owner, body) :: bodies cls body
  | .defs _ name _ body =>
    let owner := (match cls with | some c => c | none => "Object") ++ "." ++ name
    (owner, body) :: bodies cls body
  | .class' name _ body | .module' name body
  | .scopedClass _ name body | .scopedModule _ name body =>
    bodies (some name) body
  | .sclass _ body => bodies cls body
  | .seq es => es.flatMap (bodies cls)
  | .if' c t els =>
    bodies cls c ++ bodies cls t ++
      (match els with | some e => bodies cls e | none => [])
  | .while' c b | .dowhile c b => bodies cls c ++ bodies cls b
  | .vasgn _ _ rhs | .casgn _ rhs | .cpathAsgn _ _ rhs => bodies cls rhs
  | .send r _ args blk =>
    (match r with | some re => bodies cls re | none => []) ++
      args.flatMap (bodies cls) ++
      (match blk with | some b => bodies cls b | none => [])
  | .block _ _ body => bodies cls body
  | .begin' body rescues els ens =>
    bodies cls body ++
      rescues.flatMap (fun (_, _, h) => bodies cls h) ++
      (match els with | some e => bodies cls e | none => []) ++
      (match ens with | some e => bodies cls e | none => [])
  | .array es => es.flatMap (bodies cls)
  | .hash prs => prs.flatMap (fun (k, v) => bodies cls k ++ bodies cls v)
  | .ret (some e) | .brk (some e) | .nxt (some e) | .splat (some e) => bodies cls e
  | .yield' args | .super' args _ => args.flatMap (bodies cls)
  | .for' _ c b => bodies cls c ++ bodies cls b
  | .defined e => bodies cls e
  | _ => []

/-- Does the expression contain a nested `def`/`defs`? (Used to scope the
    cross-check: `walk` attributes a nested def's entries to the nested owner,
    so the outer body's entry list is not comparable to its own `mfragB`.) -/
partial def hasDef : Expr → Bool
  | .def' _ _ _ | .defs _ _ _ _ => true
  | .class' _ _ body | .module' _ body | .scopedClass _ _ body
  | .scopedModule _ _ body | .sclass _ body | .block _ _ body => hasDef body
  | .seq es => es.any hasDef
  | .if' c t els =>
    hasDef c || hasDef t || (match els with | some e => hasDef e | none => false)
  | .while' c b | .dowhile c b => hasDef c || hasDef b
  | .vasgn _ _ rhs | .casgn _ rhs | .cpathAsgn _ _ rhs => hasDef rhs
  | .send r _ args blk =>
    (match r with | some re => hasDef re | none => false) ||
      args.any hasDef || (match blk with | some b => hasDef b | none => false)
  | .begin' body rescues els ens =>
    hasDef body || rescues.any (fun (_, _, h) => hasDef h) ||
      (match els with | some e => hasDef e | none => false) ||
      (match ens with | some e => hasDef e | none => false)
  | .array es => es.any hasDef
  | .hash prs => prs.any (fun (k, v) => hasDef k || hasDef v)
  | .ret (some e) | .brk (some e) | .nxt (some e) | .splat (some e) => hasDef e
  | .yield' args | .super' args _ => args.any hasDef
  | .for' _ c b => hasDef c || hasDef b
  | .defined e => hasDef e
  | _ => false

end Census

/-- The census report as JSON. Entries are grouped per owner; each `def` body
    additionally carries the `mfragB` cross-check (`drift = true` flags a
    divergence between this file's mirror and the real gate — see the module
    docstring). -/
def censusJ (prog : Expr) : Lean.Json :=
  let entries := Census.walk "(top)" none true false prog
  -- Group by owner, preserving first-appearance order.
  let owners := (entries.map (·.owner)).eraseDups
  let defBodies := Census.bodies none prog
  let entryJson := fun (e : CensusEntry) =>
    Lean.Json.mkObj [("head", Lean.Json.str e.head),
                     ("stmt", Lean.Json.bool e.stmt),
                     ("claimable", Lean.Json.bool e.claimable),
                     ("shadowed", Lean.Json.bool e.shadowed)]
  let ownerJson := owners.map (fun o =>
    let es := entries.filter (·.owner = o)
    Lean.Json.mkObj [
      ("owner", Lean.Json.str o),
      ("blocked", Lean.Json.num es.length),
      ("claimable", Lean.Json.num (es.filter (·.claimable)).length),
      ("effective", Lean.Json.num (es.filter (fun x => !x.shadowed)).length),
      ("entries", Lean.Json.arr (es.map entryJson).toArray)])
  let bodyJson := defBodies.map (fun (o, b) =>
    let es := entries.filter (·.owner = o)
    let mfragOk := mfragB [] 1000000 b
    let comparable := !Census.hasDef b
    Lean.Json.mkObj [
      ("owner", Lean.Json.str o),
      ("clean", Lean.Json.bool es.isEmpty),
      ("claimableOnly", Lean.Json.bool
        (es.all (fun x => x.claimable || x.shadowed) && !es.isEmpty)),
      ("mfragOk", Lean.Json.bool mfragOk),
      ("drift", Lean.Json.bool (comparable && (es.isEmpty != mfragOk)))])
  let heads := (entries.map (·.head)).eraseDups
  let summary := heads.map (fun h =>
    let es := entries.filter (·.head = h)
    (h, Lean.Json.mkObj [
      ("total", Lean.Json.num es.length),
      ("claimable", Lean.Json.num (es.filter (·.claimable)).length),
      ("effective", Lean.Json.num (es.filter (fun x => !x.shadowed)).length),
      ("effectiveUnclaimable", Lean.Json.num
        (es.filter (fun x => !x.shadowed && !x.claimable)).length)]))
  let nClean := (defBodies.filter (fun (o, _) =>
    (entries.filter (·.owner = o)).isEmpty)).length
  let nClaimableOnly := (defBodies.filter (fun (o, _) =>
    let es := entries.filter (·.owner = o)
    !es.isEmpty && es.all (fun x => x.claimable || x.shadowed))).length
  Lean.Json.mkObj [
    ("bodies_total", Lean.Json.num defBodies.length),
    ("bodies_clean", Lean.Json.num nClean),
    ("bodies_claimable_only", Lean.Json.num nClaimableOnly),
    ("blocked_total", Lean.Json.num entries.length),
    ("blocked_effective", Lean.Json.num
      (entries.filter (fun x => !x.shadowed)).length),
    ("summary", Lean.Json.mkObj summary),
    ("bodies", Lean.Json.arr bodyJson.toArray),
    ("owners", Lean.Json.arr ownerJson.toArray)]

end RubyCore.Judgment
