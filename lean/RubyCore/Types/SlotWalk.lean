import RubyCore.Types.SlotClaim

/-!
# §5 step 2 — the install walk

`docs/semantics/slot-frame.md` §5: the conflict check is decidable *because* the
world is closed (SF6), and this file is what closes it — the syntactic
enumeration of every table-mutating site in the linked program.

Three honest properties, in the design's own order:

* **Soundness is never at stake.** A site the walk cannot read syntactically
  emits `InstallN.opaque_`, which makes the *program* rejectable. Same polarity
  as every other gate in the pipeline.
* **Completeness is lost exactly at laundering** (SF6a): `define_method(argv[0])`
  keeps the site enumerable and forces its key set to ⊤ at the name coordinate
  (`InstallN.anyName`), which conflicts with every reader at that class. That
  loss is a feature — a rejection there flags metaprogramming driven by
  unvalidated input.
* **A computed dispatch is not a write** and is invisible here (`obj.send(name)`
  emits nothing). It is untypable for the ordinary no-`Row`-for-an-unknown-name
  reason, not for a frame reason.

The walk is **name-keyed** (`InstallN`) because a static text names classes, and
`SlotClaim` is id-keyed because a slot is a heap cell. `InstallN.resolve` is the
bridge, and it is deliberately a *partial* function supplied by the caller: an
install at a class name the resolver does not know is a rejection, not a silent
drop.
-/

namespace RubyCore.Types

open RubyCore

/-- A table-mutating site, keyed by class *name* (SF8's rows, syntactically). -/
inductive InstallN where
  | defM (cls name : String)
  | ancestry (cls : String)
  /-- SF6a — the name coordinate is data. -/
  | anyName (cls : String)
  /-- The walk cannot see this site (`eval`, a singleton class, a `*_eval`
      block). Not a claim that it is dangerous — a claim that the closed world
      does not hold here, so the frame declines and the case exits to the `wp`
      door (§8). -/
  | opaque_ (why : String)
deriving Repr, DecidableEq, Inhabited

namespace InstallN

/-- Names the walk treats as ancestry mutations wherever they appear as a send. -/
def ancestryNames : List String := ["include", "prepend", "extend"]

/-- Sends whose *body* re-opens a definee the walk cannot follow. -/
def opaqueNames : List String :=
  ["eval", "class_eval", "module_eval", "instance_eval", "class_exec",
   "module_exec", "instance_exec", "define_singleton_method"]

/-- The class a send targets: an explicit constant receiver, else the definee. -/
def sendTarget (definee : String) (recv : Option Expr) : Option String :=
  match recv with
  | none => some definee
  | some (.self') => some definee
  | some (.const n) => some n
  | some (.cpath _ n) => some n
  | some _ => none

end InstallN

/-- The walk. `definee` is the class body we are lexically inside — `"Object"` at
    toplevel, exactly as a `def` there installs on `Object`. Fuel-bounded for
    totality — **and not `partial`**: a `partial def` is opaque to the kernel, and
    SF-T3's adequacy theorem (a derivation's install-set misses a claim's
    footprint) has to reason about this walk. Any fuel at least the program's
    depth works; running out emits `opaque_`, i.e. rejects, rather than silently
    returning `[]`. -/
def installsGo : Nat → String → Expr → List InstallN
  | 0, _, _ => [.opaque_ "fuel exhausted"]
  | fuel + 1, definee, e =>
  let installsGo (d : String) (x : Expr) := installsGo fuel d x
  let kids (es : List Expr) := es.flatMap (installsGo definee)
  let optK (o : Option Expr) := match o with | some x => installsGo definee x | none => []
  match e with
  -- ## The writes
  | .def' name _ _ => [.defM definee name]
  | .undef names => names.map (fun n => InstallN.defM definee n)
  | .alias' newName _ => [.defM definee newName]
  -- A singleton write. Our heap has no eigenclass, so the walk cannot say which
  -- slot this is; it declines rather than guess (§5's honest cost).
  | .defs _ name _ _ => [.opaque_ s!"defs {name}"]
  | .sclass _ _ => [.opaque_ "class << self"]
  | .send recv m args blk =>
    let base := optK recv ++ kids args ++ optK blk
    let tgt := InstallN.sendTarget definee recv
    let at? (f : String → InstallN) : List InstallN :=
      match tgt with | some t => [f t] | none => [.opaque_ s!"receiver of {m}"]
    if InstallN.ancestryNames.contains m then
      at? (fun t => .ancestry t) ++ base
    else if InstallN.opaqueNames.contains m then
      [.opaque_ m] ++ base
    else if m == "define_method" || m == "remove_method" || m == "undef_method" then
      (match args.head? with
       | some (.sym s) => at? (fun t => .defM t s)
       | _ => at? (fun t => .anyName t)) ++ base
    else if m == "alias_method" then
      (match args.head? with
       | some (.sym s) => at? (fun t => .defM t s)
       | _ => at? (fun t => .anyName t)) ++ base
    else if m == "attr_reader" || m == "attr_writer" || m == "attr_accessor" then
      (args.flatMap fun a =>
        match a, tgt with
        | .sym s, some t =>
          (if m == "attr_reader" then [InstallN.defM t s]
           else if m == "attr_writer" then [InstallN.defM t (s ++ "=")]
           else [InstallN.defM t s, InstallN.defM t (s ++ "=")])
        | _, some t => [InstallN.anyName t]
        | _, none => [InstallN.opaque_ m]) ++ base
    else base
  -- ## The definee-changing heads
  | .class' name _ body => installsGo name body
  | .module' name body => installsGo name body
  | .scopedClass _ name body => installsGo name body
  | .scopedModule _ name body => installsGo name body
  -- ## Everything else: the children
  | .vasgn _ _ x => installsGo definee x
  | .casgn _ x => installsGo definee x
  | .cpath base _ => optK base
  | .cpathAsgn base _ x => optK base ++ installsGo definee x
  | .kwargs entries => entries.flatMap fun kv =>
      match kv with
      | .pair _ v => installsGo definee v
      | .dyn k v => installsGo definee k ++ installsGo definee v
      | .splat x => installsGo definee x
  | .block _ _ body => installsGo definee body
  | .yield' args => kids args
  | .blockpass x => optK x
  | .if' c t els => installsGo definee c ++ installsGo definee t ++ optK els
  | .while' c body => installsGo definee c ++ installsGo definee body
  | .dowhile body c => installsGo definee body ++ installsGo definee c
  | .for' _ coll body => installsGo definee coll ++ installsGo definee body
  | .array elems => kids elems
  | .hash pairs => pairs.flatMap (fun p => installsGo definee p.1 ++ installsGo definee p.2)
  | .splat x => optK x
  | .ret x => optK x
  | .brk x => optK x
  | .nxt x => optK x
  | .begin' body rescues els ens =>
    installsGo definee body
    ++ rescues.flatMap (fun r => kids r.1 ++ installsGo definee r.2.2)
    ++ optK els ++ optK ens
  | .super' args blk => kids args ++ optK blk
  | .zsuper blk => optK blk
  | .defined x => installsGo definee x
  | .seq es => kids es
  | _ => []

/-- §5 step 2 — the program's install inventory. Toplevel definee is `Object`. -/
def installsOf (p : Expr) (fuel : Nat) : List InstallN := installsGo fuel "Object" p

/-- The name→id bridge. Partial on purpose: an install at a class the resolver
    cannot name is a rejection. -/
def InstallN.resolve (f : String → Option ObjId) : InstallN → Option Install
  | .defM cls name => (f cls).map (fun k => .defM k name)
  | .ancestry cls => (f cls).map (fun k => .ancestry k)
  | .anyName cls => (f cls).map Install.anyName
  | .opaque_ _ => none

/-- Is the claim trivial? The unit of the PCM reads nothing, so *every* write
    frames it — including a write the walk could not read. -/
def SlotClaim.isTrivial (c : SlotClaim) : Bool :=
  c.defined.isEmpty && c.empty.isEmpty && c.spines.isEmpty && c.noMM.isEmpty

/-- One site against one footprint. The two unreadable cases — an `opaque_` site
    and a class name the resolver cannot place — collapse to the same verdict,
    and it is the conservative one: an unknown write might be *any* write, so
    only the trivial claim survives it. That is what keeps the default
    (no footprint claimed) certificate unaffected by this check while making a
    real claim pay for every site the walk cannot read. -/
def InstallN.framedBy (c : SlotClaim) (f : String → Option ObjId) : InstallN → Bool
  | .opaque_ _ => SlotClaim.isTrivial c
  | i =>
    match i.resolve f with
    | some inst => !inst.conflicts c
    | none => SlotClaim.isTrivial c

/-- §5 step 3, over a program: **every enumerated install misses the footprint**. -/
def framedProgB (c : SlotClaim) (f : String → Option ObjId) (p : Expr) (fuel : Nat) : Bool :=
  (installsOf p fuel).all (InstallN.framedBy c f)

/-! ## The wire shape: claims are written in names

A certificate is a static text and names classes; a slot is a heap cell and is
an id. `SlotClaimN` is the name-keyed surface, `resolve` the bridge, and the
bridge is total-or-nothing: a footprint mentioning a class the resolver cannot
place is a rejected certificate, never a silently shrunk one.
-/

/-- SF5's footprint, keyed by class name — the JSON-facing shape. -/
structure SlotClaimN where
  defined : List (String × String × MethodDecl) := []
  empty : List (String × String) := []
  spines : List (String × List String) := []
  noMM : List String := []
deriving Repr, Inhabited, DecidableEq

namespace SlotClaimN

private def mapM' {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | x :: xs => match f x, mapM' f xs with
    | some y, some ys => some (y :: ys)
    | _, _ => none

/-- Resolve every name, or fail. -/
def resolve (c : SlotClaimN) (f : String → Option ObjId) : Option SlotClaim := do
  let d ← mapM' (fun x => (f x.1).map (fun k => (k, x.2.1, x.2.2))) c.defined
  let e ← mapM' (fun x => (f x.1).map (fun k => (k, x.2))) c.empty
  let s ← mapM' (fun x => do
    let k ← f x.1
    let seg ← mapM' f x.2
    pure (k, seg)) c.spines
  let n ← mapM' f c.noMM
  pure { defined := d, empty := e, spines := s, noMM := n }

/-- The name-keyed `Row` (SF7), so a certificate can spell one directly. -/
def row (C : String) (seg : List String) (owner : String) (m : String)
    (σ : MethodDecl) : SlotClaimN :=
  let before := seg.takeWhile (· != owner)
  { defined := [(owner, m, σ)]
    empty := before.map (fun k => (k, m))
    spines := [(C, seg)]
    noMM := before }

end SlotClaimN

/-- The boot classes, as a resolver. Every class the boot heap registers; a
    program-created class is *not* here, so a footprint naming one is rejected
    until the claim layer is taken at the post-prefix conformant state (SF9's
    "re-measure per target"). -/
def bootResolver (n : String) : Option ObjId :=
  (Boot.classTable.find? (fun r => r.2.1 == n)).map (·.1)

end RubyCore.Types
