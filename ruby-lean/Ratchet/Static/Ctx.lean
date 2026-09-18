import Ratchet.Static.Closures

/-!
# `Ratchet/Static/Ctx.lean`

**The context, split by polarity** (`notes/ratchet/context-splitting.md`): `Pos` (what is
declared), `Neg` (what is *not*), `Scope` (where we are), and the `Ctx` bundle over the
three, with its accessors, the `Neg` seeding pass and the constant tables.
-/

namespace Ratchet

/-! ## The context, split by polarity (`context-splitting.md`)

`Ctx` used to be one flat record of nine fields, and `context-splitting.md` §1 measured why
that was wrong: the fields have **three different disciplines** and the single record threaded
none of them. They are now three structures.

* **`Pos`** — facts that only ever *grow* along program order. Every premise that reads one is
  a **lookup** ("the table contains at least this fact"), so `PosOk` is a `∀`-over-a-set and
  weakening to a subset is one line.
* **`Neg`** — facts that only ever *shrink*. Every premise that reads one is a **membership**,
  not a miss in `Pos`: absence is its own fact, seeded whole-program (§2.2), not the complement
  of whatever `extendDefs` happened to reconstruct. That is `found-issues.md` §F20's fix.
* **`Scope`** — lexical, rebound on entry to a body, and never reported out. `Ctx.inMethod`
  already drew this line; this names it.

Only `Pos` and `Neg` thread (`Judge`'s `κ'`); `Scope` is pinned equal by every rule. -/

/-- A **receiver port**: the two method-lookup relations this checker walks
(`context-splitting.md` §4.6). `inst C` is `mroList?`/`mroGet?`'s chain — prepends, `C`,
includes, then the superclass chain. `cls C` is `lookupUpS`/`smroGet?`'s — `C`'s singleton
methods and `extend`s, up the superclass chain, **and then the metaclass tail** into `Class`'s
instance chain, which is the entailment §4.6 makes the seed respect. -/
inductive Port where
  | inst (c : String)
  | cls (c : String)
deriving BEq, DecidableEq, Repr, Inhabited

/-- Facts that grow: everything the checker learns as it walks the program in order.

Facts are reported out of a derivation rather than reconstructed from later syntax.
An upper bound such as `globalConsts` grows by weakening absence, not by granting a type. -/
structure Pos where
  classes : CTable
  defs : DefTable
  /-- The **constant** environment (tier 13), keyed by absolute path (`"::LIMIT"`). Carried
      unchanged into every method body, which is the whole reason it is here rather than in
      `Env` — see §Constants below `Ctx.inCtor` for the three facts that force this
      placement. -/
  consts : Env
  /-- The absolute keys `private_constant` has hidden (tier 13d). Read by `Judge.constPath`
      and by nothing else. -/
  privConsts : List String
  /-- Retain the top-level receiver's heap/dispatch world across other activations. -/
  mainWorld : Bool := false
  /-- Classes proved to allocate plain objects, independently of method/initializer rows. -/
  plainAlloc : List String := []
  /-- Upper bound on names possibly bound on Object now; absence outside it is justified
      by conformance. Unlike `consts`, membership grants no value/type information. -/
  globalConsts : List String := []
deriving Inhabited

/-- Facts that shrink: what the program provably does **not** provide.

`noMethod` is keyed by a receiver **port** (§4.5, §4.6) rather than by a bare name, because
Ruby has more than one lookup relation and "is this name free?" has a different answer per
receiver. `(p, n) ∈ noMethod` means *nothing on `p`'s chain provides `n`* — which subsumes four
encodings that used to be separate: `nameFree`, `mroGet? … = none`, `smroGet? … = none`, and
`MissFree`'s `method_missing`.

**Seeded whole-program** (`negSeed`), not built up: a `def` buried in an expression is still a
`def`, and a table reconstructed from statement syntax cannot see it (§F20). Forgetting to seed
a name is conservative (a rule declines); forgetting to *remove* one is unsound, so the fragile
step lives at one place that sees all the syntax. -/
structure Neg where
  /-- The ports the seed enumerated. A port outside this list is unseeded, so a rule asking
      about it declines — the conservative direction §2.2 names. -/
  ports : List Port
  noMethod : List (Port × String)
  /-- Every method name the program declares **anywhere**, on any port. The coarse belt is its
      complement: `nameFree`'s old question, asked over the whole program instead of over the
      already-declared tables, for the rules that have no receiver type to hand.

      Stated as the *declared* set rather than the free one on purpose. The free set would have
      to be enumerated against a name list, and a name missing from that list would read as
      "free" — the unsound direction. A name missing from `declared` is one the program does not
      declare, which is the fact itself. -/
  declared : List String
  /-- A reflective declarer this pre-pass cannot read — `define_method` with a computed name,
      `define_singleton_method` with one. Nothing is free at such a program, and saying so with
      a flag is what keeps the two lists above meaning "and nothing more". -/
  unpinned : Bool
  /-- **The whole program's class table**, `extendClasses` folded over every `class`/`module`
      node wherever written. Read only by the **negative** guards §F9 needs — `isANoOk` and
      `mixinFreeChain`, which ask whether anything *anywhere* disturbs a builtin ancestor chain.
      The *positive* half of narrowing still reads `κ.classes`, the already-declared table, and
      the split is the point: a chain is broken by a class declared later just as much as by one
      declared earlier, while a constant not yet assigned resolves nowhere and raises.

      Asking it whole-program is **strictly more conservative** — a bigger table can only make
      `mixinFreeChain`/`noDeclaredBelow` answer `false`, i.e. refuse more refinements — so it
      cannot admit anything the per-point table refused. What it buys is that the guard is
      *invariant* under `Ctx.afterStmt`, which is what `StateOk`'s down-transport needs and what
      `context-splitting.md` §3 assumed without it. -/
  wholeCls : CTable
  /-- Every constant **name** the program binds anywhere. `coreConstFreeN`'s complement, and it
      is here for `wholeCls`'s reason: `coreConstFree` read `constGet? κ`, which grows, so the
      guard it feeds was antitone in `Pos`. -/
  boundConsts : List String
  /-- No constant of this absolute path is bound anywhere in the program. Not yet consumed by
      any rule — the cref work (§7.2) is what needs it — and seeded empty. -/
  freeConsts : List String
deriving Inhabited

/-- Lexical scope: rebound on entry to a body, never reported out.

Neither a positive fact about the heap nor a negative one. `asms` is here by §7.3's decision —
it is a conditional *assumption*, not a guarantee, and `Ctx.inMethod` already keeps it across a
body entry for a reason that is about scope. -/
structure Scope where
  /-- The definition site of the running method, or `none` outside any method body. -/
  frame : Option Frame
  /-- Every block literal in the program, indexed by `Ty.clos`. Constant for a whole run —
      `validate` fills it in from `collectBlocks` and nothing changes it. -/
  closures : ClosTable
  /-- The **block** the currently-executing method was called with, as a `Ty.clos`, or `none`
      if it has none (or if we are not in a method body). This is what `yield` reads: Ruby
      passes a block implicitly, out of band from the argument list, and `yield` is the only
      way to reach it unless the method also names it with `&b`.

      Set by `callDefBlk` on entry to the body and by nothing else — in particular *not*
      inherited into a nested `callDef`, because a block does not propagate to methods the
      body calls. -/
  blockTy : Option Ty
  /-- The type of `self`, or `none` at top level.

      `none` rather than "the type of `main`" because this judgment has no rule that needs
      it: at top level, `self'` is not typed and an implicit-self send goes to the `defs`
      table. Inside a method body it is `some (.inst c ivars)`, which is what makes
      `class-self-returning-method` work — `self` there is not merely "a `Point`", it is
      *this* `Point`, ivars and all. -/
  selfTy : Option Ty
  /-- The assumptions in force, grown at a call site being discharged (`Judge.callDef`). -/
  asms : AsmTable
  /-- The ordinary `main` receiver world, shared by top level and its method activations.
      False imposes no runtime restriction; changing this flag requires state transport. -/
  runtimeMain : Bool := false
  /-- Ordinary lexical class owner, shared by a class body and its method activations.
      This is independent of the receiver type; `none` imposes no class-scope requirement. -/
  runtimeClass : Option String := none
  /-- Unmentioned self ivars are known to read as nil. Ordinary open instance annotations
      do not provide this fact; fresh initialization does. -/
  closedIvars : Bool := true
deriving Inhabited

/-- The judgment's non-local state, in three disciplines. -/
structure Ctx where
  pos : Pos
  neg : Neg
  scope : Scope
deriving Inhabited

/-- Open receiver annotations say nothing about unmentioned fields. -/
def Ctx.ivarReadTy (κ : Ctx) (I : Ty) (x : String) : Ty :=
  (ivarGet? I x).getD (if κ.scope.closedIvars then .nilT else .any)

/-! ### Field accessors

`Ctx.classes` and friends are `abbrev`s onto the sub-structures, so every `κ.classes` in the
checker, the rules and the proofs reads exactly as it did before the split and still reduces by
`rfl`. Only the *writers* — the sixteen `{ κ with … }` sites — had to move, and they moved to
the four named updaters below. -/
@[reducible] def Ctx.classes (κ : Ctx) : CTable := κ.pos.classes
@[reducible] def Ctx.defs (κ : Ctx) : DefTable := κ.pos.defs
@[reducible] def Ctx.consts (κ : Ctx) : Env := κ.pos.consts
@[reducible] def Ctx.privConsts (κ : Ctx) : List String := κ.pos.privConsts
@[reducible] def Ctx.ports (κ : Ctx) : List Port := κ.neg.ports
@[reducible] def Ctx.noMethod (κ : Ctx) : List (Port × String) := κ.neg.noMethod
@[reducible] def Ctx.declared (κ : Ctx) : List String := κ.neg.declared
@[reducible] def Ctx.negUnpinned (κ : Ctx) : Bool := κ.neg.unpinned
@[reducible] def Ctx.wholeCls (κ : Ctx) : CTable := κ.neg.wholeCls
@[reducible] def Ctx.boundConsts (κ : Ctx) : List String := κ.neg.boundConsts
@[reducible] def Ctx.freeConsts (κ : Ctx) : List String := κ.neg.freeConsts
@[reducible] def Ctx.frame (κ : Ctx) : Option Frame := κ.scope.frame
@[reducible] def Ctx.closures (κ : Ctx) : ClosTable := κ.scope.closures
@[reducible] def Ctx.blockTy (κ : Ctx) : Option Ty := κ.scope.blockTy
@[reducible] def Ctx.selfTy (κ : Ctx) : Option Ty := κ.scope.selfTy
@[reducible] def Ctx.asms (κ : Ctx) : AsmTable := κ.scope.asms

/-- Push an assumption (`Judge.callAsm`/`callDef`/`vcallDef`). -/
@[reducible] def Ctx.pushAsm (κ : Ctx) (a : Asm) : Ctx :=
  { κ with scope := { κ.scope with asms := a :: κ.scope.asms } }

/-- Re-point the running method's definition site (`super`). -/
@[reducible] def Ctx.withFrame (κ : Ctx) (f : Option Frame) : Ctx :=
  { κ with scope := { κ.scope with frame := f } }

/-- Bind the implicit block a body was entered with (`Judge.callDefBlk`). -/
@[reducible] def Ctx.withBlockTy (κ : Ctx) (t : Option Ty) : Ctx :=
  { κ with scope := { κ.scope with blockTy := t } }

/-- Fill in the whole-program block table (`Ctx.withBlocks`, `Ratchet/Validate.lean`). -/
@[reducible] def Ctx.withClosures (κ : Ctx) (K : ClosTable) : Ctx :=
  { κ with scope := { κ.scope with closures := K } }


/-! ### Seeding `Neg` (`context-splitting.md` §2.2, §4.5, §4.6)

`Neg` is not built up as the checker walks; it is **seeded by a whole-program pre-pass**, the
way `Ctx.closures` already is. That is what closes `found-issues.md` §F20: a `def` buried in an
expression is still a `def`, and a table reconstructed from *statement* syntax by
`Ctx.afterStmt` cannot see it, so every premise that read absence as a miss in that table
believed a name was unclaimed when it was not.

The polarity of the mistake is what makes a pre-pass the right shape. **Forgetting to seed a
name is conservative** — the rule that wanted the fact declines — while forgetting to *remove*
one is unsound. So the fragile step lives at one place that sees all the syntax, instead of at
every rule that might declare something.

Three pieces:

1. `negEmit` — walk the whole program and emit one `(Port, name)` for every declaration,
   *wherever* it is written. The site is carried down, so a `def` nested in a method body of
   `class C` lands on `inst C` and not on `Object`, which is both correct and the precision
   §10.1 measured as paying for the seeding.
2. `negWild` — the declarations whose port cannot be pinned (`def obj.m` for an `obj` that is
   not the enclosing `self`, `define_singleton_method`, a computed `define_method` name). These
   remove the name from **every** port; §4.6 argues that is the only sound answer available,
   since `Ty.inst` carries no object identity.
3. `negSeed` — the grid, closed under both chains of §4.6. -/

/-- The method names a rule ever asks `Neg` about. A name absent from this list is simply never
seeded, so a rule asking about it fails its premise — the conservative direction. -/
def negNames : List String :=
  ["lambda", "proc", "method_missing", "is_a?", "===", "nil?", "raise", "to_s", "class", "x",
   "new", "call"]

/-- The metaclass tail of §4.6: once a class object's singleton chain is exhausted, `C.foo`
falls through to these classes' **instance** methods. So `(cls C, n)` may only be seeded when
none of them declares `n` either — which is what makes the seed strictly finer than the
`nameFree κ "to_s"` belt §F7 needed, rather than merely different. -/
def metaTail : List String := ["Class", "Module", "Object", "Kernel", "BasicObject"]

/-- The class objects the seed enumerates. Anything outside this list is unseeded, so a rule
asking about it declines. -/
def negOwnerNames (C : CTable) : List String :=
  ("Object" :: "Proc" :: "Regexp" :: "Range" :: metaTail ++ builtinClsNames) ++ C.map (·.name)

/-- One declaration, at the port it lands on. -/
abbrev NegEmit := Port × String

/-- What one pass over a subexpression yields: the declarations it performs, the names whose
port it could not pin, and every `class`/`module` node it contains — the last so that the
**whole-program** class table can be folded from them, since `Ctx.afterStmt`'s version sees
only top-level statements and that is the other half of §F20. -/
structure NegAcc where
  emits : List NegEmit
  wild : List String
  decls : List Expr
  /-- Every constant **name** bound, wherever written. -/
  consts : List String

instance : Append NegAcc where
  append a b := ⟨a.emits ++ b.emits, a.wild ++ b.wild, a.decls ++ b.decls, a.consts ++ b.consts⟩

def NegAcc.empty : NegAcc := ⟨[], [], [], []⟩

/-- The site a `def` written here installs onto: the lexically enclosing class or module, or
`Object` at top level. Carried down through method bodies and blocks, because that is what
Ruby's *cref* does — `class C; def a; def b; end; end; end` makes `b` an instance method of
`C`. -/
abbrev NegSite := String

/-- The instance-method names an `attr_*` call declares. `attr_writer`/`attr_accessor` also
declare the `name=` setter. -/
def attrNames (s : NegSite) (m : String) : List Expr → List NegEmit
  | [] => []
  | .sym n :: rest =>
    let setter := if m == "attr_reader" then [] else [(Port.inst s, n ++ "=")]
    (Port.inst s, n) :: setter ++ attrNames s m rest
  | _ :: rest => attrNames s m rest

mutual

/-- Every declaration the program performs, with the port it lands on. Recurses into **every**
expression position, which is the whole point (§F20). -/
def negEmit (s : NegSite) : Expr → NegAcc
  | .def' n _ body => ⟨[(.inst s, n)], [], [], []⟩ ++ negEmit s body
  -- `def self.m` inside `class C` is a singleton method of `C`. Anywhere else — a `def obj.m`
  -- on some other receiver, or a `def self.m` at top level, where `self` is `main` — the port
  -- is not expressible (`Ty.inst` carries no object identity), so §4.6's uniform answer: the
  -- name leaves every port.
  | .defs recv n _ body =>
    (match recv with
     | .self' => if s == "Object" then ⟨[], [n], [], []⟩ else ⟨[(.cls s, n)], [], [], []⟩
     | _ => ⟨[], [n], [], []⟩) ++ negEmit s recv ++ negEmit s body
  | e@(.class' n sup body) =>
    ⟨[], [], [e], []⟩ ++ negEmitOpt s sup ++ negEmit n body
  | e@(.module' n body) => ⟨[], [], [e], []⟩ ++ negEmit n body
  -- A `class << obj` body declares singleton methods on an object the checker cannot name, so
  -- every name it declares leaves every port.
  | .sclass obj body =>
    let inner := negEmit s body
    ⟨[], inner.emits.map (·.2), [], []⟩ ++ negEmit s obj ++ inner
  | .alias' nw _ => ⟨[(.inst s, nw)], [], [], []⟩
  | .undef ns => ⟨[], ns, [], []⟩
  | .send recv m args blk =>
    let base := negEmitOpt s recv ++ negEmitAll s args ++ negEmitOpt s blk
    -- The reflective declarers. A literal-symbol name is as pinnable as a `def`; a computed
    -- one is not, and there is nothing honest to do with it but drop every name — which the
    -- `""` marker does, by emptying the seed.
    if m == "attr_reader" || m == "attr_accessor" || m == "attr_writer" then
      ⟨attrNames s m args, [], [], []⟩ ++ base
    else if m == "define_method" then
      (match args with
       | [.sym n] => ⟨[(.inst s, n)], [], [], []⟩
       | _ => ⟨[], [""], [], []⟩) ++ base
    else if m == "alias_method" then
      (match args with
       | [.sym nw, _] => ⟨[(.inst s, nw)], [], [], []⟩
       | _ => ⟨[], [""], [], []⟩) ++ base
    else if m == "define_singleton_method" then
      (match args with
       | .sym n :: _ => ⟨[], [n], [], []⟩
       | _ => ⟨[], [""], [], []⟩) ++ base
    else base
  | .seq es => negEmitAll s es
  | .vasgn _ _ e => negEmit s e
  | .casgn n e => ⟨[], [], [], [n]⟩ ++ negEmit s e
  | .cpathAsgn b n e => ⟨[], [], [], [n]⟩ ++ negEmitOpt s b ++ negEmit s e
  | .cpath b _ => negEmitOpt s b
  | .array es => negEmitAll s es
  | .hash ps => negEmitPairs s ps
  | .block _ _ body => negEmit s body
  | .yield' args => negEmitAll s args
  | .blockpass e => negEmitOpt s e
  | .if' c t e => negEmit s c ++ negEmit s t ++ negEmitOpt s e
  | .while' c body => negEmit s c ++ negEmit s body
  | .dowhile body c => negEmit s body ++ negEmit s c
  | .for' _ coll body => negEmit s coll ++ negEmit s body
  | .begin' body rescues els ens =>
    negEmit s body ++ negEmitRescues s rescues ++ negEmitOpt s els ++ negEmitOpt s ens
  | .super' args blk => negEmitAll s args ++ negEmitOpt s blk
  | .zsuper blk => negEmitOpt s blk
  | .ret e => negEmitOpt s e
  | .brk e => negEmitOpt s e
  | .nxt e => negEmitOpt s e
  | .splat e => negEmitOpt s e
  | .defined e => negEmit s e
  | .kwargs es => negEmitKw s es
  -- `class A::B` / `module A::B` — the base is an expression and the body declares under `B`.
  -- The node itself is **not** offered to `extendClasses`, which does not read these shapes; a
  -- class it cannot read is a class no rule can use, and the declarations inside it are still
  -- emitted, which is the conservative direction.
  | .scopedClass b n body => negEmitOpt s b ++ negEmit n body
  | .scopedModule b n body => negEmitOpt s b ++ negEmit n body
  | _ => NegAcc.empty

def negEmitAll (s : NegSite) : List Expr → NegAcc
  | [] => NegAcc.empty
  | e :: es => negEmit s e ++ negEmitAll s es

def negEmitOpt (s : NegSite) : Option Expr → NegAcc
  | none => NegAcc.empty
  | some e => negEmit s e

def negEmitPairs (s : NegSite) : List (Expr × Expr) → NegAcc
  | [] => NegAcc.empty
  | (k, v) :: ps => negEmit s k ++ negEmit s v ++ negEmitPairs s ps

def negEmitKw (s : NegSite) : List KwEntry → NegAcc
  | [] => NegAcc.empty
  | .pair _ v :: es => negEmit s v ++ negEmitKw s es
  | .dyn k v :: es => negEmit s k ++ negEmit s v ++ negEmitKw s es
  | .splat e :: es => negEmit s e ++ negEmitKw s es

def negEmitRescues (s : NegSite) :
    List (List Expr × Option (TargetKind × String) × Expr) → NegAcc
  | [] => NegAcc.empty
  | (cls, _, body) :: rs => negEmitAll s cls ++ negEmit s body ++ negEmitRescues s rs

end


/-! #### Closing the seed under the two chains (§4.6)

A raw emission says where a declaration *lands*; a `Neg` fact is about a whole **chain**. The
two are joined here, and the closure is done **at seed time** rather than re-checked per rule —
which is §10.4's resolution: the pre-pass sees the entire static hierarchy (superclasses,
`include`, `prepend`, `extend`), so `Coherent` modulo inheritance holds by construction. -/

/-- The instance lookup chain of `c` under the whole-program table, plus `Object` — which is on
every instance chain and is where a top-level `def` lands. -/
def negInstChain (C : CTable) (c : String) : List String :=
  ((mroList? C c).getD [c]) ++ ["Object"]

/-- The class object's own chain: `c` and its superclasses, walked with `C.length` fuel the way
`lookupUpS` does. -/
def negSingChain (C : CTable) : Nat → String → List String
  | 0, _ => []
  | k + 1, n =>
    n :: (match clsGet? C n with
          | some c => match c.super? with
                      | some sn => negSingChain C k sn
                      | none => []
          | none => [])

/-- Does any emission put `n` on `inst c`'s chain? Also reads each chain entry's `prepends`
and `includes`, which `mroList?` already folds in, so this is a lookup rather than a walk. -/
def negInstHit (C : CTable) (E : List NegEmit) (c n : String) : Bool :=
  (negInstChain C c).any (fun a => E.contains (.inst a, n))

/-- Does any emission put `n` on `cls c`'s chain — the singleton chain, the modules each of its
entries `extend`s, **or the metaclass tail**? The third disjunct is §F7's belt made precise:
today's `nameFree κ "to_s"` goes false as soon as any class anywhere declares `to_s`; this asks
only about `Class`/`Module`/`Object`/`Kernel`/`BasicObject`. -/
def negClsHit (C : CTable) (E : List NegEmit) (c n : String) : Bool :=
  let chain := negSingChain C (C.length + 1) c
  chain.any (fun a =>
    E.contains (.cls a, n) ||
    (match clsGet? C a with
     | some cl => cl.extended.any (fun mm => negInstHit C E mm n)
     | none => false)) ||
  metaTail.any (fun t => negInstHit C E t n)

/-- The whole-program class table: `extendClasses` folded over **every** `class`/`module` node
`negEmit` found, wherever written. -/
def wholeClasses (ds : List Expr) : CTable := ds.foldl extendClasses []

/-- The `Neg` a program is checked under. -/
def negSeed (p : Expr) : Neg :=
  let acc := negEmit "Object" p
  let C := wholeClasses acc.decls
  let E := acc.emits
  -- A declaration whose name could not be pinned to a port removes that name everywhere; the
  -- empty string is `negEmit`'s marker for "a reflective declarer with a computed name", which
  -- nothing can be sound about, so it empties the seed.
  if acc.wild.contains "" then ⟨[], [], [], true, C, acc.consts, []⟩ else
  let names := negNames.filter (fun n => !acc.wild.contains n)
  let owners := negOwnerNames C
  let ports := owners.flatMap (fun c => [Port.inst c, Port.cls c])
  let noMethod :=
    names.flatMap (fun n =>
      owners.flatMap (fun c =>
        (if negInstHit C E c n then [] else [(Port.inst c, n)]) ++
        (if negClsHit C E c n then [] else [(Port.cls c, n)])))
  -- The coarse belt, whole-program: every name the program declares anywhere, at any port or
  -- at none. This is what `nameFree` used to read off the already-declared tables.
  ⟨ports, noMethod, E.map (·.2) ++ acc.wild, false, C, acc.consts, []⟩

/-! #### Reading `Neg`

Three queries, and the shape §4.4 argues for: every one is a **lookup**, not a whole-table
scan. A miss in a positive table is a claim about that table's completeness; a hit in `Neg` is
a fact of its own. -/

/-- **Is `n` free on this receiver port?** The keyed query (§4.5). -/
def portFree (κ : Ctx) (p : Port) (n : String) : Bool := κ.noMethod.contains (p, n)

/-- **Is `n` declared nowhere in the program?** The coarse belt, for a rule with no receiver
type to hand — `Judge.bareName`, `lambdaLit`, `raiseCls`, and the narrowing guards, all of
which are implicit-self sends whose `self` this judgment does not always type.

This is `nameFree`'s question, and the only change is *where* it is asked: over the whole
program, so a `def` written anywhere at all answers it (`found-issues.md` §F20), rather than
over the tables `Ctx.afterStmt` reconstructed from statement syntax. -/
def nameFreeN (κ : Ctx) (n : String) : Bool := !κ.negUnpinned && !κ.declared.contains n

/-- The receiver ports a type denotes, or `none` where the type pins no class — `.any`, an
arrow, an ivar spine. `none` is not "no ports": a rule asking about an unpinned receiver gets
`false` and declines. -/
def tyPorts? : Ty → Option (List Port)
  | .int => some [.inst "Integer"]
  | .float => some [.inst "Float"]
  | .bool => some [.inst "TrueClass", .inst "FalseClass"]
  | .nilT => some [.inst "NilClass"]
  | .sym => some [.inst "Symbol"]
  | .cls n => some [.inst n]
  | .clsOf n => some [.cls n]
  | .arrayOf _ => some [.inst "Array"]
  | .hashOf _ _ => some [.inst "Hash"]
  | .inst n _ => some [.inst n]
  | .clos _ _ _ => some [.inst "Proc"]
  | .never => some []
  | .nilable τ => (tyPorts? τ).map (fun ps => .inst "NilClass" :: ps)
  | .union σ τ =>
    match tyPorts? σ, tyPorts? τ with
    | some a, some b => some (a ++ b)
    | _, _ => none
  | .sameAs _ τ => tyPorts? τ
  | _ => none

/-- **Is `n` free on every port a receiver of type `σ` can have?** -/
def tyFree (κ : Ctx) (σ : Ty) (n : String) : Bool :=
  match tyPorts? σ with
  | some ps => ps.all (fun p => portFree κ p n)
  | none => false

/-- **The frame-sensitive records in `Ctx` that an assignment can invalidate.**

`Ratchet/Lang/Ty.lean` §Stale closure captures fixes `Judge.vasgn` by *rewriting* the outgoing
`Env` and ivar spine (`killClosOver`/`killClosOverSpine`). Three `Ctx` fields can hold a
`Ty.clos` too — `selfTy` (its ivar spine may name one), `blockTy` (it *is* one) and `consts` —
and `Ctx` is an **input** to every rule: no rule rewrites it, so no rule can widen them. So
they become a *premise* instead: the rule applies only where they record nothing about the
assigned name that the assignment would falsify.

Sound rather than precise, and the imprecision is namespaced. A method frame captures nothing,
so an assignment inside a method body cannot reach the frame `blockTy`'s closure captured;
this premise nevertheless refuses the case where the two happen to use the same *name*. The
alternative — a `StateOk` component stating frame-chain disjointness — is a bigger change to
the semantic side for precision no rung has asked for; recorded in `found-issues.md` §F1
rather than built. -/
def capStaleCtx (x : String) (τ : Ty) (κ : Ctx) : Bool :=
  capStale x τ (κ.selfTy.getD .never) || capStale x τ (κ.blockTy.getD .never) ||
    κ.consts.any (fun p => capStale x τ p.2)

/-- The class name behind a `self` type, for `Frame.recvClass`. `.inst n _` and `.clsOf n`
are the only two shapes any body-entering rule supplies; anything else cannot arise and gets a
name no class has, which makes `super` fail rather than dispatch somewhere wrong. -/
def selfClsName : Ty → String
  | .inst n _ => n
  | .clsOf n => n
  | _ => ""

/-- Entering a method body whose `self` has type `σ`. Only `selfTy` changes: the class and
method tables are the ones in force at the call site, and the assumption table is *kept*,
because a recursive call made from inside a body must still find the assumption discharging
it. The body's *locals* are not in `Ctx` at all — they are the threaded `Env`, and a call
rule supplies `paramEnv`'s fresh one. -/
def Ctx.inMethod (κ : Ctx) (σ : Ty) (dc m : String) : Ctx :=
  { κ with scope := { κ.scope with selfTy := some σ, frame := some ⟨selfClsName σ, dc, m⟩ } }

/-- Entering a body whose `self` this judgment declines to type — `initialize` (see
`Judge.newInst`) — but whose *definition site* still has to be recorded, because the body may
call `super`. -/
def Ctx.inCtor (κ : Ctx) (rc dc m : String) : Ctx :=
  κ.withFrame (some ⟨rc, dc, m⟩)

/-! ### Constants (tier 13)

A constant is a **binding**, and the three facts that decide where it lives are:

1. its type is not syntactic — `LIMIT = compute` needs the judgment to know what `compute`
   answers, so a constant table cannot be built by a syntactic pre-pass the way `CTable`
   and `DefTable` are;
2. it is written once and read from *everywhere afterwards*, including from inside method
   bodies whose local environment is the fresh, parameters-only one `paramEnv` builds — so
   it cannot live in `Env`, which is exactly the state a call rule replaces;
3. but it is still **order-sensitive**: `X + 1; X = 10` raises `NameError`, so a
   whole-program table would certify a program that fails.

`Ctx.consts` satisfies all three at once. It is in `Ctx`, so every body-entering rule
(`Ctx.inMethod`/`inCtor`, and the call rules' `{κ with …}`) carries it into the callee for
free — which is right, because a constant assigned before the call really is assigned when
the body runs. And it grows at `JudgeSeq.cons`, which is the one rule that knows statement
order, so fact 3 holds for the same reason `foo(); def foo; end` has no derivation.

The price is that `Ctx.afterStmt` now needs the statement's **type**, since that is what a
`casgn` binds. That is available in `JudgeSeq.cons` (it is the `σ` the first premise
produces) and in `chkSeq`, and it is the only change to a rule already on file.

Keys are the constant's **absolute path** (`"::LIMIT"`, `"::Box::SIZE"`), which is Ruby's own
notation for one and keeps the namespace visibly disjoint from `Env`'s locals — no local can
contain a colon. -/
def constPaths (κ : Ctx) (n : String) : List String :=
  match κ.frame with
  | some f => [constKeyIn f.defClass n, constKey n]
  | none => [constKey n]

/-- What a constant read resolves to, or `none` if the program has not assigned it — in
which case there is no rule and the read is rejected, which is what fact 3 above buys.

**Resolution is lexical, innermost first** (tier 13b): inside a method body, a bare `SIZE`
means `Box::SIZE` if the running method was *declared* in `Box`, and the top-level `SIZE`
otherwise. `Frame.defClass` is exactly the right name to ask — it is where the method was
found, which for a method declared with `def` inside `class Box` is `Box`, and for an
inherited one is the ancestor whose body the `def` was written in. Both are Ruby's lexical
cref for that `def`.

Outside any method (`frame = none`) only the top-level path is tried, which is why
`class Box; SIZE = 3; end; SIZE` is rejected — Ruby raises `NameError` for it. -/
def constGet? (κ : Ctx) (n : String) : Option Ty :=
  (constPaths κ n).findSome? (fun k => envGet? κ.consts k)

/-- The constants a statement binds. `envSet` rather than a cons because Ruby's
re-assignment of a constant is a warning, not an error, and the *later* type is the live one.

A `class`/`module` statement binds the constants in its **body** (tier 13b), and those get
their types from `constLitTy?` — see §A class body's constants for why that is a syntactic
function and what makes it sound. -/
def extendConsts (S : Env) : Expr → Ty → Env
  | .casgn n _, τ => envSet S (constKey n) τ
  -- Tier 13c: `M::X = 4`. The base is matched *syntactically* here, which is why
  -- `Judge.cpathAsgn` is stated at the same syntax: the two have to agree about the key, and
  -- a base this pattern does not read simply binds nothing (conservative).
  | .cpathAsgn (some (.const owner)) n _, τ => envSet S (constKeyIn owner n) τ
  -- Tier 13e: and the constants of anything nested inside it, at their qualified owners.
  | .class' n _ body, _ =>
    addNestedConsts (addClassConsts S n (bodyConsts body)) nestFuel n (bodyNested body)
  | .module' n body, _ =>
    addNestedConsts (addClassConsts S n (bodyConsts body)) nestFuel n (bodyNested body)
  | _, _ => S

/-- **What a constant assignment owes the tables that already describe the name**
(`found-issues.md` §F18).

`Ctx.afterStmt` records a constant's type from a **top-level `casgn` statement**, and
`extendConsts` matches only that shape — so an assignment *buried* inside a larger expression
(`y = (X = "s")`) rebinds the constant at run time while `κ.consts` still carries the old type.
`Judge.casgn` had no premise at all and its docstring called the invisibility "conservative, in
the direction that costs a rung rather than soundness". It was not: `X = 1; y = (X = "s"); X + 1`
was certified `Integer` against a `TypeError`, and `y = (String = 5); String.new` is the same
hole through `constBuiltin` instead of `constEnv`.

**Agreement, not absence** — the same shape §F17 settled on, and for the same reason: the
first assignment of a name resolves nowhere yet, so absence is what the *common* case has, and
a re-assignment at the type already recorded changes nothing anyone read. What is refused is a
rebinding the tables would then be wrong about: a different type, a declared class, a builtin
class, or an exception class. -/
def constAsgnOk (κ : Ctx) (n : String) (τ : Ty) : Bool :=
  match constGet? κ n with
  | some σ => σ == τ
  | none =>
    (clsGet? κ.classes n).isNone && !builtinClsNames.contains n && !excName? κ.classes n

/-- `κ` after performing statement `e`, which produced a value of type `τ`: both syntax
tables grow, the constant table grows if `e` was a `casgn`, nothing else changes. Used only
by `JudgeSeq.cons`, which is the only rule that knows about statement order.

`τ` is used by `extendConsts` alone; every other component of the result is syntactic. -/
def Ctx.afterStmt (κ : Ctx) (e : Expr) (τ : Ty) : Ctx :=
  { κ with pos := { classes := extendClasses κ.classes e, defs := extendDefs κ.defs e,
                     consts := extendConsts κ.consts e τ,
                     privConsts := extendPrivConsts κ.privConsts e } }

/-- Is the method name `m` **unclaimed by the program** — no top-level `def`, and no class or
module in the table declaring it as an instance or singleton method?

Read by `Judge.lambdaLit` (`found-issues.md` §F2). `lambda { … }` is an *implicit-self send*,
and in CRuby a toplevel `def lambda` installs a private method **on `Object`** while `Kernel`
is included *in* `Object` — so the user's definition shadows `Kernel#lambda` and
`f = lambda { 1 }` binds `5`, not a Proc. The rule concluded `.clos` unconditionally, which is
how `def lambda; 5; end; f = lambda { 1 }; f.call + 1` came to be certified `Integer` against a
`NoMethodError`.

Deliberately coarse: it asks whether *any* class declares the name, not whether the class
`self` belongs to does. Sharpening it means reading `κ.selfTy` and the ancestor chain, and the
imprecision costs nothing any rung wants — no program in this corpus names a method `lambda` or
`proc`. -/
def nameFree (κ : Ctx) (m : String) : Bool :=
  (κ.defs.find? (·.name == m)).isNone &&
  κ.classes.all (fun c => (c.methods.find? (·.name == m)).isNone &&
                          (c.smethods.find? (·.name == m)).isNone)

/-- `paramEnv` for a call that **carries a block**. Same walk, plus one case: a
`&b` parameter (`Param.block`) consumes not an argument but the block itself.

`blk` is `none` when the call passes no block, and then `&b` binds `.nilT` — which is exactly
Ruby (`def run(&b); b; end; run` is `nil`), and also exactly why the binding cannot be
skipped: `b` is in scope either way. A `&b` parameter is required to come **last**, which is
not enforced here because the parser already guarantees it. -/
def paramEnvB (blk : Option Ty) (ps : List Param) (τs : List Ty) : Option Env :=
  paramBind blk ps τs []

end Ratchet
