import Ratchet.Static.Lookup

/-!
# `Ratchet/Static/Classes.lean`

The **class table**: `Cls`/`CTable`, what a class body's members are (`clsMember?`,
`splitMembers`, alias resolution), the constants and `private_constant` names a body
contributes, and method lookup up the chain (mixins, the MRO as a list, `mroGet?`/`smroGet?`,
exception-class names, the constructor).
-/

namespace Ratchet

/-! ## Tier 7's class table, and the context bundle

A class is a *third* kind of thing the checker has to remember, and unlike a `def` it
carries two method tables and a superclass. At that point `Judge`'s index list stops being
readable, so the four **input-only** components — classes, methods, assumptions and the type
of `self` — are bundled into one `Ctx`. Nothing about the bundling is semantic; it is the
difference between five indices and one.

What is *not* in `Ctx` is what threads: the local environment and (new at tier 7) the ivar
spine. Those stay explicit, before and after, because reading a rule means reading how they
flow. -/

/-- One class declaration, as the checker sees it: a name, an optional superclass name, and
its two method tables. No types, and no ivar list — Ruby declares neither.

`smethods` are the **singleton** methods (`def self.origin`), which are a genuinely separate
namespace: `Point.origin` and a `Point`'s `origin` are different methods, and only the first
exists here. -/
structure Cls where
  name : String
  super? : Option String
  methods : List Defn
  smethods : List Defn
  /-- `true` for a `module`. One `Cls` serves both because everything tier 8 asks for —
      `M.foo` resolving to a `def self.foo` — is `callSMethod` unchanged, and duplicating the
      structure to express that would duplicate the lookups too.

      What the flag is *for* is the one place the two really differ: **a module cannot be
      allocated.** `M.new` raises `NoMethodError`, so `ctorGet?`/`instClsGet?` refuse a module
      and `newInst`/`newInstNoInit`/`selfNew` go through them. Without the flag, `M.new`
      would find no `initialize`, take the zero-argument allocator route, and certify a
      program that raises.

      A module's *instance* methods (a plain `def` in its body) are recorded in `methods` and
      are unreachable, which is correct-by-accident and worth saying out loud: they become
      callable through `include`/`extend`/`module_function`, none of which has a rule, so no
      program that uses one types at all. `M.foo` for an instance-method `foo` looks in
      `smethods`, misses, and is rejected — which is what Ruby does too. Tier 10's
      `include`/`extend` are what make them reachable, via the two fields below. -/
  isModule : Bool
  /-- Modules mixed into **instance** dispatch by `include M` in this class's body, in source
      order. `mroGet?` searches them after the class's own methods and before its superclass,
      and it searches them **reversed**, because a later `include` wins in Ruby. -/
  includes : List String
  /-- Modules mixed in **ahead of the class itself** by `prepend M` (tier 10). The only mixin
      direction that changes the *order* rather than just adding to it: `class C; prepend M;
      def f; …; end; end` gives `C.ancestors = [M, C, …]`, so `M#f` wins over `C#f` and a
      `super` inside `M#f` runs `C#f`. That second half is why prepend forced the MRO to become
      a **list** (`mroList?`) instead of a `super?` walk — `M`'s "next" is `C`, which is not
      `M`'s superclass and could not be found from `M` alone. -/
  prepends : List String
  /-- Modules mixed into **singleton** dispatch by `extend M`. The asymmetry with `includes` is
      the whole content of `extend`: it takes the module's *instance* methods (a plain `def M`)
      and makes them methods of the class **object**, so `smroGet?` looks in `.methods`, not in
      `.smethods`. `metaprog-extend`'s `module Loud; def shout; …; end; class Person; extend
      Loud; end; Person.shout` is exactly that one-line fact. -/
  extended : List String

abbrev CTable := List Cls

def clsGet? (C : CTable) (n : String) : Option Cls := C.find? (·.name == n)

/-- One member of a class body that this checker can read. -/
inductive ClsMember where
  | inst (d : Defn)
  | sing (d : Defn)
  /-- `include M` (tier 10). -/
  | incl (n : String)
  /-- `extend M` (tier 10). -/
  | ext (n : String)
  /-- `prepend M` (tier 10). -/
  | prep (n : String)
  /-- `SIZE = 3` in a class body (tier 13) — a **constant**, carried as its unjudged
      initializer, because the class table is built by a syntactic function and a type is not
      syntactic. What closes that gap is `constLitTy?` plus `JudgeConsts`: see
      `Judge.classStmt`. -/
  | constM (n : String) (e : Expr)
  /-- `attr_reader :x, :y` (tier 13d) — *n* method declarations in one statement.
      `splitMembers` expands each name into the `def x; @x; end` it stands for, so nothing
      downstream knows this member kind existed. -/
  | attrR (names : List String)
  /-- `alias length size` (tier 13d). Resolved by `classMethods?`, not here: an alias copies a
      method that has to be found first, and only the whole member list knows what is
      there. -/
  | aliasM (newName oldName : String)
  /-- `private_constant :SECRET` (tier 13d). Declares nothing, so `splitMembers` drops it;
      what reads it is `privNames`, from `Ctx.afterStmt`. -/
  | privC (names : List String)
  /-- A **nested class or module** (tier 13e): `module M; class Box; … end; end`. The flag is
      `Cls.isModule`'s. Carried as its unread body, because everything about it — its own
      members, its own constants, its own nested declarations — has to be recomputed under
      the *qualified* name `M::Box`, and only the enclosing statement knows the prefix. -/
  | nestedM (isMod : Bool) (name : String) (body : Expr)

/-- A list of send arguments as bare symbol names, or `none` if any argument is anything
else. `attr_reader`/`private_constant` are declarations, so an argument this cannot read has
to make the whole member unreadable rather than be skipped. -/
def symNames? : List Expr → Option (List String)
  | [] => some []
  | .sym n :: es => (symNames? es).map (fun ns => n :: ns)
  | _ => none

/-- The methods `attr_reader :x` stands for: `def x; @x; end`, one per name. The ivar's name
is the reader's with an `@`, which is Ruby's rule and the only thing there is to know about
`attr_reader`. -/
def attrDefns : List String → List Defn
  | [] => []
  | n :: ns => ⟨n, [], .var .ivar ("@" ++ n)⟩ :: attrDefns ns

def clsMember? : Expr → Option ClsMember
  | .def' n ps b => some (.inst ⟨n, ps, b⟩)
  -- `def self.m` is the only `defs` receiver read: `def obj.m` for some other object is a
  -- singleton method on *that* object, which this checker has no way to record.
  | .defs .self' n ps b => some (.sing ⟨n, ps, b⟩)
  -- Tier 10. Both are ordinary implicit-self sends in the desugared syntax, and the argument
  -- is required to be a **bare constant**: `include some_expr` is not read, so the class does
  -- not enter the table and nothing using it is typed. That the named module is really a
  -- *module* is checked separately, by `Judge.classStmt` -- `include SomeClass` raises
  -- `TypeError` in Ruby, and the table cannot see `isModule` from here.
  | .send none "include" [.const n] none => some (.incl n)
  | .send none "extend" [.const n] none => some (.ext n)
  | .send none "prepend" [.const n] none => some (.prep n)
  -- Tier 13: a constant. Unlike a `def`, a `casgn` in a class body **executes** when the
  -- class statement runs, which is why it is the first member kind `classStmt` has to type
  -- rather than merely record.
  | .casgn n e => some (.constM n e)
  -- Tier 13d. All three are the same kind of thing as `include`: an ordinary class-body
  -- statement that this checker reads *declaratively*, matched at the exact syntax the
  -- desugarer emits. The arguments must be bare symbol literals; `attr_reader(*names)` is not
  -- read, so the class does not enter the table and nothing using it types.
  | .send none "attr_reader" args none => (symNames? args).map ClsMember.attrR
  | .send none "private_constant" args none => (symNames? args).map ClsMember.privC
  | .alias' newName oldName => some (.aliasM newName oldName)
  -- Tier 13e. A nested class with a **superclass** is deliberately not read: the superclass
  -- name would need resolving against the nesting too, and refusing the member here makes the
  -- *enclosing* class unreadable rather than silently dropping the nested one.
  | .class' n none body => some (.nestedM false n body)
  | .module' n body => some (.nestedM true n body)
  | _ => none

abbrev Nested := List (Bool × String × Expr)

def splitMembers :
    List ClsMember →
      List Defn × List Defn × List String × List String × List String ×
        List (String × Expr) × List (String × String) × Nested
  | [] => ([], [], [], [], [], [], [], [])
  | .inst d :: ms =>
    let (i, s, c, e, p, k, a, z) := splitMembers ms; (d :: i, s, c, e, p, k, a, z)
  | .sing d :: ms =>
    let (i, s, c, e, p, k, a, z) := splitMembers ms; (i, d :: s, c, e, p, k, a, z)
  | .incl n :: ms =>
    let (i, s, c, e, p, k, a, z) := splitMembers ms; (i, s, n :: c, e, p, k, a, z)
  | .ext n :: ms =>
    let (i, s, c, e, p, k, a, z) := splitMembers ms; (i, s, c, n :: e, p, k, a, z)
  | .prep n :: ms =>
    let (i, s, c, e, p, k, a, z) := splitMembers ms; (i, s, c, e, n :: p, k, a, z)
  | .constM n e :: ms =>
    let (i, s, c, e', p, k, a, z) := splitMembers ms; (i, s, c, e', p, (n, e) :: k, a, z)
  -- Tier 13d: expanded here, so no later function knows `attr_reader` exists.
  | .attrR ns :: ms =>
    let (i, s, c, e, p, k, a, z) := splitMembers ms; (attrDefns ns ++ i, s, c, e, p, k, a, z)
  | .aliasM nw od :: ms =>
    let (i, s, c, e, p, k, a, z) := splitMembers ms; (i, s, c, e, p, k, (nw, od) :: a, z)
  -- `private_constant` declares nothing; it is read off the body separately (`privNames`).
  | .privC _ :: ms => splitMembers ms
  | .nestedM im n b :: ms =>
    let (i, s, c, e, p, k, a, z) := splitMembers ms; (i, s, c, e, p, k, a, (im, n, b) :: z)

/-- `alias new old` copies the method `old` names, so it can only be resolved once the whole
member list is known — which is why it is `classMethods?`'s job and not `clsMember?`'s.

**An unresolvable alias makes the whole class unreadable** (`none`), rather than being
skipped. Ruby raises `NameError` for `alias b a` with no `a`, and `NameError` is outside this
package's type-stuck family, so skipping would have been "sound" and useless: the class would
enter the table missing a method, and a later dispatch would fail for the wrong reason.

What this does *not* enforce is Ruby's ordering requirement — the aliased method must be
defined *before* the `alias` line. `splitMembers` keeps each kind's source order but loses the
interleaving between kinds, so `class C; alias b a; def a; 1; end; end` is accepted here and
raises `NameError` in Ruby. Outside the family, and recorded rather than fixed. -/
def resolveAliases : List Defn → List (String × String) → Option (List Defn)
  | ms, [] => some ms
  | ms, (nw, od) :: as =>
    match defGet? ms od with
    | some d => resolveAliases (⟨nw, d.params, d.body⟩ :: ms) as
    | none => none

def finishMembers :
    List Defn × List Defn × List String × List String × List String ×
      List (String × Expr) × List (String × String) × Nested →
    Option (List Defn × List Defn × List String × List String × List String ×
      List (String × Expr) × Nested)
  | (ms, sms, incs, exts, preps, cs, als, nst) =>
    (resolveAliases ms als).map (fun ms' => (ms', sms, incs, exts, preps, cs, nst))

/-- A class body's instance and singleton methods, or `none` if the body contains anything
this checker cannot read.

**That `none` is doing two jobs at once**, which is why the restriction sits in one place.
It is what makes the body safe to *evaluate* unchecked — a `def`/`defs` statement never runs
its body, and `nil` is `nil`, so a body made only of those cannot be type-stuck — and it is
what makes the class readable into `CTable`. A body with an ivar assignment at class level, a
nested class, or anything executable is not typed at all: conservative in the direction that
costs rungs rather than soundness, and it is the shape every tier-7 rung has.

**Tier 13 punched the one hole in "nothing executable".** A `casgn` in a class body *does*
run when the class statement runs, so admitting it means `classStmt` has to type it rather
than merely record it — which is exactly what its `JudgeConsts` premise does. The sixth
component of the tuple is those constants, paired with their unjudged initializers. -/
def classMethods? :
    Expr → Option (List Defn × List Defn × List String × List String × List String ×
      List (String × Expr) × Nested)
  | .nil => some ([], [], [], [], [], [], [])
  | .seq es => (es.mapM clsMember?).bind (fun ms => finishMembers (splitMembers ms))
  | e => (clsMember? e).bind (fun m => finishMembers (splitMembers [m]))

/-- The absolute path of a constant defined at top level. -/
def constKey (n : String) : String := "::" ++ n

/-- The absolute path of a constant defined in the body of class-or-module `owner`. -/
def constKeyIn (owner n : String) : String := "::" ++ owner ++ "::" ++ n

/-- Every constant a **class or module statement** binds, as path/type pairs. Skips any
initializer `constLitTy?` cannot read — which costs nothing, because `Judge.classStmt` would
not have typed the statement at all in that case. -/
def addClassConsts (S : Env) (owner : String) : List (String × Expr) → Env
  | [] => S
  | (n, e) :: cs =>
    addClassConsts (match constLitTy? e with
                    | some τ => envSet S (constKeyIn owner n) τ
                    | none => S) owner cs

/-- The same, for the constants of **nested** declarations (tier 13e), whose owner is the
qualified name. Fuel-bounded for `nestedClasses`' reason and with the same consequence: a
dropped constant is a rejected read. -/
def addNestedConsts (S : Env) : Nat → String → Nested → Env
  | 0, _, _ => S
  | _ + 1, _, [] => S
  | k + 1, pfx, (_, n, body) :: rest =>
    let q := pfx ++ "::" ++ n
    let S' := match classMethods? body with
      | some (_, _, _, _, _, cs, nst) => addNestedConsts (addClassConsts S q cs) k q nst
      | none => S
    addNestedConsts S' k pfx rest

/-- The constant members of a class body, or `[]` if the body is not one this checker reads.
Deliberately re-derived from `classMethods?` rather than passed in: `extendConsts` is called
from `Ctx.afterStmt`, which sees only the statement. -/
def bodyConsts (body : Expr) : List (String × Expr) :=
  match classMethods? body with
  | some (_, _, _, _, _, cs, _) => cs
  | none => []

/-! ### `private_constant` (tier 13d)

`private_constant :SECRET` does not change what the constant *is*; it changes who may name
it. `Box::SECRET` from outside raises `NameError`, while a bare `SECRET` inside a method of
`Box` still reads it. So the fact belongs on the *scoped read* rule and nowhere else, and it
is **precision rather than soundness** — `NameError` is outside this package's type-stuck
family, so a checker that ignored `private_constant` would still be sound and would certify
`Box::SECRET`, a program Ruby refuses to run. That is the whole reason this field exists.

It is a second syntactic pass over the class body rather than a component of
`classMethods?`'s tuple, because `splitMembers` drops the member (it declares nothing) and
`Ctx.afterStmt` is where the answer is needed. -/
mutual

def privNames : Expr → List String
  | .send none "private_constant" args none => (symNames? args).getD []
  | .seq es => privNamesAll es
  | _ => []

def privNamesAll : List Expr → List String
  | [] => []
  | e :: es => privNames e ++ privNamesAll es

end

/-- The absolute keys a class-or-module statement makes private. -/
def addPrivNames (P : List String) (owner : String) : List String → List String
  | [] => P
  | n :: ns => addPrivNames (constKeyIn owner n :: P) owner ns

def extendPrivConsts (P : List String) : Expr → List String
  | .class' n _ body => addPrivNames P n (privNames body)
  | .module' n body => addPrivNames P n (privNames body)
  | _ => P

/-- **Every name mixed in by this class body is a declared `module`.**

`Judge.classStmt`'s guard, and a soundness requirement rather than tidiness: `include` and
`extend` raise `TypeError` on anything that is not a `Module` (`include String` →
"wrong argument type Class (expected Module)"), and `TypeError` is inside the family. Without
this premise, `class P; include SomeClass; end; P.new.a_method_of_SomeClass` would dispatch
happily and certify a program that raises before it ever gets there.

A name the table does not know at all is also refused. That is stricter than Ruby, which is
happy to `include` a module declared in another file — but this judgment has no notion of
another file, and a name it cannot resolve is a name whose `isModule` it cannot check. -/
def allModules (C : CTable) (ns : List String) : Bool :=
  ns.all (fun n => match clsGet? C n with
    | some c => c.isModule
    | none => false)

/-! ### Method lookup, up the chain

`defGet?` finds a method declared *on* a class. `mroGet?` finds the one dispatch would
actually run, walking `super?`, and returns **which class it was found in** as well as the
method — because `super` needs the definition site, not the receiver's class (see
`Judge.superCall`). -/

/-- Look `m` up in each of these modules' **instance** methods, in order, and report which
module it was found in.

One function for both mixin directions, because both consult `.methods`: `include` makes a
module's instance methods instance methods of the class, and `extend` makes them methods of
the class *object*. Only the table consulted at the call site differs. -/
def mixinGet? (C : CTable) : List String → String → Option (String × Defn)
  | [], _ => none
  | mn :: ms, m =>
    match clsGet? C mn with
    | some c =>
      match defGet? c.methods m with
      | some d => some (mn, d)
      | none => mixinGet? C ms m
    | none => mixinGet? C ms m

/-- The bounded walk, **singleton dispatch only** (tier 10). `k` is a depth budget, not a
natural part of the algorithm: `CTable` is data, so nothing stops it describing a cycle
(`class A < B` and `class B < A` cannot both be declared in Ruby, but the table does not know
that). Exhausting the budget answers `none`, which — like `chk`'s fuel — can only cost
completeness.

Instance dispatch used to go through here too, with a `sing : Bool` switch; `prepend` moved it
to `mroList?`/`searchMro`, because a prepended module's "next" is the class itself and that
cannot be found by following `super?`. Singleton dispatch has no prepend form in this model, so
it kept the simpler walk. -/
def lookupUpS (C : CTable) : Nat → String → String → Option (String × Defn)
  | 0, _, _ => none
  | k + 1, n, m =>
    match clsGet? C n with
    | none => none
    | some c =>
      match defGet? c.smethods m with
      | some d => some (n, d)
      | none =>
      -- `extend M` puts *M's instance methods* in the class object's table (`Cls.extended`),
      -- searched reversed so a later `extend` wins.
      match mixinGet? C c.extended.reverse m with
      | some hit => some hit
      | none =>
        match c.super? with
        | none => none
        | some sn => lookupUpS C k sn m

/-! ### The MRO as a list (tier 10)

`prepend` is what forced this. Up to tier 8 instance dispatch could be a walk over `super?`,
because "the next place to look" was always reachable from where you were. A prepended module
breaks that: in `class C; prepend M; end` the entry after `M` is `C`, and `C` is not `M`'s
superclass — nothing about `M` names it. So the ancestor **order** has to be built once, as a
list, and both dispatch and `super` become searches over it.

Ruby's order for one class is `prepends ++ [self] ++ includes`, most recent mixin first, then
the same for its superclass. `mroList?` builds exactly that. -/

/-- The full method-resolution order of `n`, most specific first, or `none` if the walk leaves
the table (the same refusal `ancestorsUp` makes, and for the same reason). -/
def mroListUp (C : CTable) : Nat → String → Option (List String)
  | 0, _ => none
  | k + 1, n =>
    match clsGet? C n with
    | none => none
    | some c =>
      let here := c.prepends.reverse ++ (n :: c.includes.reverse)
      match c.super? with
      | none => some here
      | some sn => (mroListUp C k sn).map (fun rest => here ++ rest)

def mroList? (C : CTable) (n : String) : Option (List String) :=
  mroListUp C C.length n

/-- The first entry of an MRO that defines `m`, and which entry it was. -/
def searchMro (C : CTable) : List String → String → Option (String × Defn)
  | [], _ => none
  | e :: es, m =>
    match clsGet? C e with
    | some c =>
      match defGet? c.methods m with
      | some d => some (e, d)
      | none => searchMro C es m
    | none => searchMro C es m

/-- Everything **after** `x` in a list, or `none` if `x` is not in it.

This is what `super` means, stated as a list operation: not "the superclass of where I was
declared" (which prepend makes wrong) but "keep going from where I was found". -/
def afterInMro : List String → String → Option (List String)
  | [], _ => none
  | e :: es, x => if e == x then some es else afterInMro es x

/-- Instance-method lookup: the first entry of `n`'s MRO that defines `m`, and where it was
found — because `super` needs the definition site, not the receiver's class (see
`Judge.superCall`). -/
def mroGet? (C : CTable) (n m : String) : Option (String × Defn) :=
  match mroList? C n with
  | some l => searchMro C l m
  | none => none

/-- Singleton-method lookup. Ruby inherits class methods down the chain too, so this is the
other walk over the other tables. -/
def smroGet? (C : CTable) (n m : String) : Option (String × Defn) :=
  lookupUpS C C.length n m

/-- `n` as something **allocatable**: the table entry, unless it is a module. See
`Cls.isModule` for why the refusal is a soundness requirement rather than tidiness. -/
def instClsGet? (C : CTable) (n : String) : Option Cls :=
  match clsGet? C n with
  | some c => if c.isModule then none else some c
  | none => none

/-! ### Is this name an exception class? (tier 16b)

A builtin exception name, or a declared class whose superclass chain reaches one. Fuel-bounded
for `nestedClasses`' reason — a `Cls.super?` walk has no structural measure — and running out
answers `false`, which is a rejected `raise` rather than a wrong one. -/
def excNameUp (C : CTable) : Nat → String → Bool
  | 0, _ => false
  | k + 1, n =>
    if excCls? n then true
    else
      match clsGet? C n with
      | some c => match c.super? with
                  | some sn => excNameUp C k sn
                  | none => false
      | none => false

def excName? (C : CTable) (n : String) : Bool := excNameUp C 32 n

/-- The class names a `rescue` clause lists, or `none` if any of them is not a bare constant.
`rescue foo()` is not read, so the whole `begin` is not typed. -/
def rescueClasses? : List Expr → Option (List String)
  | [] => some []
  | .const n :: es => (rescueClasses? es).map (fun ns => n :: ns)
  | _ => none

/-- The environment a `rescue … => e` binding contributes, prepended to the handler's.

**Only a single builtin exception class may be bound**, and that is a restriction rather than a
principle: `.cls n` for an `ExcCls` name is a type this judgment can say something about
(`PrimSig.excMessage`), whereas a user exception would want `.inst n .ivar0` and a rescue over
*several* classes would want their union. Neither is hard; no rung asks. A clause with no
binding is always fine. -/
def rescueBind? (names : List String) : Option (TargetKind × String) → Option Env
  | none => some []
  | some (.lvar, x) =>
    match names with
    | [n] => if excCls? n then some [(x, .cls n)] else none
    | _ => none
  | some _ => none

/-- `n`'s constructor: `initialize`, found by the ordinary walk, but only for something that
can be allocated at all. Bundled into one lookup so the `newInst` rule's premise count did
not change when tier 8 added the module check. -/
def ctorGet? (C : CTable) (n : String) : Option (String × Defn) :=
  match instClsGet? C n with
  | some _ => mroGet? C n "initialize"
  | none => none

end Ratchet
