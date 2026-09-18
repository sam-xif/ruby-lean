import Ratchet.Static.Classes

/-!
# `Ratchet/Static/Ancestors.lean`

The **ancestor chain** and what is decided from it: `ancestors?`, the builtin chains,
`isAAnswer` (tier 12's `is_a?` executed at type level), the two dispatch-admissibility
guards, and `mergeCls`.
-/

namespace Ratchet

/-! ### The ancestor chain (tier 12)

`mroGet?` answers "which class would dispatch run this method from". `is_a?` asks a
different question — "is this class *among* those" — and needs the chain itself.

**Why the chain a declared class produces is complete**, which is the whole soundness
argument for answering `is_a?` **negatively**: a class enters `CTable` only via
`extendClasses`, which uses `classMethods?`, which is `mapM clsMember?` over the body — and
`clsMember?` reads only `def` and `def self.`. So a class body containing `include M`,
`extend M` or `prepend M` makes `classMethods?` answer `none`, the class never enters the
table, and `chk`'s `.class'` arm answers `none` for the whole program. Therefore *every*
class in this table has no mixins, and its real ancestors are exactly its declared chain
plus `Object`/`Kernel`/`BasicObject`.

That argument is load-bearing and fragile in a specific way: whichever tier gives
`include` a rule (tier 10) must revisit `isAAnswer`, because at that moment a class in the
table can have an ancestor the chain does not name. -/

/-- Names every object's chain ends with, and the reason `isANo` has to exclude them: `n`'s
declared chain stops at a class with no `super?`, whose real superclass is `Object`. -/
def rootAncestors : List String := ["Object", "Kernel", "BasicObject"]

/-- The ancestors contributed by a list of included modules — **one level only**, and `none`
if any of them mixes something in or has a superclass of its own.

That refusal is the soundness point (tier 10). `isAAnswer` answers `is_a?` *negatively* off
this chain, so an ancestor the chain fails to name is an unsoundness, not an imprecision. A
module that itself includes another module has an ancestor this function would omit, so instead
of omitting it the whole chain becomes unknown. Every rung includes only flat modules; making
this recursive is a fuelled walk nobody has needed. -/
def mixinAncestors? (C : CTable) : List String → Option (List String)
  | [] => some []
  | mn :: ms =>
    match clsGet? C mn with
    | none => none
    | some c =>
      if c.includes.isEmpty && c.super?.isNone then
        (mixinAncestors? C ms).map (fun rest => mn :: rest)
      else none

/-- The declared ancestor chain of `n`, most specific first, or `none` if the walk leaves the
table — an undeclared superclass means the chain is *unknown*, not empty, and answering
`is_a?` off a truncated chain would be unsound (`class Dog < StandardError` really is a
`StandardError`). Budgeted like `lookupUp`, for the same reason. -/
def ancestorsUp (C : CTable) : Nat → String → Option (List String)
  | 0, _ => none
  | k + 1, n =>
    match clsGet? C n with
    | none => none
    | some c =>
      -- Tier 10: a class's ancestors include the modules mixed into it. Omitting them would
      -- make `isAAnswer` answer `is_a?(SomeIncludedModule)` with a *wrong* `some false`.
      match mixinAncestors? C (c.prepends ++ c.includes) with
      | none => none
      | some _ =>
        -- The ancestor *set* is exactly the MRO's entries, and `mroListUp` already builds them
        -- in order -- so once the mixins are known to be flat, this walk and the MRO agree.
        -- Kept separate from `mroList?` only because a `none` here means "chain incomplete",
        -- which is a different claim from "dispatch found nothing".
        match c.super? with
        | none => some (c.prepends.reverse ++ (n :: c.includes.reverse))
        | some sn =>
          (ancestorsUp C k sn).map (fun rest =>
            (c.prepends.reverse ++ (n :: c.includes.reverse)) ++ rest)

def ancestors? (C : CTable) (n : String) : Option (List String) :=
  ancestorsUp C C.length n

/-- **The complete ancestor list of the class a builtin `Ty`'s values belong to**, most
specific first, modules included — checked against CRuby's `.ancestors`. Complete is the
operative word: this table is what lets `is_a?` be answered *negatively* for a builtin
receiver, so a missing entry would be an unsoundness rather than an imprecision.

`none` for every `Ty` whose values are not exactly one builtin class's instances:
`.bool` (`true` and `false` are instances of *two* classes, so `is_a?(TrueClass)` has no
single answer), `.union`/`.nilable` (handled compositionally by `isATy`/`notATy`), `.any`,
`.never`, `.inst` (a declared class — `ancestors?`'s job), `.clsOf`/`.clos` (`Class` and
`Proc`; total, but no rung asks and each row is a claim to check), and `.cls n` for any `n`
other than the two builtin classes this `Ty` actually produces. -/
def builtinAncestors : Ty → Option (List String)
  | .int => some (["Integer", "Numeric", "Comparable"] ++ rootAncestors)
  | .float => some (["Float", "Numeric", "Comparable"] ++ rootAncestors)
  | .nilT => some ("NilClass" :: rootAncestors)
  | .sym => some (["Symbol", "Comparable"] ++ rootAncestors)
  | .cls "String" => some (["String", "Comparable"] ++ rootAncestors)
  | .cls "Hash" => some (["Hash", "Enumerable"] ++ rootAncestors)
  -- **`.arrayOf`/`.hashOf` are deliberately absent**, and the reason is a denotation fact
  -- rather than a table gap: their `denM` arms read the *payload* (`arrElems?`/`hshEntries?`)
  -- and say nothing about the object's class, so a value of type `.arrayOf τ` need not be an
  -- `Array` as far as the denotation is concerned — and a **negative** `is_a?` answer about it
  -- would be a claim this judgment cannot make. Dropping the rows costs only precision, and
  -- only in one direction: the *positive* answer is what `isATy` keeps the type for, and
  -- `isAAnswer = none` keeps it too. (`Ty.arrayOf`'s docstring is where the class fact would
  -- have to be added if a rung ever wants the row back; see `found-issues.md` §F12 for the
  -- shape such a change takes.)
  | _ => none

/-- **Is every class in this chain free of mixins, as far as the context knows?**
`found-issues.md` §F9's guard. A chain is a list of *names*, and `isAAnswer` answers `is_a?`
negatively off it — so a name in it whose class the context reopens with an `include` or a
`prepend` has an ancestor the chain does not mention, and the negative answer is wrong. This
does not have to walk: it is the mixin lists of the chain's own members that matter, and
`mixinAncestors?` has already refused any chain whose *modules* are themselves impure. -/
def mixinFreeChain (C : CTable) (ch : List String) : Bool :=
  ch.all (fun n => match clsGet? C n with
    | none => true
    | some c => c.includes.isEmpty && c.prepends.isEmpty)

/-- **Does any declared class descend from `n`?** — and the answer `isAAnswer` needs is "no".

The second half of §F9's guard, and it is about a different direction of the same gap.
`mixinFreeChain` asks whether the classes *in* a chain gained ancestors; this asks whether a
class was declared *below* the chain's base. Both break the negative answer, and for `.cls`/
`.arrayOf`/`.hashOf` types it is this one that matters: those denote **is-a**
(`Denote/Ty/Den.lean`), so a value of type `.cls "String"` may be an instance of a declared
subclass, whose own name is in *its* ancestors and in no static chain.

Measured at the booted machine before the guard was written: no boot class descends from any of
`Integer`, `Float`, `NilClass`, `Symbol`, `String`, `Hash` or `Array`. So the *heap* side of
the claim needs only the context to be quiet, which is what this checks.

A chain that leaves the table counts as "might descend", for `ancestorsUp`'s reason. -/
def noDeclaredBelow (C : CTable) (n : String) : Bool :=
  C.all (fun c =>
    c.name == n ||
    (match ancestors? C c.name with
     | some ch => !(ch.contains n)
     | none => false))

/-- The two conditions a **negative** `is_a?` answer off a static chain needs: nothing was
mixed into the chain, and nothing was declared below its base. -/
def isANoOk (C : CTable) (ch : List String) : Bool :=
  mixinFreeChain C ch &&
  (match ch.head? with
   | some base => noDeclaredBelow C base
   | none => false)

/-- `is_a?(cn)` on a value of type `τ`: `some true` when **every** value of `τ` answers
`true`, `some false` when every value answers `false`, and `none` when this judgment cannot
tell — which is the answer for `.any`, `.bool`, a `.cls` outside `builtinAncestors`, and a
declared class whose chain leaves the table.

Not defined on `.union`/`.nilable`: those are not a single class, and treating them here
would hide the fact that a union's answer is per-member. `isATy`/`notATy` decompose them. -/
def isAAnswer (C W : CTable) (cn : String) : Ty → Option Bool
  | .inst n _ => (ancestors? C n).bind (fun ch =>
      if (ch ++ rootAncestors).contains cn then some true
      -- `ancestors?` checked the *declared* chain's mixins; `rootAncestors` is appended
      -- blindly, so `class Object; include M; end` is the case this guard covers
      else if mixinFreeChain W rootAncestors then some false else none)
  -- **§F9**: the builtin chain is a *static table*, and `class Integer; include M; end` really
  -- does make `5.is_a?(M)` true; and the type denotes **is-a**, so a declared subclass's
  -- instance is one of its values. So *neither* answer is available at a context that has
  -- disturbed the chain.
  --
  -- The positive answer would survive on its own (a mixin only adds ancestors, and a subclass
  -- keeps them) and an earlier version of this guard kept it. It is gated anyway, because
  -- proving the positive half without `isANoOk`'s no-subclasses clause needs **transitivity of
  -- the ancestor walk** — a general fact about `ancestors` that nothing on file proves, and one
  -- that a `StateOk` component has no business assuming. Gating costs precision only where a
  -- program mixes into or subclasses a core class, and buys the exactness the proof uses.
  | τ => (builtinAncestors τ).bind (fun ch =>
      if isANoOk W ch then (if ch.contains cn then some true else some false) else none)

/-- **Does any *declared* class descend from `n` and redefine `m`?** — `found-issues.md`
§F11's guard, and the answer it wants is "no".

`Ty.cls n`'s denotation is `is_a?`, deliberately: `rescue StandardError => e` binds whatever
was raised, and that is normally an instance of a **subclass**. So a `PrimSig` row at a
nominal receiver — `Exception#message` is the one the target uses — is a claim about a method
the receiver's *actual* class resolves, and a declared subclass that redefines the name
resolves it differently. `PrimSig` cannot see the class table (that is what makes it a table
rather than a judgment), so the check lives here and is a premise of `Judge.prim`.

Precise rather than structural, in the same way `isADispatchOk` is: it asks whether a class
that really descends from `n` really declares `m`, not whether the program mentions the name
anywhere. `ancestors?` answering `none` — a chain that leaves the table — counts as "might
descend", because a class whose superclass is unknown might be under `n`.

**`valueClsNames` is exempt, and the exemption is an argument, not a shortcut.** A value gets a
nominal type *strictly larger than its class* in exactly one place in this judgment:
`rescueBind?`, because `rescue C => e` binds whatever was raised and Ruby lets that be a
subclass. Every other `.cls n` — the four names below, which are all `PrimSig` mentions — is
produced by a literal or by a builtin and is therefore an instance of exactly `n` (the same
exactness-by-construction argument §F8 records, and subject to the same caveat). Exempting them
is what keeps `constLitTy?_sound` unconditional: that theorem types `"s".freeze` in **any**
context, so a premise it cannot discharge would have to be pushed onto every one of its
callers, none of which has a class table to check. -/
def valueClsNames : List String := ["String", "Hash", "Regexp", "MatchData"]

def primDispatchOk (C : CTable) (σ : Ty) (m : String) : Bool :=
  match σ with
  | .cls n =>
    if valueClsNames.contains n then true
    else
      C.all (fun c =>
        (c.methods.find? (·.name == m)).isNone ||
        (match ancestors? C c.name with
         | some ch => !(ch.contains n)
         | none => false))
  | _ => true

/-- **`recv.is_a?(C)` really reaches `Object#is_a?`.**

`is_a?` is total on every object and never raises for a `Module` argument, so the only way
`x.is_a?(C)` can be type-stuck is a **user-written override** — and unlike `nil?` (see
`NilQSafe`, which sidesteps the problem by refusing `.inst` outright) `is_a?` *must* admit
`.inst`, because narrowing a union of program-declared classes is the whole point of
`narrow-union-subclass`.

So the guard is precise instead of structural: for every `.inst n` component of the receiver
type, `n`'s MRO must not define `is_a?`. That is a lookup this judgment already has, and it
is why this rule takes the class table where `PrimSig` rows cannot — which is also why
`is_a?` is a `Judge` rule rather than a `PrimSig` row.

`.any` is refused for `EqSafe`'s reason (a rule no rung can falsify), `.clos` because `Proc`
does respond to `is_a?` but no rung asks, and `.never` because the strictness rules
(`primNever`) get there first. -/
def isADispatchOk (C : CTable) : Ty → Bool
  | .inst n _ => (mroGet? C n "is_a?").isNone
  | .union σ τ => isADispatchOk C σ && isADispatchOk C τ
  | .nilable ρ => isADispatchOk C ρ
  | .any | .clos _ _ _ | .never | .sameAs _ _ => false
  | _ => true

/-- **Adding a class declaration to the table, merging if the name is already there.**

Tier 10's `metaprog-class-reopening`. Ruby lets a `class` statement *reopen* an existing
class, and the methods accumulate:

```ruby
class Foo; def a; 1; end; end
class Foo; def b; 2; end; end
Foo.new.a + Foo.new.b        # both work
```

This function used to prepend unconditionally, and `clsGet?` is a `find?`, so the second
statement **shadowed** the first: `Foo` had `b` and not `a`, and the program was untypeable.
Merging is the honest model, and note it is not a special case for "metaprogramming" — a
reopened class is the same thing a class always was, and the old behaviour was simply wrong
about it rather than conservative.

Three details, each a decision:

- **The later body's methods go first**, because `defGet?` is a `find?`: a redefinition must
  win over the definition it replaces, which is what Ruby does.
- **The superclass is the later one if it names one, else the earlier's.** `class Foo` with no
  `< Bar` does not erase an inherited superclass. (Ruby *rejects* a reopening that names a
  *different* superclass; this function would silently take the later, which no rung
  exercises.)
- **The merged entry is prepended rather than replacing the old one in place.** The stale entry
  is unreachable — `clsGet?` finds the new one first — and this keeps the function a one-liner
  instead of needing a list update. It does grow `C`, which only makes `mroGet?`/`ancestors?`'s
  `C.length` budget more generous. -/
def mergeCls (C : CTable) (c : Cls) : CTable :=
  match clsGet? C c.name with
  | none => c :: C
  | some old =>
    -- **Named fields, not positional.** `Cls` now has eight of them, three of which are
    -- `List String`, and a positional `⟨…⟩` silently swapped `includes` with `prepends` when
    -- tier 10 added the third -- which *validated* `metaprog-prepend` for the wrong reason
    -- (dispatch found `Person#speak` instead of `Logger#speak`, so the `zsuper` in the module
    -- was never reached). Named fields make that class of mistake a compile error.
    { name := c.name,
      super? := c.super?.orElse (fun _ => old.super?)
      methods := c.methods ++ old.methods
      smethods := c.smethods ++ old.smethods
      isModule := c.isModule
      -- Mixins accumulate the same way, and with the later body's *later* in the list, because
      -- every mixin list is searched reversed: a module mixed in by a reopening wins over one
      -- mixed in earlier.
      includes := old.includes ++ c.includes
      prepends := old.prepends ++ c.prepends
      extended := old.extended ++ c.extended } :: C

end Ratchet
