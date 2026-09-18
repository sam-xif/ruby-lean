import Ratchet.Static.Ctx

/-!
# `Ratchet/Static/Iterators.lean`

Tier 9c's **builtin iterators**: `IterSig`, a builtin whose signature mentions a block.
`PrimSig` cannot state one, because an iterator's result depends on what its block returns.
-/

namespace Ratchet

/-! ## Tier 9c: the builtin iterators

The last piece of tier 9, and a genuinely new *kind* of rule: a builtin whose signature
mentions a **block**. `PrimSig` cannot state one — it relates a receiver type, a name and a
list of argument types to a result, and an iterator's result depends on what its *block*
returns, which is not known until the block's body has been typed.

So the signature is split in two, and the split is the design:

- **`iterParams?`** answers "given the receiver's element type and the call's arguments, at
  what types does the block's parameter list get bound?" — the information needed *before*
  typing the body.
- **`iterResult?`** answers "given that the body came back at `ρ`, what does the call
  return?" — after.

`IterSig` is the relation that joins them, with one constructor per iterator, and
`iterSig?_sound` is the lemma that the two functions only ever agree with it.

**The five iterators differ in exactly the way that matters**, which is why a single "block
rule" would get most of them wrong:

| method | block params | result |
|---|---|---|
| `each` | `[elem]` | the **receiver** |
| `map` | `[elem]` | `arrayOf` (block's return) |
| `select` | `[elem]` | `arrayOf elem` (a subset of the receiver) |
| `sort_by` | `[elem]` | `arrayOf elem`, **if** the block's return is comparable |
| `inject(init)` | `[α, elem]` | `α`, **if** the block returns `α` |

The two side conditions are not decoration:

- **`sort_by` needs `Comparable ρ`**, and the failure mode is not the obvious one. It is not
  that some key type lacks `<=>`: `nil <=> nil` is `0`, so `["a","b"].sort_by { |s| nil }`
  sorts fine. What raises is a key type whose `<=>` is not total **across its own values** —
  a union (`[1, "a"].sort_by { |x| x }` raises `ArgumentError: comparison of Integer with
  String failed`, *inside* the family) or a user class inheriting `Object#<=>`, which answers
  `0` for identical objects and `nil` otherwise (`[Z.new, Z.new].sort_by { |x| x }` raises).
  So an unconstrained `sort_by` row would be unsound, unlike `select`'s — a `select` block's
  result is only ever tested for truthiness, which never raises.
- **`inject`'s accumulator must be a fixed point.** `α` is the type of the initial value, the
  block is typed with its first parameter at `α`, and the body is *required to come back at
  `α`* — because the block's result is the next iteration's accumulator. A block that returns
  something else really does change the accumulator's type between iterations, and no single
  `Ty` describes it. This is the same assume-then-verify shape as `Judge.callDef`'s recursion,
  with the initial value playing the part of the candidate. -/

/-- Receivers of `<=>` for which `sort_by`'s comparison is total. One row per type this
`Ty` can actually produce a homogeneous array of; a `union` is deliberately absent, because
`[1, "a"].sort_by { |x| x }` really does raise `ArgumentError`. -/
inductive Comparable : Ty → Prop
  | int : Comparable .int
  | float : Comparable .float
  | str : Comparable (.cls "String")

/-- `IterSig m elem args βs ρ res`: sending `m` with argument types `args` and a block to an
`arrayOf elem` binds the block's parameters at `βs`; if the block's body then has type `ρ`,
the call's result is `res`. See the section docstring for the table and the two side
conditions. -/
inductive IterSig : String → Ty → List Ty → List Ty → Ty → Ty → Prop
  /-- `Array#each { |x| … } → self`. The block's return value is discarded entirely. -/
  | each {τ ρ : Ty} : IterSig "each" τ [] [τ] ρ (.arrayOf τ)
  /-- `Array#map { |x| … } → Array` of whatever the block returned. -/
  | map {τ ρ : Ty} : IterSig "map" τ [] [τ] ρ (.arrayOf ρ)
  /-- `Array#select { |x| … } → Array` of the *receiver's* elements. The block's result is
      only tested for truthiness, and truthiness never raises, so `ρ` is unconstrained. -/
  | select {τ ρ : Ty} : IterSig "select" τ [] [τ] ρ (.arrayOf τ)
  /-- `Array#sort_by { |x| … } → Array` of the receiver's elements, ordered by the block's
      results — which are compared with `<=>`, hence `Comparable`. -/
  | sortBy {τ ρ : Ty} : Comparable ρ → IterSig "sort_by" τ [] [τ] ρ (.arrayOf τ)
  /-- `Array#inject(init) { |acc, x| … } → α`, where `α` is `init`'s type and the block is
      required to *return* `α`. An empty receiver returns `init`, which is why the result is
      `α` rather than the block's return type — they are the same type by the premise. -/
  | inject {τ α : Ty} : IterSig "inject" τ [α] [α, τ] α α
  /-- **`inject` over a provably empty receiver** (tier 14b), where the block's return type is
      unconstrained.

      `arrayOf .never` says "every element of this array does not return a value", and `.never`
      is uninhabited — so an array of that type **has no elements**, the block never runs, and
      the result is the seed whatever the block would have returned. That is the whole argument,
      and it is about the *receiver's element type*, not about `ρ`: keying it on `ρ = .never`
      would be a different and much weaker claim.

      What needs it: `def total(*ns); ns.inject(0) { |a, b| a + b }; end; total()`. A rest
      parameter with no arguments left is `arrayOf (elemTy []) = arrayOf .never`, so the block
      is judged with `b : .never`, `a + b` is `.never` by strictness, and the general `inject`
      row's `ρ = α` fails on a call that cannot go wrong. -/
  | injectEmpty {α ρ : Ty} : IterSig "inject" .never [α] [α, .never] ρ α
  -- ### Tier 17's iterators
  /-- `xs.any? { … }` / `xs.all? { … }` → `Bool`. The block's result is only tested for
      truthiness, which never raises, so `ρ` is unconstrained — `select`'s reason. -/
  | anyP {τ ρ : Ty} : IterSig "any?" τ [] [τ] ρ .bool
  | allP {τ ρ : Ty} : IterSig "all?" τ [] [τ] ρ .bool
  /-- `xs.each_with_index { |v, i| … }` → self. The **first two-parameter iterator whose second
      parameter is not an accumulator**: `inject` binds `[α, τ]`, this binds `[τ, .int]`, and the
      `.int` is the only thing in the table that comes from neither the receiver nor the
      arguments. -/
  | eachWithIndex {τ ρ : Ty} : IterSig "each_with_index" τ [] [τ, .int] ρ (.arrayOf τ)
  /-- `xs.flat_map { … }` → the concatenation, so the block must return an **array** and the
      result's element type is that array's. Ruby also accepts a non-array return (it is
      included as-is); that shape has no row, because the result would be a union of two element
      types and nothing consumes one. -/
  | flatMap {τ σ : Ty} : IterSig "flat_map" τ [] [τ] (.arrayOf σ) (.arrayOf σ)
  /-- `xs.filter_map { … }` → the block's **truthy** results, so the element type is
      `truthyTy ρ` — tier 12's refinement used on a result rather than in a branch, and the
      second row (with `compact`) whose result type is computed by one. Note it removes `false`
      as well as `nil`, which is why `truthyTy` rather than `nonNilTy`. -/
  | filterMap {τ ρ : Ty} : IterSig "filter_map" τ [] [τ] ρ (.arrayOf (truthyTy ρ))
  /-- `xs.find { … }` → an element **or nil**, because nothing may match. `ρ` unconstrained for
      `select`'s reason. -/
  | findFirst {τ ρ : Ty} : IterSig "find" τ [] [τ] ρ (mkNilable τ)

end Ratchet
