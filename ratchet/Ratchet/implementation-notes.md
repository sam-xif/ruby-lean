
## Clink 29 (2026-09-01) — tier 13c: `M::X`, and a premise that is not decoration: 133 → 135

`const-scoped-read`, `const-scoped-assign`. Two rules (`constPath`, `cpathAsgn`), one new
`extendConsts` case, and the interest is entirely in one premise.

### A scoped read is easier than a bare one, except for the base

`constEnv` has to *search* — a bare `SIZE` means `Box::SIZE` or the top-level `SIZE`
depending on where it is written, so `constGet?` walks a path list. `M::X` says where to
look, so `constPath` is a single `envGet?` at the absolute key. That much is a simplification.

What is new is that `M::X` **evaluates `M`**, and after `M = 5` it evaluates to something that
is not a namespace: `5::X` raises `TypeError` ("5 is not a class/module"). So the rule judges
the base, at `.clsOf owner`:

```
Judge κ Γ I (.const owner) (.clsOf owner) Γ I → envGet? κ.consts (constKeyIn owner n) = some τ
  → Judge κ Γ I (.cpath (some (.const owner)) n) τ Γ I
```

That premise does real work, and controls (p13h)/(p13i) prove it: `module M; X = 1; end;
M = 5; M::X` leaves a perfectly good `"::M::X"` in the constant table, and the program raises
anyway. Both controls print as **sound** rejections. The mechanism is clink 27's disjointness
premise paying off a second time — after the `casgn`, the only rule that types `.const "M"` is
`constEnv`, which answers `.int`, and `constCls` is blocked.

### Why the base is *also* restricted syntactically

`constPath`/`cpathAsgn` are stated at the syntax `.cpath (some (.const owner)) n`, not at an
arbitrary base expression that happens to judge as `.clsOf owner`. The reason is agreement
with `extendConsts`, which is a **function of syntax** (`Ctx.afterStmt` sees a statement, not
a judgment) and therefore has to match the base by pattern to know which key a write lands on.
Keeping the rule at the same shape means the two cannot disagree. A base the pattern does not
read binds nothing, which is conservative.

Worth noting the one thing this does *not* need: `.const owner` cannot judge as
`.clsOf other` for a different name — all three `const` rules answer `.clsOf n` for the same
`n` they were asked about — so the syntactic owner and the judged owner are the same string by
construction, and no premise has to say so.

### `M::X = 4` is `casgn`'s twin, and lands on the same key

`cpathAsgn` types the statement at its right-hand side and binds nothing; `extendConsts`
binds `constKeyIn owner n`, which is the *same key* a `casgn` inside `module M`'s body would
have used. So a later read cannot tell how the constant got there — which is correct, because
neither can Ruby. `r142` is that program, and its module body is `nil`: the module
contributes nothing to the table itself.

### What is left in tier 13, and what it is really about

Four rungs, and three of them are the same missing thing rather than three things:

- `const-scoped-nested` (`Outer::Inner::Y`), `const-scoped-class-ref` (`M::Box.new`) and
  `const-class-of-const` all need a **class or module declared inside another one** to enter
  the class table at all. `classMethods?` rejects a nested `class`/`module` member today, and
  `extendClasses` does not recurse — so `M::Box` names nothing. That is a change to the
  *class* namespace (qualified `Cls.name`s, and bare class names resolved lexically), not to
  the constant one, and it is the next clink.
- `const-attr-reader`, `const-alias`, `const-private-constant` are three more class-body
  member kinds, each declaring a method (or hiding a constant) rather than assigning one.

### State

**135 rungs of 232**, tier 13 at 6/13. 135/135 cross-checked, 101/101 controls rejected (two
new, both sound rejections), corpus agreement 232/232, axiom-clean.
