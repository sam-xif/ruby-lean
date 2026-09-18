import Ratchet.Static.Ancestors

/-!
# `Ratchet/Static/Nested.lean`

**Nested namespaces** (`nestedClasses`, `mergeAll`, `extendClasses`) and `Frame`, the
description of the activation a method body is judged inside — which is what `super` reads
and what `selfTy` cannot answer.
-/

namespace Ratchet

/-! ### Nested namespaces (tier 13e)

`module M; class Box; … end; end` gives a class whose name **is** `"M::Box"` — that is what
CRuby's `Box.name` answers, and matching it means the `CTable` key, `Ty.clsOf` and `Ty.inst`
all agree with the runtime rather than with a convention this package invented.

The recursion is **fuel-bounded**, and unlike `chk`'s fuel this one bounds *breadth as well as
depth*: `nestedClasses` spends a unit per nested declaration visited in either direction. The
reason is termination — the nested bodies come out of `classMethods?`, which Lean cannot see
as returning subterms of its argument, so there is no structural measure to recurse on. It is a
completeness knob like every other fuel here: running out drops a table entry, and a dropped
entry means a later use of that class finds nothing and is rejected.

`nestFuel` is generous for a source file (the deepest nesting in the target is three, with
tens of siblings) and finite, which is all the kernel needs. -/
def nestFuel : Nat := 512

/-- Every class-or-module entry a nested declaration list contributes, with names qualified by
`pfx`. Flat, so the caller folds `mergeCls` over it — which is what makes a *reopened* nested
class merge with its earlier definition exactly as a top-level one does. -/
def nestedClasses : Nat → String → Nested → List Cls
  | 0, _, _ => []
  | _ + 1, _, [] => []
  | k + 1, pfx, (isMod, n, body) :: rest =>
    let q := pfx ++ "::" ++ n
    (match classMethods? body with
     | some (ms, sms, incs, exts, preps, _, nst) =>
       { name := q, super? := none, methods := ms, smethods := sms, isModule := isMod,
         includes := incs, prepends := preps, extended := exts }
         :: nestedClasses k q nst
     | none => []) ++ nestedClasses k pfx rest

def mergeAll (C : CTable) : List Cls → CTable
  | [] => C
  | c :: cs => mergeAll (mergeCls C c) cs

/-- The nested declarations of a class body, or `[]` if the body is not one this checker
reads — `bodyConsts`'s twin, and re-derived from `classMethods?` for the same reason. -/
def bodyNested (body : Expr) : Nested :=
  match classMethods? body with
  | some (_, _, _, _, _, _, nst) => nst
  | none => []

def extendClasses (C : CTable) : Expr → CTable
  | .class' n sup body =>
    match classMethods? body with
    | some (ms, sms, incs, exts, preps, _, _) =>
      -- Tier 13e: `mergeAll … (nestedClasses …)` is the only addition, and it is the same in
      -- both arms and in `module'` below: whatever this statement declares, its nested
      -- declarations are declared with it, under its name as prefix.
      match sup with
      | none =>
        mergeAll (mergeCls C
          { name := n, super? := none, methods := ms, smethods := sms, isModule := false
            includes := incs, prepends := preps, extended := exts })
          (nestedClasses nestFuel n (bodyNested body))
      | some (.const sn) =>
        mergeAll (mergeCls C
          { name := n, super? := some sn, methods := ms, smethods := sms, isModule := false
            includes := incs, prepends := preps, extended := exts })
          (nestedClasses nestFuel n (bodyNested body))
      -- A superclass expression that is not a bare constant (`class C < foo()`) is not
      -- read, so the class does not enter the table and nothing using it is typed.
      | some _ => C
    | none => C
  -- Tier 8. A module is a `Cls` with no superclass and the module flag set; the body is read
  -- by the same `classMethods?`, so `def self.foo` lands in `smethods` and `M.foo` is
  -- `callSMethod` with nothing added.
  | .module' n body =>
    match classMethods? body with
    | some (ms, sms, incs, exts, preps, _, _) =>
      mergeAll (mergeCls C
        { name := n, super? := none, methods := ms, smethods := sms, isModule := true
          includes := incs, prepends := preps, extended := exts })
        (nestedClasses nestFuel n (bodyNested body))
    | none => C
  | _ => C

/-- Where the currently-executing method was **found** — which is not the same as the class
of the receiver, and `super` is the reason the distinction has to be recorded.

`Triangle#initialize` calls `super(3)`; the parent to delegate to is the superclass of
*`Triangle`*, the class the running method was declared in, and if that method had itself
been inherited from somewhere higher the answer would differ. `selfTy` names the receiver's
class and cannot answer this. The method name is here for the same reason: `super` calls the
method of the same name. -/
structure Frame where
  /-- The class of the object the running method is *running on* (tier 10). `super` needs it
      because a prepended module's "next" is the class that prepended it, and that is only
      findable in the **receiver's** MRO — `defClass` alone cannot name it.

      For a singleton method body this is the class object's own name, which is harmless: a
      `super` there would search instance methods and find nothing. -/
  recvClass : String
  /-- Where the running method was **found** — which for a prepended or included module is that
      module, not the receiver's class. `super` continues from just after it. -/
  defClass : String
  methName : String

end Ratchet
