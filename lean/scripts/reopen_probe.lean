import RubyCore.PreludeBoot
import RubyCore.HeapCert

/-!
**Which class names may go in `reopenableClasses`** (L189), decided rather than
argued. Every row of that table is a promise `ClassOk` keeps, and since L189 it is
**seven** clauses per name — the three `enterClassBody` tests (present, a class, not
a module), uniqueness at the name, head-of-chain, `NoShadowBefore`, and the two the
`.const` read rule added (a legal receiver, and `Object` as sole owner). This decides
all seven for every plausible candidate, so widening the table costs a `decide`.

The refusals are the interesting output, and each names a real fact:

* `Float` owns `NAN` and `INFINITY`, so something in front of `Object` on its chain
  owns a constant — `NoShadowBefore` fails;
* `Array`, `Hash` and `Range` lose **sole ownership**, because `T::Array`, `T::Hash`
  and `T::Range` own those names too. That is L177's `T` collision arriving as a
  refusal rather than as a hazard;
* `Regexp` is one of the two ids `invoke` dispatches a singleton family from (L106),
  which `classRecv` excludes;
* `Comparable`, `Kernel` and `T` are modules.

    lake env lean --run scripts/reopen_probe.lean     -- a report; read the table
-/

open RubyCore
open RubyCore.Interp
def cands : List String :=
  ["Object","String","Integer","Float","Array","Hash","Symbol","Regexp","Range",
   "Proc","Exception","NilClass","TrueClass","FalseClass","Comparable","Kernel","T"]
def main : IO UInt32 := do
  match Prelude.boot with
  | .error e => IO.eprintln s!"boot failed: {e}"; return 1
  | .ok mp =>
    let h := mp.heap
    IO.println "name        ok?  reason"
    for nm in cands do
      match constOwn h Boot.objectId nm with
      | some (.ref k) =>
        match h.classPayload? k with
        | some cp =>
          let mod := cp.isModule
          let nmok := className h k == nm
          let uniq := (List.range h.objs.size).all fun j =>
            !((h.classPayload? j).isSome && className h j == nm) || j == k
          let head := (ancestors h k).head? == some k
          let nsb := noShadowBeforeB h k
          let idok := k != Boot.regexpId && k != Boot.mathId
          let sole := (List.range h.objs.size).all fun j =>
            !((h.classPayload? j).isSome && j != Boot.objectId) || (constOwn h j nm).isNone
          let ok := !mod && nmok && uniq && head && nsb && idok && sole
          IO.println s!"{nm}  {ok}  module={mod} name={nmok} uniq={uniq} head={head} noShadow={nsb} idok={idok} sole={sole}"
        | none => IO.println s!"{nm}  false  constant is not a class"
      | _ => IO.println s!"{nm}  false  not a class constant of Object"
    return 0
