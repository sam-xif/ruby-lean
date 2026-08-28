import RubyCore.Types.SlotClaim
import RubyCore.Types.SlotWalk

/-!
# The two measured blockers, cleared — `#guard`ed

`docs/semantics/slot-frame.md` §1 measured two consequences of `declaresName`'s
name-globality on the judge slice, and §7 claims both are "one `compose` away".
This file is that claim, executable. Ids are symbolic stand-ins for the slice's
classes; nothing here reads a heap, because neither blocker was ever a heap
fact — both were artifacts of pricing a row's stability against the whole
future.

Kept off every library's default target's critical path by being a leaf: nothing
imports it, it is checked at elaboration by `#guard`.
-/

namespace RubyCore.Types
namespace SlotEg

/-! ## Blocker 1 — three `include Comparable` need `<` at three classes -/

def objectId : ObjId := 1
def comparableId : ObjId := 10
def versionId : ObjId := 20
def pkgVersionId : ObjId := 21
def stringId : ObjId := 30

/-! `<` as Comparable declares it. -/
def ltSig : MethodDecl := { params := [Ty.any], ret := Ty.bool }

/-! `Version` resolves `<` at `Comparable`: spine `[Version, Comparable]`, the
    `empty` segment is `[Version]`, the `defined` slot is `Comparable#<`. -/
def rowVersionLt : SlotClaim :=
  SlotClaim.row versionId [versionId, comparableId] comparableId "<" ltSig

/-- And so does `PkgVersion`, through its own spine. -/
def rowPkgVersionLt : SlotClaim :=
  SlotClaim.row pkgVersionId [pkgVersionId, comparableId] comparableId "<" ltSig

/-! **They compose.** Same `defined` slot with the same signature (agreement),
    disjoint `empty` segments. Impossible today: the name-global guard holds `<`
    at one class or none. -/
#guard (SlotClaim.compose rowVersionLt rowPkgVersionLt).isSome

/-! The composite still owns both spines and both empty cells. -/
#guard match SlotClaim.compose rowVersionLt rowPkgVersionLt with
  | some c => c.spines.length == 2 && c.empty.length == 2 && c.defined.length == 2
  | none => false

/-! And a genuinely contradictory pair — the same slot pinned to two different
    signatures — is rejected at compose time, which is the point of the guard. -/
#guard (SlotClaim.compose rowVersionLt
    (SlotClaim.row versionId [versionId, comparableId] comparableId "<"
      { params := [], ret := Ty.int })).isNone

/-! ## Blocker 2 — `String#to_s` *and* `Version#to_s` -/

def toSSig : MethodDecl := { params := [], ret := Ty.cls "String" }

/-! `String` resolves `to_s` at itself. -/
def rowStringToS : SlotClaim :=
  SlotClaim.row stringId [stringId] stringId "to_s" toSSig

/-! A monkey-patched `Version#to_s`, resolving at `Version`. -/
def rowVersionToS : SlotClaim :=
  SlotClaim.row versionId [versionId] versionId "to_s" toSSig

/-! Both at once: `Version` is not on `String`'s chain, so the slots are disjoint
    and nothing is a choice-of-receiver-per-name. `core-rows.txt`'s
    ONE-ROW-PER-METHOD-NAME rule (§7.1) has no work left to do. -/
#guard (SlotClaim.compose rowStringToS rowVersionToS).isSome

/-! ## SF8 — what a write actually breaks

The frame is only worth having if it says *no* in the right places too.
-/

def bothToS : SlotClaim :=
  (SlotClaim.compose rowStringToS rowVersionToS).getD SlotClaim.unit

/-! Additive monkey-patching of an unrelated class is free. -/
#guard !(Install.defM comparableId "to_s").conflicts bothToS

/-! Redefining `String#to_s` is not: it is the `defined` slot the claim reads. -/
#guard (Install.defM stringId "to_s").conflicts bothToS

/-! **Additions are not free either** — SF8's correction of `declaresName`'s
    docstring. A fresh `def <` at `Version` breaks `Row Version "<"`-resolving-
    at-`Comparable`, because `Version` is on that row's own `empty` segment. -/
#guard (Install.defM versionId "<").conflicts rowVersionLt

/-! `include`/`prepend`/`extend` anywhere on a spine breaks it. -/
#guard (Install.ancestry comparableId).conflicts rowVersionLt
#guard !(Install.ancestry stringId).conflicts rowVersionLt

/-! SF2 — `method_missing` is a write to the default component, and it
    invalidates every `empty` reader on a chain through the class. Today
    `hookFreeNames` omits it, soundly, only because nothing owns emptiness. -/
#guard (Install.defM versionId "method_missing").conflicts rowVersionLt

/-! SF6a — a laundering site (`define_method(argv[0])`) keeps the site
    enumerable but forces its key set to ⊤, so it conflicts with every reader at
    that class. Completeness is lost exactly here, by design. -/
#guard (Install.anyName versionId).conflicts rowVersionLt
#guard !(Install.anyName stringId).conflicts rowVersionLt

/-! §5 step 3 over a whole inventory: the slice's shape — additive patches to
    unrelated classes, no ancestry mutation after boot (SF9). -/
#guard framedB bothToS
  [Install.defM comparableId "to_s", Install.defM objectId "hash",
   Install.ancestry pkgVersionId]

/-! ## §5 step 2 — the walk, on syntax

The inventory is what makes the closed world closed, so it is worth seeing it
read a program.
-/

/-! `class Version; def to_s; end; end` — one install, at `Version`. -/
#guard installsOf (.class' "Version" none (.def' "to_s" [] .nil)) 20
  == [InstallN.defM "Version" "to_s"]

/-! `class Version; include Comparable; end` — an ancestry mutation at `Version`
    (definition-position, so SF9 puts it in the boot prefix). -/
#guard installsOf (.class' "Version" none (.send none "include" [.const "Comparable"] none)) 20
  == [InstallN.ancestry "Version"]

/-! A literal-keyed `define_method` is an ordinary slot write... -/
#guard installsOf (.class' "V" none (.send none "define_method" [.sym "f"] none)) 20
  == [InstallN.defM "V" "f"]

/-! ...and a laundered one (SF6a) is the ⊤ key set at that class. -/
#guard installsOf (.class' "V" none
    (.send none "define_method" [.var .lvar "n"] none)) 20
  == [InstallN.anyName "V"]

/-! `attr_accessor :x` is two slots, which is exactly the sort of arithmetic the
    name-global guard could not do. -/
#guard installsOf (.class' "V" none (.send none "attr_accessor" [.sym "x"] none)) 20
  == [InstallN.defM "V" "x", InstallN.defM "V" "x="]

/-! `eval` is not readable, so the *program* is rejectable — §5's honest cost,
    and the same polarity as every other gate. -/
#guard (installsOf (.send none "class_eval" [] none) 20).any
  (fun i => match i with | .opaque_ _ => true | _ => false)

/-! A computed *dispatch* is not a write and is invisible to the frame. -/
#guard installsOf (.send (some (.var .lvar "o")) "send" [.var .lvar "n"] none) 20 == []

/-- End to end: the resolver maps the two names, the inventory misses the
    footprint, `framedProgB` accepts. -/
def egResolver : String → Option ObjId
  | "Version" => some versionId
  | "String" => some stringId
  | "Comparable" => some comparableId
  | _ => none

#guard framedProgB rowStringToS egResolver
  (.class' "Version" none (.def' "to_s" [] .nil)) 20

/-! And the same program does *not* frame a claim that reads `Version#to_s`'s
    slot — the additive monkey-patch is only free for claims elsewhere. -/
#guard !framedProgB rowVersionToS egResolver
  (.class' "Version" none (.def' "to_s" [] .nil)) 20

/-! An install at a class the resolver cannot name is a rejection, not a silent
    drop. -/
#guard !framedProgB rowStringToS egResolver
  (.class' "Unknown" none (.def' "to_s" [] .nil)) 20

end SlotEg
end RubyCore.Types
