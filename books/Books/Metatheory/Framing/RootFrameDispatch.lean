import Books.Metatheory.Framing.RootFrameMethod

/-! Root-execution framing for class and iterator entry. -/
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace RubyCore.Proof.Root
open Builtins Interp

@[rootFrameLem] theorem assignConstant_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (target : ObjId) (name : String) (value : Value) :
    assignConstant (pushRootK K m) target name value = rootFrameR K (assignConstant m target name value) := by
  have hLock := hK.hashLockFree
  unfold assignConstant
  root_dispatch_walk K hK

@[rootFrameLem] theorem inheritableClass_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (value : Value) (requireInitialized : Bool) :
    inheritableClass (pushRootK K m) value requireInitialized = (inheritableClass m value requireInitialized).mapError (rootFrameR K) := by
  have hLock := hK.hashLockFree
  unfold inheritableClass
  root_dispatch_walk K hK

@[rootFrameLem] theorem inheritClassBody_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (k : ObjId) (superclass : Option ObjId)
    (libraryName : String) (body : Expr) :
    inheritClassBody (pushRootK K m) k superclass libraryName body = rootFrameR K (inheritClassBody m k superclass libraryName body) := by
  have hLock := hK.hashLockFree
  unfold inheritClassBody
  root_dispatch_walk K hK

/-- The final allocation/notification phase, definitionally shared by both class entries. -/
def finishNewClass (m : Machine) (h : Heap) (k : ObjId) (superclass : Option ObjId)
    (libraryName : String) (body : Expr) (target : ObjId) (name : String) : StepResult :=
  let (_, m) := eigenclassOf { m with heap := h } k
  callConstAdded { m with kont := .constClassK k superclass libraryName body :: m.kont } target name

@[rootFrameLem] theorem finishNewClass_frame (K : List Kont) (hK : ContextFree K) (m : Machine) (h : Heap)
    (k : ObjId) (superclass : Option ObjId) (libraryName : String) (body : Expr)
    (target : ObjId) (name : String) :
    finishNewClass (pushRootK K m) h k superclass libraryName body target name =
      rootFrameR K (finishNewClass m h k superclass libraryName body target name) := by
  unfold finishNewClass
  rw [show ({ pushRootK K m with heap := h } : Machine) = pushRootK K { m with heap := h } from rfl]
  rw [eigenclassOf_frame]
  dsimp only
  rw [← callConstAdded_frame K hK]
  congr 1
  generalize eigenclassOf { m with heap := h } k = p
  cases he : p.2.activeEnumerator <;> simp [pushRootK, he]

def classBodyView (m : Machine) (name : String) (isMod : Bool) (sup? : Option ObjId) (body : Expr) : StepResult :=
  let kindWord := if isMod then "module" else "class"
  let libraryName := if m.lexicalNamespace == Boot.objectId then name else
    s!"{(libraryNamespace m.heap m.lexicalNamespace).getD (className m.heap m.lexicalNamespace)}::{name}"
  let pushFrame (m : Machine) (k : ObjId) := pushClassFrame m k libraryName body
  -- Reopen detection looks up `name` in the *current innermost namespace only*
  -- (`defmod`), NOT a flat toplevel lookup and NOT the full lexical cref chain.
  -- So `module B` inside a reopened `module A` finds the existing `A::B` (A's own
  -- constant) and reuses that object instead of allocating a duplicate and
  -- clobbering `A::B`. Crucially it is *not* the cref-walk used for constant
  -- *reads*: `class Foo` nested in `M` must create `M::Foo`, it does NOT reopen a
  -- lexically-visible `::Foo` (verified against CRuby). At the toplevel `defmod`
  -- is `Object`, so this coincides with the old flat lookup.
  match constOwn m.heap m.lexicalNamespace name with
  | some (.ref k) =>
    match m.heap.classPayload? k with
    | some c =>
      if c.isModule != isMod then
        .next (raiseErr m Boot.typeErrorId s!"{name} is not a {kindWord}")
      else match sup? with
        | some s =>
          if c.superclass == some s then pushFrame m k
          else .next (raiseErr m Boot.typeErrorId s!"superclass mismatch for class {name}")
        | none => pushFrame m k
    | none => .next (raiseErr m Boot.typeErrorId s!"{name} is not a {kindWord}")
  | some _ => .next (raiseErr m Boot.typeErrorId s!"{name} is not a {kindWord}")
  | none =>
    if (m.heap.get m.lexicalNamespace).frozen then raiseFrozen m (.ref m.lexicalNamespace) else
    let superclass := if isMod then none else some (sup?.getD Boot.objectId)
    -- A nested definition (`module B` inside `A`) takes the qualified constant
    -- path `A::B` as its `name` (CRuby derives the name from where the constant
    -- is bound); a toplevel definition (`defmod` = Object) keeps the bare name.
    let defmod := m.lexicalNamespace
    let obj : Object :=
      { klass := (if isMod then Boot.moduleId else Boot.classId), payload := .cls { superclass, name := "", isModule := isMod, ancestryReady := superclass.all (fun s => (m.heap.classPayload? s).all (·.ancestryReady)), allocatorUnavailable := superclass.any (fun s => (m.heap.classPayload? s).any (·.allocatorUnavailable)) } }
    let (k, h) := m.heap.alloc obj
    -- register the class name in the *enclosing* namespace (Object at toplevel)
    let h := constSetIn h m.lexicalNamespace name (.ref k)
    match nameConstant h defmod name (.ref k) with
    | .error why => .unsupported why
    | .ok h =>
      -- Eagerly realize the metaclass chain so inherited class methods resolve
      -- (`B < A` ⇒ `B`'s metaclass superclasses `A`'s) before any `def self.`.
      finishNewClass m h k superclass libraryName body defmod name

def scopedClassBodyView (m : Machine) (container : ObjId) (name : String) (isMod : Bool) (body : Expr) : StepResult :=
  let kindWord := if isMod then "module" else "class"
  let fullName := s!"{className m.heap container}::{name}"
  let libraryName := s!"{(libraryNamespace m.heap container).getD (className m.heap container)}::{name}"
  let pushFrame (m : Machine) (k : ObjId) := pushClassFrame m k libraryName body
  let existing : Option Value := (m.heap.classPayload? container).bind fun c =>
    (c.consts.find? (·.1 == name)).map (·.2)
  match existing with
  | some (.ref k) =>
    match m.heap.classPayload? k with
    | some c =>
      if c.isModule != isMod then
        .next (raiseErr m Boot.typeErrorId s!"{fullName} is not a {kindWord}")
      else pushFrame m k
    | none => .next (raiseErr m Boot.typeErrorId s!"{fullName} is not a {kindWord}")
  | some _ => .next (raiseErr m Boot.typeErrorId s!"{fullName} is not a {kindWord}")
  | none =>
    if (m.heap.get container).frozen then raiseFrozen m (.ref container) else
    let superclass := if isMod then none else some Boot.objectId
    let obj : Object :=
      { klass := (if isMod then Boot.moduleId else Boot.classId),
        payload := .cls { superclass, name := "", isModule := isMod } }
    let (k, h) := m.heap.alloc obj
    let h := constSetIn h container name (.ref k)
    match nameConstant h container name (.ref k) with
    | .error why => .unsupported why
    | .ok h =>
      finishNewClass m h k superclass libraryName body container name

@[rootFrameLem] theorem enterClassBody_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (name : String) (isMod : Bool)
    (sup? : Option ObjId) (body : Expr) :
    enterClassBody (pushRootK K m) name isMod sup? body = rootFrameR K (enterClassBody m name isMod sup? body) := by
  have hLock := hK.hashLockFree
  change classBodyView (pushRootK K m) name isMod sup? body = rootFrameR K (classBodyView m name isMod sup? body)
  unfold classBodyView
  root_dispatch_walk K hK

@[rootFrameLem] theorem enterScopedClassBody_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (container : ObjId) (name : String)
    (isMod : Bool) (body : Expr) :
    enterScopedClassBody (pushRootK K m) container name isMod body = rootFrameR K (enterScopedClassBody m container name isMod body) := by
  have hLock := hK.hashLockFree
  change scopedClassBodyView (pushRootK K m) container name isMod body = rootFrameR K (scopedClassBodyView m container name isMod body)
  unfold scopedClassBodyView
  root_dispatch_walk K hK

@[rootFrameLem] theorem startIter_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (mname : String) (cl : Closure)
    (elemArgs : List (List Value)) (kind : IterKind) (initAcc : List Value)
    (retVal : Value) :
    startIter (pushRootK K m) recv mname cl elemArgs kind initAcc retVal = rootFrameR K (startIter m recv mname cl elemArgs kind initAcc retVal) := by
  have hLock := hK.hashLockFree
  unfold startIter
  root_dispatch_walk K hK

@[rootFrameLem] theorem callArrayMapBuiltin_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (mname : String)
    (args : List Value) (blk : Option Value) (kw : List (Value × Value)) :
    callArrayMapBuiltin (pushRootK K m) recv mname args blk kw = rootFrameR K (callArrayMapBuiltin m recv mname args blk kw) := by
  have hLock := hK.hashLockFree
  unfold callArrayMapBuiltin
  root_dispatch_walk K hK

@[rootFrameLem] theorem tryIterator_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (mname : String) (args : List Value)
    (blk : Option Value) :
    tryIterator (pushRootK K m) recv mname args blk = (tryIterator m recv mname args blk).map (rootFrameR K) := by
  have hLock := hK.hashLockFree
  unfold tryIterator
  root_dispatch_walk K hK

@[rootFrameLem] theorem callNativeIterator_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (bid : String) (recv : Value) (args : List Value)
    (blk : Option Value) (kw : List (Value × Value)) :
    callNativeIterator (pushRootK K m) bid recv args blk kw = rootFrameR K (callNativeIterator m bid recv args blk kw) := by
  have hLock := hK.hashLockFree
  unfold callNativeIterator
  cases hr : Builtins.run bid recv args m <;>
    cases hi : tryIterator m recv ((bid.splitOn "#").getLast!) [] blk <;>
    root_dispatch_walk K hK <;>
    simp_all only [rootFrameLem, hr, hi, Option.map_none, Option.map_some, Option.getD]

@[rootFrameLem] theorem tryMixin_frame (K : List Kont) (hK : ContextFree K)
    (m : Machine) (recv : Value) (mname : String)
    (args : List Value) :
    tryMixin (pushRootK K m) recv mname args = (tryMixin m recv mname args).map (rootFrameR K) := by
  have hLock := hK.hashLockFree
  unfold tryMixin
  root_dispatch_walk K hK

end RubyCore.Proof.Root
