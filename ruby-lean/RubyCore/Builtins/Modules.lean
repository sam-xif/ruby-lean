import RubyCore.Builtins.Regex
import RubyCore.CRubyNames

/-!
Exception, Module and Class rules — the end of the chain, so this is
where an unmodeled bid becomes `unsupported`.

Split out of the single `Builtins.run` match (L98), one class group per file, no
behaviour change: each rule file matches its own bids and hands anything it does
not recognise to the next file in the chain.
-/

namespace RubyCore

namespace Builtins

/-- Module#name returns its frozen native path String, including shared identity
    across bindings with the same path. Promotion selects a new cached String;
    earlier temporary-name values remain unchanged. Anonymous namespaces return
    nil. ASCII permanent names retain the existing US-ASCII/UTF-8 boundary;
    temporary ASCII paths are native binary Strings (L297). -/
def nativeModuleName (m : Machine) (c : ClassPayload) : BRes :=
  if c.name.isEmpty then .ok .nil m else
  let binary := !c.namePermanent && !hasHighByte c.name
  match m.heap.nameStrings.find? (fun (s, b, _) => s == c.name && b == binary) with
  | some (_, _, o) => .ok (.ref o) m
  | none =>
    let (o, h) := m.heap.alloc
      { klass := Boot.stringId, payload := .str c.name, binary, frozen := true }
    let h := { h with nameStrings := (c.name, binary, o) :: h.nameStrings }
    .ok (.ref o) { m with heap := h }

/-- Exception, Module and Class rules — the end of the chain, so this is -/
def setConstantVisibility (m : Machine) (recv : Value) (o : ObjId) (privateConst : Bool)
    (names : List String) : BRes :=
  match names with
  | [] => .ok recv m
  | name :: rest =>
    match m.heap.classPayload? o with
    | none => .unsupported "constant visibility on a non-module"
    | some cp =>
      if name.isEmpty || !(name.toList.headD '_').isUpper ||
          !(name.toList.all (fun c => c.isAlphanum || c == '_')) then
        .unsupported "constant visibility with a non-simple constant name" else
      if !(cp.consts.any (·.1 == name)) then
        let known := (crubyNamespaceConstants.find? (·.1 == className m.heap o)).any (·.2.contains name) ||
          (cp.libraryNamespace.bind (fun ns => crubyFeatureConstants.find? (·.1 == ns))).any (·.2.contains name) ||
          (o == Boot.objectId && m.attemptedFeatures.any (fun feature =>
            (crubyFeatureRoots.find? (·.1 == feature)).any (·.2.contains name)))
        if known then .unsupported s!"constant visibility of unmodeled constant {name}" else
        .err Boot.nameErrorId s!"constant {className m.heap o}::{name} not defined" m
      else
        let priv := if privateConst then
          cp.privateConsts ++ (if cp.privateConsts.contains name then [] else [name])
          else cp.privateConsts.filter (· != name)
        setConstantVisibility { m with heap := m.heap.setClassPayload o { cp with privateConsts := priv } }
          recv o privateConst rest

def runModules (bid : String) (recv : Value) (args : List Value) (m : Machine) : BRes :=
  let h := m.heap
  match bid with
  /- ─── Exception ─── -/
  -- `Exception#message` is **not** here: it is `to_s` in CRuby (`exc_message` is
  -- one `rb_funcall`), so a user `to_s` must show through it. As a builtin sharing
  -- this arm it read the payload directly, and `E.new("boom").message` answered
  -- "boom" for a class whose `to_s` says otherwise. It is prelude Ruby now — `def
  -- message = to_s` — which is the only spelling that dispatches (L131).
  | "UncaughtThrowError#tag" | "UncaughtThrowError#value" =>
    if !args.isEmpty then .err Boot.argumentErrorId
      s!"wrong number of arguments (given {args.length}, expected 0)" m else
    match recv with
    | .ref o => .ok (if bid == "UncaughtThrowError#tag" then (h.get o).throwTag else (h.get o).throwValue) m
    | _ => .unsupported "UncaughtThrowError metadata receiver"
  | "UncaughtThrowError#__throw_metadata" =>
    match recv, args with
    | .ref o, [tag, value] =>
      if (h.get o).frozen then .frozen recv m else
      .ok recv { m with heap := h.set o { h.get o with throwTag := tag, throwValue := value } }
    | _, _ => .unsupported "UncaughtThrowError metadata arguments"
  | "Exception#to_s" =>
    match recv with
    | .ref o => match (h.get o).payload with
      | .exc msg =>
        if msg.identEq .nil then okStr m (className h (h.get o).klass) else
        match strPayload? h msg with
        | some _ => .ok msg m
        | none => .unsupported "Exception#to_s requires checked String conversion"
      | _ => .unsupported "message"
    | _ => .unsupported "message"
  | "Exception#inspect" =>
    match inspectP m recv with
    | .ok s => okStr m s
    | .error e => .unsupported e
  /- ─── Module / Class ─── -/
  | "Module#===" =>
    binArg m args fun b =>
      match recv with
      | .ref k =>
        if (h.classPayload? k).isSome then .ok (.bool (isA h b k)) m
        else .unsupported "==="
      | _ => .unsupported "==="
  | "Module#name" | "Module#to_s" | "Module#inspect" =>
    match recv with
    | .ref k =>
      match h.classPayload? k with
      | some c =>
        if bid == "Module#name" then
          nativeModuleName m c
        else okStr m (className h k)
      | none => .unsupported "name"
    | _ => .unsupported "name"
  | "Module#==" =>
    binArg m args fun b => .ok (.bool (recv.identEq b)) m
  | "Module#ancestors" =>
    match recv with
    | .ref k =>
      if (h.classPayload? k).isSome then
        let (v, m) := allocArr m ((ancestors h k).map Value.ref).toArray
        .ok v m
      else .unsupported "ancestors"
    | _ => .unsupported "ancestors"
  | "Class#inherited" | "Module#const_added" =>
    if args.length == 1 then .ok .nil m else
      .err Boot.argumentErrorId s!"wrong number of arguments (given {args.length}, expected 1)" m
  | "Class#superclass" =>
    -- `nil` for BasicObject and for a module [V].
    match recv with
    | .ref k =>
      match h.classPayload? k with
      | some cp =>
        if !cp.ancestryReady then .err Boot.typeErrorId "uninitialized class" m else
        .ok (match cp.superclass with | some sup => .ref sup | none => .nil) m
      | none => .unsupported "superclass on a non-class"
    | _ => .unsupported "superclass on a non-class"
  | "BasicObject#initialize" | "Object#initialize" =>
    if args.isEmpty then .ok .nil m else
      .err Boot.argumentErrorId s!"wrong number of arguments (given {args.length}, expected 0)" m
  | "Object#initialize_copy" =>
    match args with
    | [other] =>
      if recv.identEq other then .ok recv m else
      match recv with
      | .ref o =>
        if (h.get o).frozen then .frozen recv m else
        if realClassOf h recv != realClassOf h other then
          .err Boot.typeErrorId "initialize_copy should take same class object" m
        else .ok recv m
      | _ => .frozen recv m
    | _ => .err Boot.argumentErrorId s!"wrong number of arguments (given {args.length}, expected 1)" m
  | "String#initialize" | "Array#initialize" | "Hash#initialize"
  | "Exception#initialize" =>
    -- Core initializers *mutate* the (already allocated) receiver, so a subclass's
    -- `initialize` can `super` into them (L70). Constructors now allocate then
    -- send initialize through ordinary lookup (L284).
    match recv with
    | .ref o =>
      if bid != "Array#initialize" && args.length > 1 then
        .err Boot.argumentErrorId s!"wrong number of arguments (given {args.length}, expected 0..1)" m else
      if (h.get o).frozen && !(bid == "String#initialize" && args.isEmpty) then
        .frozen recv m else
      if bid == "Array#initialize" && args.length > 2 then
        .err Boot.argumentErrorId s!"wrong number of arguments (given {args.length}, expected 0..2)" m else
      let setP := fun (pl : Payload) =>
        BRes.ok recv { m with heap := m.heap.set o { m.heap.get o with payload := pl } }
      if bid == "String#initialize" then
        match args with
        | [] => .ok recv m
        | [sv] => match strPayload? h sv with
          | some str => setP (.str str)
          | none => .unsupported "String#initialize with a non-String argument"
        | _ => .unsupported "String#initialize arity"
      else if bid == "Array#initialize" then
        match args with
        | [] => setP (.arr #[])
        | [.int n] =>
          if n < 0 then .err Boot.argumentErrorId "negative array size" m
          else setP (.arr (Array.replicate n.toNat .nil))
        | [.int n, dflt] =>
          if n < 0 then .err Boot.argumentErrorId "negative array size" m
          else setP (.arr (Array.replicate n.toNat dflt))
        | _ => .unsupported "Array#initialize arity"
      else if bid == "Hash#initialize" then
        match args with
        | [] => .ok recv { m with heap := h.set o { h.get o with hashDflt := none } }
        | [dflt] =>
          let obj := { m.heap.get o with hashDflt := some (.val dflt) }
          .ok recv { m with heap := m.heap.set o obj }
        | _ => .unsupported "Hash#initialize arity"
      else
        match args with
        | [] => setP (.exc .nil)
        | [msgV] => setP (.exc msgV)
        | _ => .unsupported "Exception#initialize arity"
    | _ => .unsupported "initialize on a non-object"
  | "Class#new" | "Module#new" => newImpl m recv args
  | "Class#__range_new_unchecked" =>
    -- Allocate a `Range` with **no endpoint check** — the primitive the prelude's
    -- `Range.new` builds on, because the check has to dispatch `<=>` (L122).
    -- Third argument by *truthiness*, since `Range.new(1, 2, 3).exclude_end?` is
    -- `true` [V]; it used to be matched as a `Bool` and anything else gated.
    match recv, args with
    | .ref k, [lo, hi, excl] =>
      if k != Boot.rangeId then .unsupported "__range_new_unchecked on a non-Range"
      else
        let (o, h) := m.heap.alloc
          -- CRuby's ranges are frozen, literal and constructed alike [V]
          { klass := Boot.rangeId, payload := .range lo hi excl.truthy, frozen := true }
        .ok (.ref o) { m with heap := h }
    | _, _ => .unsupported "__range_new_unchecked arity"
  -- `allocate`: the first half of `new` — an instance with the class's *empty*
  -- payload and NO `initialize` call. Immediates have no heap representation, so
  -- CRuby raises `TypeError: allocator undefined for X` for Integer/Float/Symbol/
  -- NilClass/TrueClass/FalseClass [V]. That error is not academic: ObjectGraph's
  -- `objectspace_loop` rescues exactly it (`detail.message =~ /allocator
  -- undefined/`), so answering it faithfully is what lets that loop run.
  | "Class#allocate" =>
    match recv with
    | .ref k =>
      match m.heap.classPayload? k with
      | none => .unsupported "allocate on non-class"
      | some c =>
        if c.isModule then .unsupported "Module#allocate"
        else
          let chain := ancestors m.heap k
          let noAllocator :=
            [Boot.integerId, Boot.floatId, Boot.symbolId, Boot.nilClassId, Boot.procId,
             Boot.trueClassId, Boot.falseClassId].any chain.contains
          if noAllocator then
            .err Boot.typeErrorId s!"allocator undefined for {className m.heap k}" m
          else
            let payload := match allocatableCore m.heap k with
              | some core => emptyCorePayload core
              | none => Payload.none
            let (o, h) := m.heap.alloc { klass := k, payload }
            .ok (.ref o) { m with heap := h }
    | _ => .unsupported "allocate on non-class"
  | "Module#private_constant" | "Module#public_constant" =>
    -- Constant *visibility*: a `private_constant` name stays visible to lexical
    -- lookup from inside the module and disappears from `A::B` outside it, where
    -- CRuby then runs `const_missing` (or raises `NameError`). Modeled as a list
    -- on the class payload and consulted by the `cpath` rule (L104). Nine of
    -- Homebrew `version.rb`'s constants are declared this way.
    match recv with
    | .ref o =>
      match h.classPayload? o with
      | none => .unsupported "private_constant on a non-module"
      | some _ =>
        if (h.get o).frozen then .frozen recv m else
        let names := args.filterMap fun a =>
          match a with
          | .sym s => some s
          | .ref so => match (h.get so).payload with | .str s => some s | _ => none
          | _ => none
        if names.length != args.length then .unsupported "constant visibility: name conversion" else
        setConstantVisibility m recv o (bid == "Module#private_constant") names
    | _ => .unsupported "private_constant on a non-module"
  | _ => runRegex bid recv args m

end Builtins

end RubyCore
