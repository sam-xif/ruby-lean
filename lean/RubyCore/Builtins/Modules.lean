import RubyCore.Builtins.Regex

/-!
Exception, Module and Class rules — the end of the chain, so this is
where an unmodeled bid becomes `unsupported`.

Split out of the single `Builtins.run` match (L98), one class group per file, no
behaviour change: each rule file matches its own bids and hands anything it does
not recognise to the next file in the chain.
-/

namespace RubyCore

namespace Builtins

/-- Exception, Module and Class rules — the end of the chain, so this is -/
def runModules (bid : String) (recv : Value) (args : List Value) (m : Machine) : BRes :=
  let h := m.heap
  match bid with
  /- ─── Exception ─── -/
  | "Exception#message" | "Exception#to_s" =>
    match recv with
    | .ref o => match (h.get o).payload with
      | .exc msg => okStr m msg
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
        if c.name.isEmpty then
          -- anonymous (`Class.new`): `name` is nil, `to_s`/`inspect` show the
          -- address form (L72)
          if bid == "Module#name" then .ok .nil m
          else match inspectP m recv with
            | .ok r => okStr m r
            | .error e => .unsupported e
        else okStr m c.name
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
  | "Class#superclass" =>
    -- `nil` for BasicObject and for a module [V].
    match recv with
    | .ref k =>
      match h.classPayload? k with
      | some cp => .ok (match cp.superclass with | some sup => .ref sup | none => .nil) m
      | none => .unsupported "superclass on a non-class"
    | _ => .unsupported "superclass on a non-class"
  | "Object#initialize" => .ok .nil m
  | "String#initialize" | "Array#initialize" | "Hash#initialize"
  | "Exception#initialize" =>
    -- Core initializers *mutate* the (already allocated) receiver, so a subclass's
    -- `initialize` can `super` into them (L70). Reached only via `super` or the
    -- allocate-then-initialize path; a plain `String.new` goes through `newImpl`.
    match recv with
    | .ref o =>
      let setP := fun (pl : Payload) =>
        BRes.ok .nil { m with heap := m.heap.set o { m.heap.get o with payload := pl } }
      if bid == "String#initialize" then
        match args with
        | [] => setP (.str "")
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
        | [] => setP (.hsh #[])
        | [dflt] =>
          let obj := { m.heap.get o with payload := .hsh #[], hashDflt := some (.val dflt) }
          .ok .nil { m with heap := m.heap.set o obj }
        | _ => .unsupported "Hash#initialize arity"
      else
        match args with
        | [] => setP (.exc (className h (h.get o).klass))
        | [msgV] => match toSP m msgV with
          | .ok str => setP (.exc str)
          | .error e => .unsupported e
        | _ => .unsupported "Exception#initialize arity"
    | _ => .unsupported "initialize on a non-object"
  | "Class#new" => newImpl m recv args
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
            [Boot.integerId, Boot.floatId, Boot.symbolId, Boot.nilClassId,
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
      | some cp =>
        let names := args.filterMap fun a =>
          match a with
          | .sym s => some s
          | .ref so => match (h.get so).payload with | .str s => some s | _ => none
          | _ => none
        if names.length != args.length then .unsupported "private_constant: non-name argument"
        else
          let priv :=
            if bid == "Module#private_constant" then
              cp.privateConsts ++ names.filter (fun n => !cp.privateConsts.contains n)
            else cp.privateConsts.filter (fun n => !names.contains n)
          .ok .nil { m with heap := h.setClassPayload o { cp with privateConsts := priv } }
    | _ => .unsupported "private_constant on a non-module"
  | _ => runRegex bid recv args m

end Builtins

end RubyCore
