import RubyCore.Builtins.Numerics

/-!
BasicObject / Object core, Kernel I/O, and the nil / boolean rules.

Split out of the single `Builtins.run` match (L98), one class group per file, no
behaviour change: each rule file matches its own bids and hands anything it does
not recognise to the next file in the chain.
-/

namespace RubyCore

namespace Builtins

/-- Libraries whose surface the prelude actually carries, so `require` of them
    is a faithful no-op. `sorbet-runtime` is the T shim (L80/L101); the rest of
    the stdlib is not modeled and must gate rather than pretend (L109). -/
def modeledFeatures : List String :=
  ["sorbet-runtime", "sorbet-runtime/lib/types/private/methods/decl_builder",
   -- the pure halves of these are in the prelude (L112): `Pathname`'s path
   -- operations, `URI.decode_www_form_component`, `File`'s path operations
   "pathname", "uri", "forwardable", "json"]

/-- BasicObject / Object core, Kernel I/O, and the nil / boolean rules. -/
def runObjects (bid : String) (recv : Value) (args : List Value) (m : Machine) : BRes :=
  let h := m.heap
  match bid with
  /- ─── BasicObject / Object core ─── -/
  | "BasicObject#==" | "Object#==" =>
    match args with
    | [b] =>
      -- default == is identity — except Exception, which compares
      -- class + message [V]
      match recv, b with
      | .ref x, .ref y =>
        match (h.get x).payload, (h.get y).payload with
        | .exc ma, .exc mb =>
          .ok (.bool ((h.get x).klass == (h.get y).klass && ma == mb)) m
        | _, _ => .ok (.bool (recv.identEq b)) m
      | _, _ => .ok (.bool (recv.identEq b)) m
    | _ => .unsupported "==/arity"
  | "BasicObject#equal?" | "Object#equal?" =>
    match args with
    | [b] => .ok (.bool (recv.identEq b)) m
    | _ => .unsupported "equal?/arity"
  | "Object#eql?" =>
    match args with
    | [b] => .ok (.bool (valueEql h recv b)) m
    | _ => .unsupported "eql?/arity"
  | "BasicObject#!" | "Object#!" => .ok (.bool (!recv.truthy)) m
  | "BasicObject#!=" | "Object#!=" =>
    match args with
    | [b] => .ok (.bool (!(valueEq h recv b))) m
    | _ => .unsupported "!=/arity"
  | "Object#__write" =>
    -- The primitive the prelude's repr twins write through: append a String to
    -- stdout verbatim, with no rendering of any kind (L116).
    binArg m args fun a =>
      match strPayload? h a with
      | some str =>
        if isBinaryStr h a && hasHighByte str then
          .unsupported "__write of a byte string holding a byte ≥ 0x80 (L118)"
        else .ok .nil { m with out := m.out ++ str }
      | none => .unsupported "__write of a non-String"
  | "Object#__addr_str" =>
    -- The `0x…` an object's default `inspect` carries. The observation
    -- normalizes addresses on both sides, so only the *shape* matters — but it
    -- has to be `Repr.fakeAddr`'s shape, since the two render the same objects.
    match recv with
    | .ref o => okStr m (fakeAddr o)
    | _ => .unsupported "__addr_str of an immediate"
  | "Object#__match_to_caller" =>
    -- Declares the running activation a stand-in for a CRuby **C function** as far
    -- as `$~` goes: every later read or write in this body resolves to the
    -- caller's frame slot (L121). `String#sub`/`#gsub`/`#index` and
    -- `Regexp.last_match` are prelude Ruby (L110/L115) where CRuby has C, and a C
    -- function sets its caller's backref — so without this the caller of `gsub`
    -- would see no match where CRuby shows it the last one.
    --
    -- A marker *call* rather than a Lean-side list of transparent bids, because a
    -- reader of `gsub` has to be able to see it: this is the one property of the
    -- method not derivable from its body. It must be the body's first statement.
    .ok .nil (m.setCurrentFrame { m.currentFrame with matchXparent := true })
  | "Object#__user_defines?" =>
    -- Heap introspection the object language cannot perform: does this object's
    -- ancestor chain carry a **non-builtin** definition of `name`? Prelude Ruby
    -- needs it to reproduce CRuby's `rb_check_funcall` rule, which consults a
    -- *custom* `respond_to?` if the class has one and otherwise falls back to
    -- "the method is defined, or `method_missing` can serve it" (L115).
    --
    -- `classOf`, not `realClassOf`: the chain that matters is the one *dispatch*
    -- would walk, which starts at the **eigenclass**. `bootstraptest/test_yjit_167`
    -- is exactly this — `def obj.to_ary` on a single object, which `a, b, c = obj`
    -- must find — and `realClassOf` skipped it.
    let defines : String → Bool := fun n => reprOverridden h [n] (classOf h recv)
    binArg m args fun a =>
      match a with
      | .sym n => .ok (.bool (defines n)) m
      | .ref o => match (h.get o).payload with
        | .str n => .ok (.bool (defines n)) m
        | _ => .unsupported "__user_defines? of a non-name"
      | _ => .unsupported "__user_defines? of a non-name"
  | "Object#__coerce_failed" =>
    -- The two messages the coerce protocol's prelude twins raise (L123). They are
    -- primitives for one reason: `coerceDesc`'s rule for naming an operand (a
    -- special constant shows its `inspect`, everything else its class) is already
    -- written once, and a second copy in Ruby is a second copy to drift — the
    -- messages themselves are the *only* thing these builtins produce.
    binArg m args fun b =>
      .err Boot.typeErrorId
        s!"{coerceDesc h b} can't be coerced into {className h (realClassOf h recv)}" m
  | "Object#__cmp_failed" =>
    -- `rb_cmperr`, which names the **original** operands, not the coerced pair.
    binArg m args fun b =>
      .err Boot.argumentErrorId
        s!"comparison of {className h (realClassOf h recv)} with {coerceDesc h b} failed" m
  | "Object#nil?" | "NilClass#nil?" =>
    .ok (.bool (match recv with | .nil => true | _ => false)) m
  | "Object#class" => .ok (.ref (realClassOf h recv)) m
  | "Object#inspect" =>
    match inspectP m recv with
    | .ok s => okStr m s
    | .error e => .unsupported e
  | "Object#to_s" =>
    match toSP m recv with
    | .ok s => okStr m s
    | .error e => .unsupported e
  | "Object#frozen?" | "Hash#frozen?" =>
    match recv with
    | .ref o => .ok (.bool (h.get o).frozen) m
    | _ => .ok (.bool true) m
  | "Object#freeze" | "String#freeze" | "Array#freeze" | "Hash#freeze" =>
    match recv with
    | .ref o => .ok recv { m with heap := h.set o { h.get o with frozen := true } }
    | _ => .ok recv m
  | "Object#is_a?" | "Object#kind_of?" =>
    match args with
    | [.ref k] =>
      if (h.classPayload? k).isSome then .ok (.bool (isA h recv k)) m
      else .err Boot.typeErrorId "class or module required" m
    | [_] => .err Boot.typeErrorId "class or module required" m
    | _ => .unsupported "is_a?/arity"
  | "Object#instance_of?" =>
    match args with
    | [.ref k] =>
      if (h.classPayload? k).isSome then .ok (.bool (realClassOf h recv == k)) m
      else .err Boot.typeErrorId "class or module required" m
    | [_] => .err Boot.typeErrorId "class or module required" m
    | _ => .unsupported "instance_of?/arity"
  | "Object#block_given?" =>
    -- true iff the enclosing method activation received a block (the block
    -- is propagated onto block frames, so the current frame's blk answers) [V]
    .ok (.bool m.currentFrame.blk.isSome) m
  | "Object#__unsupported__" =>
    -- The prelude's fragment gate (L62): RubyCore-level core-library code cannot
    -- return `.unsupported` on its own, so it calls this to declare a form it
    -- does not model (`Enumerator`, a `<=>`-less comparison, …). Keeps the
    -- "declare, never guess" discipline available to prelude authors.
    match args with
    | [a] => match strPayload? h a with
      | some s => .unsupported s
      | none => .unsupported "prelude gate (non-String reason)"
    | _ => .unsupported "prelude gate"
  | "Object#require" | "Object#require_relative" =>
    -- Linked programs have their internal deps inlined, so a residual `require`
    -- names a library the *control* will load and the model will not. Returning
    -- `true` for all of them (the old rule) is the N34 bug: the program then
    -- runs on against constants the model does not have, and the first one
    -- becomes a NameError where CRuby succeeded — a **disagreement** rather than
    -- a refusal. So: a feature the prelude actually models returns true; any
    -- other gates by name (L109).
    match args with
    | [f] =>
      match strPayload? h f with
      | some feat =>
        if modeledFeatures.contains feat then .ok (.bool true) m
        else .unsupported s!"require of an unmodeled library: {feat}"
      | none => .unsupported "require of a non-String feature"
    | _ => .unsupported "require arity"
  -- Registered on Range (not inherited from Object) so the L6 shadow check sees
  -- the right owner; `Repr` already renders `.range` payloads [V].
  | "Range#inspect" =>
    match inspectP m recv with
    | .ok s => okStr m s
    | .error e => .unsupported e
  | "Range#to_s" =>
    match toSP m recv with
    | .ok s => okStr m s
    | .error e => .unsupported e
  | "Range#first" | "Range#begin" =>
    match recv with
    | .ref o => match (h.get o).payload with
      | .range lo _ _ => .ok lo m
      | _ => .unsupported "Range#first"
    | _ => .unsupported "Range#first"
  | "Range#last" | "Range#end" =>
    match recv with
    | .ref o => match (h.get o).payload with
      | .range _ hi _ => .ok hi m
      | _ => .unsupported "Range#last"
    | _ => .unsupported "Range#last"
  | "Range#exclude_end?" =>
    match recv with
    | .ref o => match (h.get o).payload with
      | .range _ _ e => .ok (.bool e) m
      | _ => .unsupported "Range#exclude_end?"
    | _ => .unsupported "Range#exclude_end?"
  | "Random#rand" =>
    match recv with
    | .ref o =>
      match (h.get o).payload with
      | .rng st =>
        match args with
        | [] =>   -- Random#rand → Float in [0,1); mutate the object's MT state
          let (r, st') := MT.nextReal st
          .ok (.flt r) { m with heap := h.set o { h.get o with payload := .rng st' } }
        | _ => .unsupported "Random#rand(n) (bounded draw not modeled)"
      | _ => .unsupported "rand on non-Random receiver"
    | _ => .unsupported "Random#rand"
  | "Object#rand" =>
    -- Deterministic placeholder for CRuby's *unseeded* Kernel#rand. Its value is
    -- observationally irrelevant to any program CRuby runs deterministically: an
    -- output that depends on unseeded `rand` is nondeterministic under CRuby's
    -- double-run and excluded as `control_invalid`, so a fixed value here can
    -- never cause a recorded disagreement — while output-*independent* uses run
    -- (q_learning's `rand < exploration` with exploration 0 always takes the
    -- exploit branch since 0.0 < 0.0 is false, matching CRuby's rand ∈ [0,1)).
    -- Seeded RNG (`srand`, `Random.new(seed)`) stays UNMODELED (gates), so a
    -- deterministic seeded program cannot silently diverge here. See notes L43.
    match args with
    | [] => .ok (.flt 0.0) m                           -- rand → Float in [0,1)
    | [.int n] =>
      if n > 0 then .ok (.int 0) m                     -- rand(n) → Integer in [0,n)
      else .unsupported "rand(n <= 0)"                  -- rand(0) is Float [0,1): rare, gate
    | _ => .unsupported "rand (float/range arg)"
  /- ─── Kernel I/O ─── -/
  | "Object#puts" => putsImpl m args
  | "Object#print" =>
    args.foldlM (fun m a => do
      match toSP m a with
      | .ok s => pure (m.emit s)
      | .error e => none) m
    |> fun
      | some m => .ok .nil m
      | none => .unsupported "print: impure to_s"
  | "Object#p" =>
    let rec go (m : Machine) : List Value → Option Machine
      | [] => some m
      | a :: rest =>
        match inspectP m a with
        | .ok s => go (m.emit (s ++ "\n")) rest
        | .error _ => none
    match go m args with
    | none => .unsupported "p: impure inspect"
    | some m =>
      match args with
      | [] => .ok .nil m
      | [a] => .ok a m
      | _ => let (v, m) := allocArr m args.toArray; .ok v m
  | "Object#String" =>
    match args with
    | [a] =>
      match toSP m a with
      | .ok s => okStr m s
      | .error e => .unsupported e
    | _ => .unsupported "String()/arity"
  | "Object#raise" => raiseImpl m args
  /- ─── nil / booleans ─── -/
  | "NilClass#to_s" => okStr m ""
  | "NilClass#inspect" => okStr m "nil"
  | "NilClass#to_a" => let (v, m) := allocArr m #[]; .ok v m
  | "NilClass#&" | "FalseClass#&" => .ok (.bool false) m
  | "NilClass#|" | "FalseClass#|" =>
    match args with
    | [b] => .ok (.bool b.truthy) m
    | _ => .unsupported "|/arity"
  | "TrueClass#&" =>
    match args with
    | [b] => .ok (.bool b.truthy) m
    | _ => .unsupported "&/arity"
  | "TrueClass#|" => .ok (.bool true) m
  | "TrueClass#to_s" | "TrueClass#inspect" => okStr m "true"
  | "FalseClass#to_s" | "FalseClass#inspect" => okStr m "false"
  | _ => runNumerics bid recv args m

end Builtins

end RubyCore
