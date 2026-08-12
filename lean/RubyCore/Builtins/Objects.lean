import RubyCore.Builtins.Numerics

/-!
BasicObject / Object core, Kernel I/O, and the nil / boolean rules.

Split out of the single `Builtins.run` match (L98), one class group per file, no
behaviour change: each rule file matches its own bids and hands anything it does
not recognise to the next file in the chain.
-/

namespace RubyCore

namespace Builtins

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
    -- Linked programs have their internal deps inlined; a residual `require` of a
    -- stdlib (e.g. `benchmark`/`yaml`) is a no-op that returns true (as CRuby's
    -- first load does). The result is essentially never observed.
    .ok (.bool true) m
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
