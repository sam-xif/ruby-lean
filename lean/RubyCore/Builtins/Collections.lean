import RubyCore.Builtins.Modules

/-!
Array and Hash rules.

Split out of the single `Builtins.run` match (L98), one class group per file, no
behaviour change: each rule file matches its own bids and hands anything it does
not recognise to the next file in the chain.
-/

namespace RubyCore

namespace Builtins

/-- Array and Hash rules. -/
def runCollections (bid : String) (recv : Value) (args : List Value) (m : Machine) : BRes :=
  let h := m.heap
  match bid with
  /- ─── Array ─── -/
  | "Array#==" | "Array#eql?" =>
    binArg m args fun b =>
      match arrPayload? h recv, arrPayload? h b with
      | some _, some _ =>
        .ok (.bool (if bid == "Array#eql?" then valueEql h recv b else valueEq h recv b)) m
      | _, _ => .ok (.bool false) m
  | "Array#!=" =>
    binArg m args fun b => .ok (.bool (!(valueEq h recv b))) m
  | "Array#[]" =>
    match arrPayload? h recv, args with
    | some xs, [.int i] =>
      let idx := if i < 0 then i + xs.size else i
      if idx < 0 || idx ≥ xs.size then .ok .nil m
      else .ok xs[idx.toNat]! m
    | some xs, [.ref ro] =>
      match (h.get ro).payload with
      | .range lo hi excl =>
        -- Array slice by Range: normalize endpoints (nil begin → 0, nil end → to
        -- last; negative → +size), then take start..(excl ? end-1 : end).
        let n : Int := xs.size
        let startI? : Option Int := match lo with
          | .nil => some 0
          | .int i => some (if i < 0 then i + n else i)
          | _ => none
        match startI? with
        | none => .unsupported "Array#[] range non-int begin"
        | some s =>
          if s < 0 || s > n then .ok .nil m
          else
            let lastI? : Option Int := match hi with
              | .nil => some (n - 1)
              | .int i => let e := if i < 0 then i + n else i; some (if excl then e - 1 else e)
              | _ => none
            match lastI? with
            | none => .unsupported "Array#[] range non-int end"
            | some lastRaw =>
              let lastI := min lastRaw (n - 1)
              if lastI < s then let (v, m) := allocArr m #[]; .ok v m
              else
                let sub := ((xs.toList.drop s.toNat).take (lastI.toNat - s.toNat + 1)).toArray
                let (v, m) := allocArr m sub; .ok v m
      | _ => .unsupported "Array#[] non-int index"
    | some xs, [.int start, .int len] =>
      match sliceRange xs.size start len with
      | none => .ok .nil m
      | some (off, count) =>
        let (v, m) := allocArr m ((xs.toList.drop off).take count).toArray
        .ok v m
    | some _, _ => .unsupported "Array#[] index form"
    | _, _ => .unsupported "[]"
  | "Array#[]=" =>
    match recv, arrPayload? h recv, args with
    | .ref o, some xs, [.int i, v] =>
      if (h.get o).frozen then frozenErr m recv "Array"
      else
        let idx := if i < 0 then i + xs.size else i
        if idx < 0 then
          .err Boot.indexErrorId
            s!"index {i} too small for array; minimum: -{xs.size}" m
        else
          let xs := if idx.toNat ≥ xs.size
            then (xs ++ Array.replicate (idx.toNat - xs.size + 1) Value.nil).set! idx.toNat v
            else xs.set! idx.toNat v
          .ok v { m with heap := h.set o { h.get o with payload := .arr xs } }
    | _, some _, _ => .unsupported "Array#[]= non-int index"
    | _, _, _ => .unsupported "[]="
  | "Array#<<" | "Array#push" =>
    match recv, arrPayload? h recv with
    | .ref o, some xs =>
      if (h.get o).frozen then frozenErr m recv "Array"
      else
        match bid, args with
        | "Array#<<", [v] =>
          .ok recv { m with heap := h.set o { h.get o with payload := .arr (xs.push v) } }
        | "Array#push", _ =>
          .ok recv { m with heap := h.set o { h.get o with payload := .arr (xs ++ args.toArray) } }
        | _, _ => .unsupported "<</arity"
    | _, _ => .unsupported "<<"
  | "Array#pop" =>
    match recv, arrPayload? h recv, args with
    | .ref o, some xs, [] =>
      if (h.get o).frozen then frozenErr m recv "Array"
      else if xs.isEmpty then .ok .nil m
      else .ok xs.back! { m with heap := h.set o { h.get o with payload := .arr xs.pop } }
    | _, _, _ => .unsupported "pop with arg"
  | "Array#shift" =>
    match recv, arrPayload? h recv, args with
    | .ref o, some xs, [] =>
      if (h.get o).frozen then frozenErr m recv "Array"
      else if xs.isEmpty then .ok .nil m
      else .ok xs[0]! { m with heap := h.set o { h.get o with payload := .arr (xs.extract 1 xs.size) } }
    | _, _, _ => .unsupported "shift with arg"
  | "Array#unshift" =>
    match recv, arrPayload? h recv with
    | .ref o, some xs =>
      if (h.get o).frozen then frozenErr m recv "Array"
      else .ok recv { m with heap := h.set o { h.get o with payload := .arr (args.toArray ++ xs) } }
    | _, _ => .unsupported "unshift"
  | "Array#length" | "Array#size" =>
    match arrPayload? h recv with
    | some xs => .ok (.int xs.size) m
    | none => .unsupported "length"
  | "Array#first" =>
    match arrPayload? h recv, args with
    | some xs, [] => .ok (xs[0]?.getD .nil) m
    | _, _ => .unsupported "first(n)"
  | "Array#last" =>
    match arrPayload? h recv, args with
    | some xs, [] => .ok (xs.back?.getD .nil) m
    | _, _ => .unsupported "last(n)"
  | "Array#empty?" =>
    match arrPayload? h recv with
    | some xs => .ok (.bool xs.isEmpty) m
    | none => .unsupported "empty?"
  | "Array#include?" =>
    binArg m args fun b =>
      match arrPayload? h recv with
      | some xs =>
        if hasUserEq h b || xs.any (hasUserEq h) then
          .unsupported "Array#include? with a user-defined =="
        else .ok (.bool (xs.any (valueEq h · b))) m
      | none => .unsupported "include?"
  | "Array#index" =>
    binArg m args fun b =>
      match arrPayload? h recv with
      | some xs =>
        if hasUserEq h b || xs.any (hasUserEq h) then
          .unsupported "Array#index with a user-defined =="
        else match xs.toList.findIdx? (valueEq h · b) with
        | some i => .ok (.int i) m
        | none => .ok .nil m
      | none => .unsupported "index"
  | "Array#+" =>
    binArg m args fun b =>
      match arrPayload? h recv, arrPayload? h b with
      | some xs, some ys => let (v, m) := allocArr m (xs ++ ys); .ok v m
      | some _, none => .err Boot.typeErrorId
          s!"no implicit conversion of {coerceName h b} into Array" m
      | _, _ => .unsupported "+"
  | "Array#-" =>
    binArg m args fun b =>
      match arrPayload? h recv, arrPayload? h b with
      | some xs, some ys =>
        let (v, m) := allocArr m (xs.filter (fun x => !(ys.any (valueEql h x ·))))
        .ok v m
      | _, _ => .unsupported "-"
  -- Set intersection/union. Both **deduplicate** and keep the receiver's order
  -- [V]: `[1,2,2,3] & [2,3,4]` is `[2,3]`, `[1,2,2,3] | [3,4,4]` is `[1,2,3,4]`.
  -- Element identity is `eql?` (`valueEql`), matching `Array#-` above.
  | "Array#&" =>
    binArg m args fun b =>
      match arrPayload? h recv, arrPayload? h b with
      | some xs, some ys =>
        let keep := xs.foldl (fun acc x =>
          if ys.any (valueEql h x ·) && !(acc.any (valueEql h x ·)) then acc.push x else acc) #[]
        let (v, m) := allocArr m keep
        .ok v m
      | _, _ => .unsupported "&"
  | "Array#|" =>
    binArg m args fun b =>
      match arrPayload? h recv, arrPayload? h b with
      | some xs, some ys =>
        let dedup := fun (acc : Array Value) (x : Value) =>
          if acc.any (valueEql h x ·) then acc else acc.push x
        let (v, m) := allocArr m (ys.foldl dedup (xs.foldl dedup #[]))
        .ok v m
      | _, _ => .unsupported "|"
  | "Array#*" =>
    binArg m args fun b =>
      match arrPayload? h recv, b with
      | some xs, .int n =>
        if n < 0 then .err Boot.argumentErrorId "negative argument" m
        else
          let (v, m) := allocArr m ((List.replicate n.toNat xs).foldl (· ++ ·) #[])
          .ok v m
      | some _, _ => .unsupported "Array#* join form"
      | _, _ => .unsupported "*"
  | "Array#concat" =>
    match recv, arrPayload? h recv, args with
    | .ref o, some xs, [b] =>
      match arrPayload? h b with
      | some ys =>
        if (h.get o).frozen then frozenErr m recv "Array"
        else .ok recv { m with heap := h.set o { h.get o with payload := .arr (xs ++ ys) } }
      | none => .err Boot.typeErrorId
          s!"no implicit conversion of {coerceName h b} into Array" m
    | _, _, _ => .unsupported "concat"
  | "Array#inspect" | "Array#to_s" =>
    match inspectP m recv with
    | .ok s => okStr m s
    | .error e => .unsupported e
  | "Array#to_a" => .ok recv m
  | "Array#reverse" =>
    match arrPayload? h recv with
    | some xs => let (v, m) := allocArr m xs.reverse; .ok v m
    | none => .unsupported "reverse"
  | "Array#join" => joinImpl m recv args
  | "Array#flatten" =>
    match arrPayload? h recv, args with
    | some _, [] =>
      match flattenAll m recv 100 with
      | some vs => let (v, m) := allocArr m vs.toArray; .ok v m
      | none => .unsupported "flatten depth"
    | _, _ => .unsupported "flatten(n)"
  | "Array#compact" =>
    match arrPayload? h recv with
    | some xs =>
      let (v, m) := allocArr m (xs.filter (fun x => match x with | .nil => false | _ => true))
      .ok v m
    | none => .unsupported "compact"
  | "Array#uniq" =>
    match arrPayload? h recv, args with
    | some xs, [] =>
      let ys := xs.foldl (init := #[]) fun acc x =>
        if acc.any (valueEql h x ·) then acc else acc.push x
      let (v, m) := allocArr m ys
      .ok v m
    | _, _ => .unsupported "uniq"
  | "Array#frozen?" =>
    match recv with
    | .ref o => .ok (.bool (h.get o).frozen) m
    | _ => .unsupported "frozen?"
  | "Array#sort" => sortImpl m recv
  | "Array#min" | "Array#max" =>
    match arrPayload? h recv, args with
    | some xs, [] =>
      if xs.isEmpty then .ok .nil m
      else
        match sortKey? h xs with
        | some keyed =>
          let sorted := keyed.toList.mergeSort (fun a b => leKey a.1 b.1)
          .ok (if bid == "Array#min" then sorted.head!.2 else sorted.getLast!.2) m
        | none => .unsupported "min/max needs <=> dispatch"
    | _, _ => .unsupported "min/max with arg"
  | "Array#sum" =>
    match arrPayload? h recv, args with
    | some xs, [] =>
      let step := fun (acc : Option Num) (x : Value) =>
        match acc, num? x with
        | some (.i a), some (.i b) => some (Num.i (a + b))
        | some (.i a), some (.f b) => some (Num.f (Float.ofInt a + b))
        | some (.f a), some (.i b) => some (Num.f (a + Float.ofInt b))
        | some (.f a), some (.f b) => some (Num.f (a + b))
        | _, _ => none
      match xs.foldl step (some (Num.i 0)) with
      | some n => .ok n.value m
      | none => .unsupported "sum of non-numerics"
    | _, _ => .unsupported "sum with arg"
  /- ─── Hash ─── -/
  | "Hash#==" =>
    binArg m args fun b =>
      match recv, b with
      | .ref _, .ref _ => .ok (.bool (valueEq h recv b)) m
      | _, _ => .ok (.bool false) m
  | "Hash#[]" =>
    binArg m args fun b =>
      match recv with
      | .ref o =>
        match (h.get o).payload with
        | .hsh xs =>
          match xs.find? (fun (k, _) => valueEql h k b) with
          | some (_, v) => .ok v m
          | none =>
            -- Miss: consult the hash's default. A static `val` is returned as-is;
            -- a `prc` default_proc must call a closure (push a frame), which a pure
            -- builtin cannot do — it is intercepted in `invoke` (L42), so reaching
            -- it here means the interception missed → gate rather than answer wrong.
            match (h.get o).hashDflt with
            | some (.val d) => .ok d m
            | some (.prc _) => .unsupported "Hash#[] default_proc"
            | none => .ok .nil m
        | _ => .unsupported "[]"
      | _ => .unsupported "[]"
  | "Hash#[]=" =>
    match recv, args with
    | .ref o, [k, v] =>
      match (h.get o).payload with
      | .hsh xs =>
        if (h.get o).frozen then frozenErr m recv "Hash"
        else
          let xs := match xs.toList.findIdx? (fun (k', _) => valueEql h k' k) with
            | some i => xs.set! i (xs[i]!.1, v)
            | none => xs.push (k, v)
          .ok v { m with heap := h.set o { h.get o with payload := .hsh xs } }
      | _ => .unsupported "[]="
    -- Arity is checked before the receiver's payload (CRuby's `[]=` is a C
    -- function of arity 2, so the check precedes any element handling). Dispatch
    -- has already resolved `Hash#[]=`, so the receiver is a Hash: a wrong arity
    -- is an `ArgumentError`, not an unmodeled case. This matters beyond fidelity
    -- — ArgumentError is in `typeErrorFamily`, so gating here made a *reachable
    -- type-stuck outcome* invisible to the checker (druby-reproduction-plan.md
    -- §4; the hashslice call site `h['a','b'] = 3, 4` is exactly this shape).
    | _, _ => .err Boot.argumentErrorId
        s!"wrong number of arguments (given {args.length}, expected 2)" m
  | "Hash#length" | "Hash#size" =>
    match hshPayload? h recv with
    | some xs => .ok (.int xs.size) m
    | none => .unsupported "size"
  | "Hash#empty?" =>
    match hshPayload? h recv with
    | some xs => .ok (.bool xs.isEmpty) m
    | none => .unsupported "empty?"
  | "Hash#key?" | "Hash#has_key?" | "Hash#include?" | "Hash#member?" =>
    binArg m args fun b =>
      match hshPayload? h recv with
      | some xs => .ok (.bool (xs.any (fun (k, _) => valueEql h k b))) m
      | none => .unsupported "key?"
  | "Hash#keys" =>
    match hshPayload? h recv with
    | some xs => let (v, m) := allocArr m (xs.map (·.1)); .ok v m
    | none => .unsupported "keys"
  | "Hash#values" =>
    match hshPayload? h recv with
    | some xs => let (v, m) := allocArr m (xs.map (·.2)); .ok v m
    | none => .unsupported "values"
  | "Hash#delete" =>
    match recv, args with
    | .ref o, [k] =>
      match (h.get o).payload with
      | .hsh xs =>
        if (h.get o).frozen then frozenErr m recv "Hash"
        else
          match xs.find? (fun (k', _) => valueEql h k' k) with
          | some (_, v) =>
            let xs := xs.filter (fun (k', _) => !(valueEql h k' k))
            .ok v { m with heap := h.set o { h.get o with payload := .hsh xs } }
          | none => .ok .nil m
      | _ => .unsupported "delete"
    | _, _ => .unsupported "delete/arity"
  | "Hash#fetch" =>
    match hshPayload? h recv, args with
    | some xs, [k] =>
      match xs.find? (fun (k', _) => valueEql h k' k) with
      | some (_, v) => .ok v m
      | none =>
        match inspectP m k with
        | .ok ki => .err Boot.keyErrorId s!"key not found: {ki}" m
        | .error e => .unsupported e
    | some xs, [k, dflt] =>
      match xs.find? (fun (k', _) => valueEql h k' k) with
      | some (_, v) => .ok v m
      | none => .ok dflt m
    | _, _ => .unsupported "fetch"
  | "Hash#inspect" | "Hash#to_s" =>
    match inspectP m recv with
    | .ok s => okStr m s
    | .error e => .unsupported e
  | "Hash#merge" =>
    -- Non-mutating merge: start from self's entries, fold each Hash arg in with
    -- later keys overriding — an existing key keeps its position but takes the
    -- new value, a new key is appended (CRuby's order semantics, mirroring the
    -- `Hash#[]=` update-or-append above). The conflict-resolution *block* form is
    -- not modeled (a pure builtin sees no block; cf. `Hash#fetch`), and a non-Hash
    -- argument gates rather than risk a wrong `TypeError` message.
    match hshPayload? h recv with
    | none => .unsupported "merge"
    | some base =>
      if args.all (fun a => (hshPayload? h a).isSome) then
        let acc := args.foldl (init := base) fun cur a =>
          match hshPayload? h a with
          | none => cur                       -- unreachable given the `all` guard
          | some other =>
            other.foldl (init := cur) fun cur (k, v) =>
              match cur.toList.findIdx? (fun (k', _) => valueEql h k' k) with
              | some i => cur.set! i (k, v)
              | none => cur.push (k, v)
        let (v, m) := allocHsh m acc; .ok v m
      else .unsupported "merge: non-Hash arg"
  | _ => runModules bid recv args m

end Builtins

end RubyCore
