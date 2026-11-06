# The prelude

The part of Ruby's core library that the model implements in Ruby rather than as
Lean primitives. Core boot evaluates these files before the program under test;
`ruby-lean/scripts/gen_prelude.rb` concatenates them in the order below, desugars
the result, and writes `RubyCore/Generated/PreludeJson.lean`. `make gen` then
turns that into the Lean terms the model boots from.

Pathname stays in core, not `features/`: the pinned CRuby 4.0.5 boots
`pathname.so` itself.

## Layout

| File | Contents |
|---|---|
| `core/object.rb` | `BasicObject` and the `Kernel`/`Object` methods |
| `core/comparable.rb` | `Comparable` |
| `core/enumerable.rb` | `Enumerable` and its iterator protocol |
| `core/range.rb` | `Range` |
| `core/integer.rb` | `Integer` |
| `core/hash.rb` | `Hash` |
| `core/kernel_conversions.rb` | `to_s`, `to_i`, `Array()`, `String()` and the other `Kernel` conversions |
| `core/repr.rb` | The dispatching `inspect`/`to_s` twins for classes whose repr is user-defined |
| `core/conversions.rb` | The conversion protocols (`to_str`, `to_ary`, `to_int`), the implicit array conversion and `coerce` |
| `core/pathname.rb` | The pure half of `Pathname` |
| `core/file.rb` | `File` path helpers (no I/O; the symbolic filesystem is in `RubyCore/Builtins/FS.lean`) |
| `core/encoding.rb` | `Encoding` |
| `core/struct.rb` | `Struct` |
| `features/*.rb` | Optional libraries that execute on `require`: `json`, `uri`, `forwardable`, `pathname` and a model of `sorbet-runtime` |

The order in `gen_prelude.rb`'s `CORE` list is the load order and is part of the
model: a later file may reopen a class or use a constant an earlier one defined.
When you add a file, add it to that list and to `PRELUDE_SRC` in the `Makefile`.

## Rules for authoring

These are the constraints the ratchet depends on.

1. **Stay inside the desugar fragment and the Lean fragment.** Generation fails
   loudly on the former; the latter shows up as gates at *call* time. `while`,
   `if`, `yield`, `block_given?`, `def`, `alias`, arithmetic, `Array#[]`/`[]=`/
   `push`/`length`, `Hash#[]`/`[]=` are all safe.
2. **Declare, never guess.** A form this code cannot model faithfully calls
   `__unsupported__("reason")`, the builtin that returns the engine's
   Unsupported gate — the RubyCore-level equivalent of `.unsupported` in Lean.
   Blockless methods not yet connected to the native Enumerator descriptor
   remain explicit gates.
3. **Repr-sensitive methods** (`to_s`, `inspect`, `==`, `eql?`, `message`,
   `to_str`) require dispatch at their consumers. Purity is per-class,
   impure builtin receivers dispatch prelude twins, and frozen errors
   and final observations dispatch too. When adding an override, test
   ordinary I/O, nested container repr, errors and the final observation;
   other pure consumers must still defer or gate when they cannot dispatch.
4. **A prelude method is the model of the CRuby builtin of that name** — it
   suppresses the shadow gate for its own name, so fidelity is on this
   file. Match CRuby exactly, including the empty-receiver and tie cases.
5. Optional feature bodies are smaller behavioral models of the upstream
   source. User definition hooks during require gate unless declaration order
   and callback behavior match upstream (Forwardable). Keep library origin
   separate from boot-only preludeMode; the latter must never silently suppress
   runtime user callbacks.

## Adding a method

1. Put it in the file for the class or protocol it belongs to. Define it close
   to the other methods of that class, not at the end of the file.
2. If it belongs to a class that has no file yet, add `core/<topic>.rb` in the
   position the load order needs, then add it to `CORE` and `PRELUDE_SRC`.
3. If it is a whole optional library, add `features/<name>.rb`; features load on
   `require` and are not part of core boot.
4. Run `make gen`, then `make conformance` (and `make books` if the model or the
   generated prelude changed). `make gen-check` must report every generated file
   fresh.
