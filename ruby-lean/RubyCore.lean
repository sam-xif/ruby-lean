import RubyCore.Syntax
import RubyCore.Heap
import RubyCore.Machine
import RubyCore.Repr
import RubyCore.Builtins
import RubyCore.Interp
import RubyCore.Boot
import RubyCore.Obs
import RubyCore.Trace
import RubyCore.Sorbet.Fragment
import RubyCore.Sorbet.SigRead

/-!
# RubyCore — an executable semantics for Ruby

Read in this order:

* `Syntax`    the core language every Ruby program is desugared into
* `Heap`      values, objects, classes, and method and constant lookup
* `Machine`   the machine configuration: control, continuations, frames
* `Repr`      `inspect`, `to_s`, `==` and `eql?`
* `Builtins`  the methods implemented natively, such as `Integer#+`
* `Interp`    `stepFn`, one transition of the machine, and `run`
* `Boot`      running the Ruby-written prelude to produce the initial heap
* `Obs`       what a finished run is observed as: output, result, exception

`Numeric/` and `Regex/` are libraries the builtins use, `Generated/` holds
tables produced by scripts, `Trace` prints a run step by step, and `Sorbet/`
reads `sig` declarations out of a program without running it.
-/
