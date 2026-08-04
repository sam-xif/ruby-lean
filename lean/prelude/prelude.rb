# frozen_string_literal: true

# The **prelude**: the part of Ruby's core library modeled in RubyCore itself
# rather than as Lean primitives (L62). Loaded from H₀ before the program under
# test; `scripts/gen_prelude.rb` desugars this file into `RubyCore/Prelude.lean`.
#
# Rules for authoring (the ratchet depends on them):
#
# 1. **Stay inside the desugar fragment and the Lean fragment.** Generation fails
#    loudly on the former; the latter shows up as gates at *call* time. `while`,
#    `if`, `yield`, `block_given?`, `def`, `alias`, arithmetic, `Array#[]`/`[]=`/
#    `push`/`length`, `Hash#[]`/`[]=` are all safe.
# 2. **Declare, never guess.** A form this code cannot model faithfully calls
#    `__unsupported__("reason")`, the builtin that returns the engine's
#    Unsupported gate — the RubyCore-level equivalent of `.unsupported` in Lean.
#    Blockless Enumerable calls (which CRuby answers with an `Enumerator`) are the
#    standard case.
# 3. **Never define a repr-sensitive method** (`to_s`, `inspect`, `==`, `eql?`,
#    `message`, `to_str`): defining one flips `reprPure` off globally (L7) and
#    every `puts`/`inspect` in every program would then gate.
# 4. **A prelude method is the model of the CRuby builtin of that name** — it
#    suppresses the shadow gate for its own name (L62), so fidelity is on this
#    file. Match CRuby exactly, including the empty-receiver and tie cases.

module Comparable
  def <(other)
    c = (self <=> other)
    return __unsupported__("Comparable#< with a nil <=>") if c.nil?
    c < 0
  end

  def <=(other)
    c = (self <=> other)
    return __unsupported__("Comparable#<= with a nil <=>") if c.nil?
    c <= 0
  end

  def >(other)
    c = (self <=> other)
    return __unsupported__("Comparable#> with a nil <=>") if c.nil?
    c > 0
  end

  def >=(other)
    c = (self <=> other)
    return __unsupported__("Comparable#>= with a nil <=>") if c.nil?
    c >= 0
  end

  def between?(min, max)
    if self < min
      false
    else
      !(self > max)
    end
  end

  def clamp(min, max)
    if self < min
      min
    elsif self > max
      max
    else
      self
    end
  end
end
