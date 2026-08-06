# typed: true
require "sorbet-runtime"

# No sig, so Sorbet sees this as returning T.untyped.
def untyped_array
  [1, 2]
end

class Holder
  extend T::Sig

  sig { params(xs: T::Array[Integer]).void }
  def store(xs)
    # The wrapper checks `xs.is_a?(Array)` and nothing more. Note that even a
    # DEEP check here would pass: the array conforms at this instant.
    @xs = xs
  end

  sig { returns(Integer) }
  def total
    T.must(@xs).sum
  end
end

a = untyped_array
h = Holder.new
h.store(a)
a << "boom"          # mutated AFTERWARDS, through the alias
puts h.total
