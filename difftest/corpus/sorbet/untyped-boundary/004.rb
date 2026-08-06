# typed: true
require "sorbet-runtime"

class Counter
  extend T::Sig

  sig { void }
  def initialize
    @n = T.let(0, Integer)
  end

  # No sig, so nothing checks what this stores into @n. The crossing is not a
  # call into typed code at all -- it is a write to shared state that typed
  # code later reads, so no call-graph condition can see it.
  def untyped_write(v)
    @n = v
  end

  sig { returns(Integer) }
  def bump
    @n + 1
  end
end

c = Counter.new
c.untyped_write("boom")
puts c.bump
