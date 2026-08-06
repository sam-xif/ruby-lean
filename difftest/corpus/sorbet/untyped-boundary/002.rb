# typed: true
require "sorbet-runtime"
extend T::Sig

# No sig, so Sorbet gives this method the return type T.untyped (§A.5).
def untyped_source
  "not an integer"
end

sig { returns(Integer) }
def typed_consumer
  # An untyped value crosses INTO typed code. There is no wrapper on
  # `untyped_source` (it has no sig), and assigning T.untyped to anything is
  # permitted, so nothing checks this crossing in either direction.
  v = untyped_source
  # The error is raised HERE — inside the body of a sig'd method.
  v + 1
end

puts typed_consumer
