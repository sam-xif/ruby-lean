# typed: true
require "sorbet-runtime"
extend T::Sig

# No sig, so Sorbet sees the returned proc as T.untyped.
def untyped_block
  proc { "not an integer" }
end

sig { params(blk: T.proc.returns(Integer)).returns(Integer) }
def apply_block(&blk)
  # sorbet-runtime validates that `blk` is a Proc. It never checks what the
  # block RETURNS, so the declared `T.proc.returns(Integer)` has no runtime
  # backstop and the error lands inside this typed body.
  blk.call + 1
end

puts apply_block(&untyped_block)
