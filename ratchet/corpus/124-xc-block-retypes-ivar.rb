# typed: true
class C
  extend T::Sig
  sig { params(x: Integer).void }
  def initialize(x)
    @x = x
  end

  sig { returns(T.untyped) }
  def run
    yield
  end

  sig { returns(Integer) }
  def go
    run { @x = "s" }
    @x + 1
  end
end


C.new(1).go
