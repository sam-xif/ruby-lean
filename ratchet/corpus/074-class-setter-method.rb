# typed: true
class Box
  extend T::Sig
  sig { params(size: Integer).void }
  def initialize(size)
    @size = size
  end

  sig { returns(Integer) }
  def grow
    @size = @size + 1
  end
end

Box.new(1).grow
