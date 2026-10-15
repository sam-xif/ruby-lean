# typed: true
class Box
  extend T::Sig
  sig { returns(Integer) }
  def size
    3
  end
  alias length size
end

Box.new.length
