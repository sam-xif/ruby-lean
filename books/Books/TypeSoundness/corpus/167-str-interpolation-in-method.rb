# typed: true
class Box
  extend T::Sig
  sig { params(v: Integer).void }
  def initialize(v)
    @v = v
  end

  sig { returns(String) }
  def to_s
    "Box(#{@v})"
  end
end

"#{Box.new(2)}"
