# typed: true
class Rect
  extend T::Sig
  sig { params(w: Integer, h: Integer).void }
  def initialize(w, h)
    @w = w
    @h = h
  end

  sig { returns(Integer) }
  def area
    @w * @h
  end

  sig { returns(String) }
  def describe
    "area=" + area.to_s
  end
end

Rect.new(3, 4).describe
