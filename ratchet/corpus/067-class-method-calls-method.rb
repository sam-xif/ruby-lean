class Rect
  def initialize(w, h)
    @w = w
    @h = h
  end

  def area
    @w * @h
  end

  def describe
    "area=" + area.to_s
  end
end

Rect.new(3, 4).describe
