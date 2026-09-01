class Box
  def initialize(v)
    @v = v
  end

  def to_s
    "Box(#{@v})"
  end
end

"#{Box.new(2)}"
