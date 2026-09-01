class Box
  def initialize(size)
    @size = size
  end

  def grow
    @size = @size + 1
  end
end

Box.new(1).grow
