class Box
  def initialize(f)
    @f = f
  end

  def apply(v)
    @f.call(v)
  end
end


Box.new(lambda { |x| x * 2 }).apply(4)
