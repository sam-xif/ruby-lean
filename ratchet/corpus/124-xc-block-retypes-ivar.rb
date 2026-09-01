class C
  def initialize(x)
    @x = x
  end

  def run
    yield
  end

  def go
    run { @x = "s" }
    @x + 1
  end
end


C.new(1).go
