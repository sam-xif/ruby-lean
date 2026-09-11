class C
  def initialize
    @a = 1
  end
  def get
    @a
  end
end
o = C.new
xs = [o, o.instance_variable_set(:@a, "s")]
xs[0].get + 1
