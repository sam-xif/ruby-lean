class C
  def initialize
    @a = 1
  end
  def get
    @a
  end
  def leak
    x = self
    @a = "s"
    x.get + 1
  end
end
C.new.leak
