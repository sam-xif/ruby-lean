class C
  def initialize
    @a = 1
  end
  def leak
    x = self
    @a = "s"
    x
  end
end
C.new.leak
