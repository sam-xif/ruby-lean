class C
  def whoami
    self.class
  end
  def tag
    1
  end
end
class D < C
  def tag
    "s"
  end
end
D.new.whoami.new.tag + 1
