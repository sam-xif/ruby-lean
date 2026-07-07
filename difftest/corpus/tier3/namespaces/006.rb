NAME = "global const"
class W
  def NAME; "method"; end
  def test
    NAME
  end
  def test2
    NAME()
  end
end
puts W.new.test
puts W.new.test2
puts defined?(NAME)
puts W.new.NAME
W.new.test
