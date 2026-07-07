class A
  def init(a = 10)
    "A:#{a}"
  end
end
class B < A
  def init(a)
    "B[#{super()}|#{super}]"
  end
end
puts B.new.init(5)
