module M0
  def mm0
    (a = 0)
    0
  end
end
class C0
end
class C1
  def im0
    (a = 0)
    0
  end
  def method_missing(name, *args)
    "mm-#{name}"
  end
end
(a = 0)
puts("v=#{C1.new()}")
