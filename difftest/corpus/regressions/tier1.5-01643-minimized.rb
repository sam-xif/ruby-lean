def __t(l, v)
  puts(l)
  v
end
class C0
  define_method(:dm0) do
    (a = __t("1", 0))
    __t("2", 0)
  end
  define_singleton_method(:ds0) do |x, y|
    (a = __t("3", x))
    __t("4", 0)
  end
  def method_missing(name, *args)
    "mm-#{__t("0", name)}"
  end
end
class C1
end
class C2
end
(a = C0.new())
*a, b = (__t("5", a)), (__t("6", a))
(a += C0.new())
puts(__t("7", 0))
