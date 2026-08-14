def __t(l, v)
  puts(l)
  v
end
module M0
  def mm0
    (a = __t("0", 0))
    __t("1", 0)
  end
end
module M1
  def mm0
    (a = __t("2", 0))
    __t("3", 0)
  end
end
class C0
  include M0
  class << self
    def esm0
      (a = __t("6", 0))
      __t("7", 0)
    end
  end
  def im0
    (a = __t("4", 0))
    mm0()
  end
  def method_missing(name, *args)
    "mm-#{__t("5", name)}"
  end
end
class C1
end
class C2
  define_singleton_method(:ds0) do
    (a = __t("8", 0))
    __t("9", 0)
  end
end
(a = (__t("10", 0) + C0.new()))
puts(__t("11", 0))
