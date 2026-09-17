# super: bare `super` (zsuper, forwards the enclosing method's args) vs explicit
# `super(...)`. These are DISTINCT and must render back to distinct forms.
class Base
  def compute(a, b)
    a + b
  end
end

class Doubler < Base
  # zsuper: forwards (a, b) unchanged, then post-processes.
  def compute(a, b)
    super * 2
  end
end

class Shifter < Base
  # explicit super with rewritten args.
  def compute(a, b)
    super(a + 10, b)
  end
end

class Zeroer < Base
  # super() with an explicit empty arg list is NOT the same as bare super.
  def compute(_a, _b)
    super(0, 0)
  end
end

print(Doubler.new.compute(3, 4)); print(";")   # (3+4)*2 = 14
print(Shifter.new.compute(3, 4)); print(";")   # (13)+(4) = 17
print(Zeroer.new.compute(3, 4))                # 0
