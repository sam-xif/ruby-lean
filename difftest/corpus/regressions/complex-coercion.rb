# L279: effectful coerce, including Complex division's quo dispatch.
class Answer
  def +(other); :plus; end
  def -(other); :minus; end
  def *(other); :times; end
  def /(other); :divide; end
  def quo(other); :quotient; end
end
class Operand
  def coerce(other)
    p [:coerce, other]
    [Answer.new, self]
  end
  def ==(other)
    p [:equal, other]
    :truthy
  end
end
a = 1.2ri
b = Operand.new
p [a + b, a - b, a * b, a / b, a.quo(b), a == b]
p [a.coerce(2), a.coerce(1.5), a.coerce(1.2r), a.coerce(2i)]
class Complex
  def ==(other)
    p :complex_equal
    :truthy
  end
end
p [1i.eql?(2i), 1i.eql?(1.0i)]
c = 1i
p c.eql?(c)
