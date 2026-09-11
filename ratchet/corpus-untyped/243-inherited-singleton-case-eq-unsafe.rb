class A
  def self.===(o)
    "s"
  end
end
class B < A
end
(B === 5) & true
