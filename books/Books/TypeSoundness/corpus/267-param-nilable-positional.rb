# typed: true
class Shelf
  extend T::Sig

  sig { params(label: T.nilable(String)).void }
  def initialize(label)
    @count = 0
  end

  sig { params(code: T.nilable(String)).returns(Integer) }
  def price(code)
    code.nil? ? 10 : 5
  end

  sig { params(n: T.nilable(Integer)).returns(Integer) }
  def self.tax(n)
    n.nil? ? 0 : n
  end
end

extend T::Sig
sig { params(n: T.nilable(Integer)).returns(Integer) }
def bump(n)
  n.nil? ? 0 : n + 1
end

s = Shelf.new(nil)
Shelf.new("top")
s.price("OFF") + s.price(nil) + Shelf.tax(2) + Shelf.tax(nil) + bump(1) + bump(nil)
