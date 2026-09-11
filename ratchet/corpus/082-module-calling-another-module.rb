# typed: true
module M2
  def self.bar
    10
  end
end

module M1
  def self.foo
    M2.bar + 1
  end
end

M1.foo
