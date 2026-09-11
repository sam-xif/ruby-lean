# typed: true
module Twice
  def self.apply(f, v)
    f.call(f.call(v))
  end
end


Twice.apply(lambda { |x| x + 1 }, 5)
