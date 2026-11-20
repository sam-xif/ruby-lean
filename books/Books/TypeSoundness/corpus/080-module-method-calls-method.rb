# typed: true
module M
  def self.value
    21
  end

  def self.describe
    value * 2
  end
end

M.describe
