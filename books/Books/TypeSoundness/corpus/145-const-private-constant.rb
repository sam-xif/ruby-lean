# typed: true
class Box
  SECRET = 1
  private_constant :SECRET

  def get
    SECRET
  end
end

Box.new.get
