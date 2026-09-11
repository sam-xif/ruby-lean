# typed: true
class Point
  extend T::Sig
  sig { params(x: Integer).void }
  def initialize(x)
    @x = x
  end
end

{"origin" => Point.new(0)}
