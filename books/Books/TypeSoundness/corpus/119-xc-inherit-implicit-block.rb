# typed: true
class Base
  extend T::Sig
  sig { returns(String) }
  def wrap
    "[" + yield.to_s + "]"
  end
end

class Child < Base
  extend T::Sig
  sig { returns(String) }
  def show
    wrap { 7 }
  end
end


Child.new.show
