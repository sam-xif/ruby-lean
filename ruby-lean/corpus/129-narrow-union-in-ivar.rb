# typed: true
class Holder
  extend T::Sig
  sig { params(flag: T::Boolean).void }
  def initialize(flag)
    if flag
      @v = 1
    else
      @v = "s"
    end
  end

  sig { returns(T.any(Integer, String)) }
  def describe
    if @v.is_a?(Integer)
      @v + 1
    else
      @v + "!"
    end
  end
end


Holder.new(true).describe
