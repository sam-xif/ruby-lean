# typed: true
class Holder
  def initialize(flag)
    if flag
      @v = 1
    else
      @v = "s"
    end
  end

  def describe
    if @v.is_a?(Integer)
      @v + 1
    else
      @v + "!"
    end
  end
end


Holder.new(true).describe
