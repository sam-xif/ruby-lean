class Base
  def wrap
    "[" + yield.to_s + "]"
  end
end

class Child < Base
  def show
    wrap { 7 }
  end
end


Child.new.show
