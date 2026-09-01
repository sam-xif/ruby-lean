class Box
  def size
    3
  end
  alias length size
end

Box.new.length
