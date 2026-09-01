class Shelf
  def initialize(items)
    @items = items
  end

  def names
    @items.map { |i| i.to_s }
  end
end


Shelf.new([1, 2]).names
