# typed: true
class Shelf
  extend T::Sig
  sig { params(items: T::Array[Integer]).void }
  def initialize(items)
    @items = items
  end

  sig { returns(T::Array[String]) }
  def names
    @items.map { |i| i.to_s }
  end
end


Shelf.new([1, 2]).names
