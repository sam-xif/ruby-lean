# typed: strict
require "sorbet-runtime"
extend T::Sig

class Suit < T::Enum
  enums do
    Spades = new
    Hearts = new
  end
end

sig { params(s: Suit).returns(String) }
def suit_name(s)
  case s
  when Suit::Spades then "spades"
  when Suit::Hearts then "hearts"
  else T.absurd(s)
  end
end

puts suit_name(Suit::Spades)
puts suit_name(Suit::Hearts)
