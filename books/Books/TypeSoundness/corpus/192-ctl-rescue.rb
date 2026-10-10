# typed: true
extend T::Sig
sig { params(s: String).returns(Integer) }
def parse(s)
  raise ArgumentError, "bad" if s.empty?
  s.length
rescue ArgumentError => e
  e.message.length
end

parse("") + parse("ab")
