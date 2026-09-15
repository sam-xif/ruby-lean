# typed: true
class E < StandardError
  extend T::Sig
  sig { returns(Integer) }
  def message
    5
  end
end
begin
  raise E
rescue StandardError => e
  e.message + "s"
end
