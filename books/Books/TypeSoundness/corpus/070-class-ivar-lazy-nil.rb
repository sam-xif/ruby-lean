# typed: true
class Box
  extend T::Sig
  sig { returns(NilClass) }
  def reveal
    @secret
  end
end

Box.new.reveal
