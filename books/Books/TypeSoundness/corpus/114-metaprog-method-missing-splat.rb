# typed: true
class Ghost
  extend T::Sig
  sig { params(name: Symbol, args: T.untyped).returns(String) }
  def method_missing(name, *args)
    "called"
  end
end

Ghost.new.anything_at_all
