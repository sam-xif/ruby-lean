# typed: true
class Ghost
  extend T::Sig
  sig { params(name: Symbol).returns(String) }
  def method_missing(name)
    "called " + name.to_s
  end
end

Ghost.new.anything_at_all
