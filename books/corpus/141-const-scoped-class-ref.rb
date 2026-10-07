# typed: true
module M
  class Box
    extend T::Sig
    sig { params(v: Integer).void }
    def initialize(v)
      @v = v
    end

    sig { returns(Integer) }
    def get
      @v
    end
  end
end

M::Box.new(7).get
